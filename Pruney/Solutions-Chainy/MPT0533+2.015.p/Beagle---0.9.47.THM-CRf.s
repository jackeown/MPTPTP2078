%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:19 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   44 (  86 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 256 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k8_relat_1(A_18,B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_20,C_22,B_21] :
      ( r1_tarski(k8_relat_1(A_20,C_22),k8_relat_1(B_21,C_22))
      | ~ r1_tarski(A_20,B_21)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_23,B_24,C_26] :
      ( r1_tarski(k8_relat_1(A_23,B_24),k8_relat_1(A_23,C_26))
      | ~ r1_tarski(B_24,C_26)
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [C_41,D_42,B_43,A_44] :
      ( r2_hidden(k4_tarski(C_41,D_42),B_43)
      | ~ r2_hidden(k4_tarski(C_41,D_42),A_44)
      | ~ r1_tarski(A_44,B_43)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [A_45,B_46,B_47] :
      ( r2_hidden(k4_tarski('#skF_1'(A_45,B_46),'#skF_2'(A_45,B_46)),B_47)
      | ~ r1_tarski(A_45,B_47)
      | r1_tarski(A_45,B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_34])).

tff(c_2,plain,(
    ! [C_16,D_17,B_11,A_1] :
      ( r2_hidden(k4_tarski(C_16,D_17),B_11)
      | ~ r2_hidden(k4_tarski(C_16,D_17),A_1)
      | ~ r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_48,B_49,B_50,B_51] :
      ( r2_hidden(k4_tarski('#skF_1'(A_48,B_49),'#skF_2'(A_48,B_49)),B_50)
      | ~ r1_tarski(B_51,B_50)
      | ~ v1_relat_1(B_51)
      | ~ r1_tarski(A_48,B_51)
      | r1_tarski(A_48,B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_139,plain,(
    ! [A_77,C_73,B_74,A_75,B_76] :
      ( r2_hidden(k4_tarski('#skF_1'(A_75,B_74),'#skF_2'(A_75,B_74)),k8_relat_1(A_77,C_73))
      | ~ v1_relat_1(k8_relat_1(A_77,B_76))
      | ~ r1_tarski(A_75,k8_relat_1(A_77,B_76))
      | r1_tarski(A_75,B_74)
      | ~ v1_relat_1(A_75)
      | ~ r1_tarski(B_76,C_73)
      | ~ v1_relat_1(C_73)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_265,plain,(
    ! [A_122,B_121,B_120,C_119,C_123] :
      ( r2_hidden(k4_tarski('#skF_1'(k8_relat_1(A_122,C_119),B_121),'#skF_2'(k8_relat_1(A_122,C_119),B_121)),k8_relat_1(B_120,C_123))
      | ~ v1_relat_1(k8_relat_1(B_120,C_119))
      | r1_tarski(k8_relat_1(A_122,C_119),B_121)
      | ~ v1_relat_1(k8_relat_1(A_122,C_119))
      | ~ r1_tarski(C_119,C_123)
      | ~ v1_relat_1(C_123)
      | ~ r1_tarski(A_122,B_120)
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_274,plain,(
    ! [B_124,C_125,A_126,C_127] :
      ( ~ v1_relat_1(k8_relat_1(B_124,C_125))
      | r1_tarski(k8_relat_1(A_126,C_125),k8_relat_1(B_124,C_127))
      | ~ v1_relat_1(k8_relat_1(A_126,C_125))
      | ~ r1_tarski(C_125,C_127)
      | ~ v1_relat_1(C_127)
      | ~ r1_tarski(A_126,B_124)
      | ~ v1_relat_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_265,c_4])).

tff(c_14,plain,(
    ~ r1_tarski(k8_relat_1('#skF_3','#skF_5'),k8_relat_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_291,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1(k8_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_274,c_14])).

tff(c_301,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1(k8_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_20,c_18,c_291])).

tff(c_302,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_305,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_302])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_305])).

tff(c_310,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_323,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_310])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.35  
% 2.76/1.37  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 2.76/1.37  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.76/1.37  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_relat_1)).
% 2.76/1.37  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 2.76/1.37  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 2.76/1.37  tff(c_22, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.37  tff(c_8, plain, (![A_18, B_19]: (v1_relat_1(k8_relat_1(A_18, B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.76/1.37  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.37  tff(c_20, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.37  tff(c_18, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.37  tff(c_10, plain, (![A_20, C_22, B_21]: (r1_tarski(k8_relat_1(A_20, C_22), k8_relat_1(B_21, C_22)) | ~r1_tarski(A_20, B_21) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.37  tff(c_12, plain, (![A_23, B_24, C_26]: (r1_tarski(k8_relat_1(A_23, B_24), k8_relat_1(A_23, C_26)) | ~r1_tarski(B_24, C_26) | ~v1_relat_1(C_26) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.37  tff(c_6, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.37  tff(c_34, plain, (![C_41, D_42, B_43, A_44]: (r2_hidden(k4_tarski(C_41, D_42), B_43) | ~r2_hidden(k4_tarski(C_41, D_42), A_44) | ~r1_tarski(A_44, B_43) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.37  tff(c_38, plain, (![A_45, B_46, B_47]: (r2_hidden(k4_tarski('#skF_1'(A_45, B_46), '#skF_2'(A_45, B_46)), B_47) | ~r1_tarski(A_45, B_47) | r1_tarski(A_45, B_46) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_6, c_34])).
% 2.76/1.37  tff(c_2, plain, (![C_16, D_17, B_11, A_1]: (r2_hidden(k4_tarski(C_16, D_17), B_11) | ~r2_hidden(k4_tarski(C_16, D_17), A_1) | ~r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.37  tff(c_47, plain, (![A_48, B_49, B_50, B_51]: (r2_hidden(k4_tarski('#skF_1'(A_48, B_49), '#skF_2'(A_48, B_49)), B_50) | ~r1_tarski(B_51, B_50) | ~v1_relat_1(B_51) | ~r1_tarski(A_48, B_51) | r1_tarski(A_48, B_49) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_38, c_2])).
% 2.76/1.37  tff(c_139, plain, (![A_77, C_73, B_74, A_75, B_76]: (r2_hidden(k4_tarski('#skF_1'(A_75, B_74), '#skF_2'(A_75, B_74)), k8_relat_1(A_77, C_73)) | ~v1_relat_1(k8_relat_1(A_77, B_76)) | ~r1_tarski(A_75, k8_relat_1(A_77, B_76)) | r1_tarski(A_75, B_74) | ~v1_relat_1(A_75) | ~r1_tarski(B_76, C_73) | ~v1_relat_1(C_73) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_12, c_47])).
% 2.76/1.37  tff(c_265, plain, (![A_122, B_121, B_120, C_119, C_123]: (r2_hidden(k4_tarski('#skF_1'(k8_relat_1(A_122, C_119), B_121), '#skF_2'(k8_relat_1(A_122, C_119), B_121)), k8_relat_1(B_120, C_123)) | ~v1_relat_1(k8_relat_1(B_120, C_119)) | r1_tarski(k8_relat_1(A_122, C_119), B_121) | ~v1_relat_1(k8_relat_1(A_122, C_119)) | ~r1_tarski(C_119, C_123) | ~v1_relat_1(C_123) | ~r1_tarski(A_122, B_120) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_10, c_139])).
% 2.76/1.37  tff(c_4, plain, (![A_1, B_11]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_11) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.37  tff(c_274, plain, (![B_124, C_125, A_126, C_127]: (~v1_relat_1(k8_relat_1(B_124, C_125)) | r1_tarski(k8_relat_1(A_126, C_125), k8_relat_1(B_124, C_127)) | ~v1_relat_1(k8_relat_1(A_126, C_125)) | ~r1_tarski(C_125, C_127) | ~v1_relat_1(C_127) | ~r1_tarski(A_126, B_124) | ~v1_relat_1(C_125))), inference(resolution, [status(thm)], [c_265, c_4])).
% 2.76/1.37  tff(c_14, plain, (~r1_tarski(k8_relat_1('#skF_3', '#skF_5'), k8_relat_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.37  tff(c_291, plain, (~v1_relat_1(k8_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1(k8_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_6') | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_274, c_14])).
% 2.76/1.37  tff(c_301, plain, (~v1_relat_1(k8_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1(k8_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_20, c_18, c_291])).
% 2.76/1.37  tff(c_302, plain, (~v1_relat_1(k8_relat_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_301])).
% 2.76/1.37  tff(c_305, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_302])).
% 2.76/1.37  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_305])).
% 2.76/1.37  tff(c_310, plain, (~v1_relat_1(k8_relat_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_301])).
% 2.76/1.37  tff(c_323, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_310])).
% 2.76/1.37  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_323])).
% 2.76/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.37  
% 2.76/1.37  Inference rules
% 2.76/1.37  ----------------------
% 2.76/1.37  #Ref     : 0
% 2.76/1.37  #Sup     : 74
% 2.76/1.37  #Fact    : 0
% 2.76/1.37  #Define  : 0
% 2.76/1.37  #Split   : 2
% 2.76/1.37  #Chain   : 0
% 2.76/1.37  #Close   : 0
% 2.76/1.37  
% 2.76/1.37  Ordering : KBO
% 2.76/1.37  
% 2.76/1.37  Simplification rules
% 2.76/1.37  ----------------------
% 2.76/1.37  #Subsume      : 13
% 2.76/1.37  #Demod        : 12
% 2.76/1.37  #Tautology    : 2
% 2.76/1.37  #SimpNegUnit  : 0
% 2.76/1.37  #BackRed      : 0
% 2.76/1.37  
% 2.76/1.37  #Partial instantiations: 0
% 2.76/1.37  #Strategies tried      : 1
% 2.76/1.37  
% 2.76/1.37  Timing (in seconds)
% 2.76/1.37  ----------------------
% 2.76/1.37  Preprocessing        : 0.26
% 2.76/1.37  Parsing              : 0.15
% 2.76/1.37  CNF conversion       : 0.02
% 2.76/1.37  Main loop            : 0.34
% 2.76/1.37  Inferencing          : 0.13
% 2.76/1.37  Reduction            : 0.07
% 2.76/1.37  Demodulation         : 0.05
% 2.76/1.37  BG Simplification    : 0.02
% 2.76/1.37  Subsumption          : 0.11
% 2.76/1.37  Abstraction          : 0.01
% 2.76/1.37  MUC search           : 0.00
% 2.76/1.37  Cooper               : 0.00
% 2.76/1.37  Total                : 0.64
% 2.76/1.37  Index Insertion      : 0.00
% 2.76/1.37  Index Deletion       : 0.00
% 2.76/1.37  Index Matching       : 0.00
% 2.76/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
