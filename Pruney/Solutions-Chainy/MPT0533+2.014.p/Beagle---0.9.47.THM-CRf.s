%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:19 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   50 (  93 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 249 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k8_relat_1(A_18,B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [B_23,A_22,C_24] :
      ( k8_relat_1(B_23,k8_relat_1(A_22,C_24)) = k8_relat_1(A_22,C_24)
      | ~ r1_tarski(A_22,B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(k8_relat_1(A_39,B_40),k8_relat_1(A_39,C_41))
      | ~ r1_tarski(B_40,C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_319,plain,(
    ! [A_68,C_69,B_70,C_71] :
      ( r1_tarski(k8_relat_1(A_68,C_69),k8_relat_1(B_70,C_71))
      | ~ r1_tarski(k8_relat_1(A_68,C_69),C_71)
      | ~ v1_relat_1(C_71)
      | ~ v1_relat_1(k8_relat_1(A_68,C_69))
      | ~ r1_tarski(A_68,B_70)
      | ~ v1_relat_1(C_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_49])).

tff(c_16,plain,(
    ~ r1_tarski(k8_relat_1('#skF_3','#skF_5'),k8_relat_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_324,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_3','#skF_5'),'#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k8_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_319,c_16])).

tff(c_358,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_3','#skF_5'),'#skF_6')
    | ~ v1_relat_1(k8_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_22,c_324])).

tff(c_359,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_362,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_359])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_362])).

tff(c_368,plain,(
    v1_relat_1(k8_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_10,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k8_relat_1(A_20,B_21),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [C_45,D_46,B_47,A_48] :
      ( r2_hidden(k4_tarski(C_45,D_46),B_47)
      | ~ r2_hidden(k4_tarski(C_45,D_46),A_48)
      | ~ r1_tarski(A_48,B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_49,B_50,B_51] :
      ( r2_hidden(k4_tarski('#skF_1'(A_49,B_50),'#skF_2'(A_49,B_50)),B_51)
      | ~ r1_tarski(A_49,B_51)
      | r1_tarski(A_49,B_50)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_2,plain,(
    ! [C_16,D_17,B_11,A_1] :
      ( r2_hidden(k4_tarski(C_16,D_17),B_11)
      | ~ r2_hidden(k4_tarski(C_16,D_17),A_1)
      | ~ r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_369,plain,(
    ! [A_72,B_73,B_74,B_75] :
      ( r2_hidden(k4_tarski('#skF_1'(A_72,B_73),'#skF_2'(A_72,B_73)),B_74)
      | ~ r1_tarski(B_75,B_74)
      | ~ v1_relat_1(B_75)
      | ~ r1_tarski(A_72,B_75)
      | r1_tarski(A_72,B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_379,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(k4_tarski('#skF_1'(A_72,B_73),'#skF_2'(A_72,B_73)),'#skF_6')
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(A_72,'#skF_5')
      | r1_tarski(A_72,B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_20,c_369])).

tff(c_390,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski('#skF_1'(A_76,B_77),'#skF_2'(A_76,B_77)),'#skF_6')
      | ~ r1_tarski(A_76,'#skF_5')
      | r1_tarski(A_76,B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_379])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_401,plain,(
    ! [A_78] :
      ( ~ r1_tarski(A_78,'#skF_5')
      | r1_tarski(A_78,'#skF_6')
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_390,c_4])).

tff(c_409,plain,(
    ! [A_20] :
      ( r1_tarski(k8_relat_1(A_20,'#skF_5'),'#skF_6')
      | ~ v1_relat_1(k8_relat_1(A_20,'#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_401])).

tff(c_416,plain,(
    ! [A_79] :
      ( r1_tarski(k8_relat_1(A_79,'#skF_5'),'#skF_6')
      | ~ v1_relat_1(k8_relat_1(A_79,'#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_409])).

tff(c_367,plain,(
    ~ r1_tarski(k8_relat_1('#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_421,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_416,c_367])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.32  
% 2.20/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.33  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.54/1.33  
% 2.54/1.33  %Foreground sorts:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Background operators:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Foreground operators:
% 2.54/1.33  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.33  
% 2.54/1.34  tff(f_70, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 2.54/1.34  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.54/1.34  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 2.54/1.34  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 2.54/1.34  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.54/1.34  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 2.54/1.34  tff(c_24, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_8, plain, (![A_18, B_19]: (v1_relat_1(k8_relat_1(A_18, B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.34  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_22, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_12, plain, (![B_23, A_22, C_24]: (k8_relat_1(B_23, k8_relat_1(A_22, C_24))=k8_relat_1(A_22, C_24) | ~r1_tarski(A_22, B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.34  tff(c_49, plain, (![A_39, B_40, C_41]: (r1_tarski(k8_relat_1(A_39, B_40), k8_relat_1(A_39, C_41)) | ~r1_tarski(B_40, C_41) | ~v1_relat_1(C_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.54/1.34  tff(c_319, plain, (![A_68, C_69, B_70, C_71]: (r1_tarski(k8_relat_1(A_68, C_69), k8_relat_1(B_70, C_71)) | ~r1_tarski(k8_relat_1(A_68, C_69), C_71) | ~v1_relat_1(C_71) | ~v1_relat_1(k8_relat_1(A_68, C_69)) | ~r1_tarski(A_68, B_70) | ~v1_relat_1(C_69))), inference(superposition, [status(thm), theory('equality')], [c_12, c_49])).
% 2.54/1.34  tff(c_16, plain, (~r1_tarski(k8_relat_1('#skF_3', '#skF_5'), k8_relat_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_324, plain, (~r1_tarski(k8_relat_1('#skF_3', '#skF_5'), '#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1(k8_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_319, c_16])).
% 2.54/1.34  tff(c_358, plain, (~r1_tarski(k8_relat_1('#skF_3', '#skF_5'), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_22, c_324])).
% 2.54/1.34  tff(c_359, plain, (~v1_relat_1(k8_relat_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_358])).
% 2.54/1.34  tff(c_362, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_359])).
% 2.54/1.34  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_362])).
% 2.54/1.34  tff(c_368, plain, (v1_relat_1(k8_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_358])).
% 2.54/1.34  tff(c_10, plain, (![A_20, B_21]: (r1_tarski(k8_relat_1(A_20, B_21), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.34  tff(c_20, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_6, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.34  tff(c_63, plain, (![C_45, D_46, B_47, A_48]: (r2_hidden(k4_tarski(C_45, D_46), B_47) | ~r2_hidden(k4_tarski(C_45, D_46), A_48) | ~r1_tarski(A_48, B_47) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.34  tff(c_67, plain, (![A_49, B_50, B_51]: (r2_hidden(k4_tarski('#skF_1'(A_49, B_50), '#skF_2'(A_49, B_50)), B_51) | ~r1_tarski(A_49, B_51) | r1_tarski(A_49, B_50) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.54/1.34  tff(c_2, plain, (![C_16, D_17, B_11, A_1]: (r2_hidden(k4_tarski(C_16, D_17), B_11) | ~r2_hidden(k4_tarski(C_16, D_17), A_1) | ~r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.34  tff(c_369, plain, (![A_72, B_73, B_74, B_75]: (r2_hidden(k4_tarski('#skF_1'(A_72, B_73), '#skF_2'(A_72, B_73)), B_74) | ~r1_tarski(B_75, B_74) | ~v1_relat_1(B_75) | ~r1_tarski(A_72, B_75) | r1_tarski(A_72, B_73) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_67, c_2])).
% 2.54/1.34  tff(c_379, plain, (![A_72, B_73]: (r2_hidden(k4_tarski('#skF_1'(A_72, B_73), '#skF_2'(A_72, B_73)), '#skF_6') | ~v1_relat_1('#skF_5') | ~r1_tarski(A_72, '#skF_5') | r1_tarski(A_72, B_73) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_20, c_369])).
% 2.54/1.34  tff(c_390, plain, (![A_76, B_77]: (r2_hidden(k4_tarski('#skF_1'(A_76, B_77), '#skF_2'(A_76, B_77)), '#skF_6') | ~r1_tarski(A_76, '#skF_5') | r1_tarski(A_76, B_77) | ~v1_relat_1(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_379])).
% 2.54/1.34  tff(c_4, plain, (![A_1, B_11]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_11) | r1_tarski(A_1, B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.34  tff(c_401, plain, (![A_78]: (~r1_tarski(A_78, '#skF_5') | r1_tarski(A_78, '#skF_6') | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_390, c_4])).
% 2.54/1.34  tff(c_409, plain, (![A_20]: (r1_tarski(k8_relat_1(A_20, '#skF_5'), '#skF_6') | ~v1_relat_1(k8_relat_1(A_20, '#skF_5')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_401])).
% 2.54/1.34  tff(c_416, plain, (![A_79]: (r1_tarski(k8_relat_1(A_79, '#skF_5'), '#skF_6') | ~v1_relat_1(k8_relat_1(A_79, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_409])).
% 2.54/1.34  tff(c_367, plain, (~r1_tarski(k8_relat_1('#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_358])).
% 2.54/1.34  tff(c_421, plain, (~v1_relat_1(k8_relat_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_416, c_367])).
% 2.54/1.34  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_368, c_421])).
% 2.54/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  Inference rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Ref     : 0
% 2.54/1.34  #Sup     : 109
% 2.54/1.34  #Fact    : 0
% 2.54/1.34  #Define  : 0
% 2.54/1.34  #Split   : 1
% 2.54/1.34  #Chain   : 0
% 2.54/1.34  #Close   : 0
% 2.54/1.34  
% 2.54/1.34  Ordering : KBO
% 2.54/1.34  
% 2.54/1.34  Simplification rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Subsume      : 17
% 2.54/1.34  #Demod        : 10
% 2.54/1.34  #Tautology    : 24
% 2.54/1.34  #SimpNegUnit  : 0
% 2.54/1.34  #BackRed      : 0
% 2.54/1.34  
% 2.54/1.34  #Partial instantiations: 0
% 2.54/1.34  #Strategies tried      : 1
% 2.54/1.34  
% 2.54/1.34  Timing (in seconds)
% 2.54/1.34  ----------------------
% 2.54/1.34  Preprocessing        : 0.27
% 2.54/1.34  Parsing              : 0.15
% 2.54/1.34  CNF conversion       : 0.02
% 2.54/1.34  Main loop            : 0.29
% 2.54/1.34  Inferencing          : 0.12
% 2.54/1.34  Reduction            : 0.07
% 2.54/1.34  Demodulation         : 0.05
% 2.54/1.34  BG Simplification    : 0.02
% 2.54/1.34  Subsumption          : 0.07
% 2.54/1.34  Abstraction          : 0.01
% 2.54/1.34  MUC search           : 0.00
% 2.54/1.34  Cooper               : 0.00
% 2.54/1.34  Total                : 0.59
% 2.54/1.34  Index Insertion      : 0.00
% 2.54/1.34  Index Deletion       : 0.00
% 2.54/1.34  Index Matching       : 0.00
% 2.54/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
