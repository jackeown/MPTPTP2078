%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:11 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :   85 ( 124 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(k2_relat_1(B),k1_relat_1(k7_relat_1(C,A)))
             => k5_relat_1(B,k7_relat_1(C,A)) = k5_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_34,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_31,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),A_25)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_25] : r1_tarski(A_25,A_25) ),
    inference(resolution,[status(thm)],[c_31,c_4])).

tff(c_24,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k7_relat_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [C_28,B_29,A_30] :
      ( r2_hidden(C_28,B_29)
      | ~ r2_hidden(C_28,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_45,B_46,B_47] :
      ( r2_hidden('#skF_1'(A_45,B_46),B_47)
      | ~ r1_tarski(A_45,B_47)
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_275,plain,(
    ! [A_67,B_68,B_69,B_70] :
      ( r2_hidden('#skF_1'(A_67,B_68),B_69)
      | ~ r1_tarski(B_70,B_69)
      | ~ r1_tarski(A_67,B_70)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_309,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),k1_relat_1(k7_relat_1('#skF_4','#skF_2')))
      | ~ r1_tarski(A_72,k2_relat_1('#skF_3'))
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_24,c_275])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(A_16,B_17)
      | ~ r2_hidden(A_16,k1_relat_1(k7_relat_1(C_18,B_17)))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_315,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_72,k2_relat_1('#skF_3'))
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_309,c_18])).

tff(c_352,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),'#skF_2')
      | ~ r1_tarski(A_75,k2_relat_1('#skF_3'))
      | r1_tarski(A_75,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_315])).

tff(c_361,plain,(
    ! [A_77] :
      ( ~ r1_tarski(A_77,k2_relat_1('#skF_3'))
      | r1_tarski(A_77,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_352,c_4])).

tff(c_371,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_361])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( k5_relat_1(B_15,k6_relat_1(A_14)) = B_15
      | ~ r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_376,plain,
    ( k5_relat_1('#skF_3',k6_relat_1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_371,c_12])).

tff(c_380,plain,(
    k5_relat_1('#skF_3',k6_relat_1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_376])).

tff(c_10,plain,(
    ! [A_7,B_11,C_13] :
      ( k5_relat_1(k5_relat_1(A_7,B_11),C_13) = k5_relat_1(A_7,k5_relat_1(B_11,C_13))
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_450,plain,(
    ! [C_13] :
      ( k5_relat_1('#skF_3',k5_relat_1(k6_relat_1('#skF_2'),C_13)) = k5_relat_1('#skF_3',C_13)
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(k6_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_10])).

tff(c_489,plain,(
    ! [C_85] :
      ( k5_relat_1('#skF_3',k5_relat_1(k6_relat_1('#skF_2'),C_85)) = k5_relat_1('#skF_3',C_85)
      | ~ v1_relat_1(C_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8,c_450])).

tff(c_536,plain,(
    ! [B_86] :
      ( k5_relat_1('#skF_3',k7_relat_1(B_86,'#skF_2')) = k5_relat_1('#skF_3',B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_489])).

tff(c_22,plain,(
    k5_relat_1('#skF_3',k7_relat_1('#skF_4','#skF_2')) != k5_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_548,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_22])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.32  
% 2.49/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.32  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.32  
% 2.49/1.32  %Foreground sorts:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Background operators:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Foreground operators:
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.49/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.32  
% 2.49/1.33  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_relat_1)).
% 2.49/1.33  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.49/1.33  tff(f_34, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.49/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.49/1.33  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.49/1.33  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.49/1.33  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 2.49/1.33  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.49/1.33  tff(c_20, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.49/1.33  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.49/1.33  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.49/1.33  tff(c_31, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), A_25) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.33  tff(c_36, plain, (![A_25]: (r1_tarski(A_25, A_25))), inference(resolution, [status(thm)], [c_31, c_4])).
% 2.49/1.33  tff(c_24, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k7_relat_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.49/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.33  tff(c_38, plain, (![C_28, B_29, A_30]: (r2_hidden(C_28, B_29) | ~r2_hidden(C_28, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.33  tff(c_126, plain, (![A_45, B_46, B_47]: (r2_hidden('#skF_1'(A_45, B_46), B_47) | ~r1_tarski(A_45, B_47) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_6, c_38])).
% 2.49/1.33  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.33  tff(c_275, plain, (![A_67, B_68, B_69, B_70]: (r2_hidden('#skF_1'(A_67, B_68), B_69) | ~r1_tarski(B_70, B_69) | ~r1_tarski(A_67, B_70) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_126, c_2])).
% 2.49/1.33  tff(c_309, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), k1_relat_1(k7_relat_1('#skF_4', '#skF_2'))) | ~r1_tarski(A_72, k2_relat_1('#skF_3')) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_24, c_275])).
% 2.49/1.33  tff(c_18, plain, (![A_16, B_17, C_18]: (r2_hidden(A_16, B_17) | ~r2_hidden(A_16, k1_relat_1(k7_relat_1(C_18, B_17))) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.33  tff(c_315, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), '#skF_2') | ~v1_relat_1('#skF_4') | ~r1_tarski(A_72, k2_relat_1('#skF_3')) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_309, c_18])).
% 2.49/1.33  tff(c_352, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), '#skF_2') | ~r1_tarski(A_75, k2_relat_1('#skF_3')) | r1_tarski(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_315])).
% 2.49/1.33  tff(c_361, plain, (![A_77]: (~r1_tarski(A_77, k2_relat_1('#skF_3')) | r1_tarski(A_77, '#skF_2'))), inference(resolution, [status(thm)], [c_352, c_4])).
% 2.49/1.33  tff(c_371, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_36, c_361])).
% 2.49/1.33  tff(c_12, plain, (![B_15, A_14]: (k5_relat_1(B_15, k6_relat_1(A_14))=B_15 | ~r1_tarski(k2_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.49/1.33  tff(c_376, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_371, c_12])).
% 2.49/1.33  tff(c_380, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_376])).
% 2.49/1.33  tff(c_10, plain, (![A_7, B_11, C_13]: (k5_relat_1(k5_relat_1(A_7, B_11), C_13)=k5_relat_1(A_7, k5_relat_1(B_11, C_13)) | ~v1_relat_1(C_13) | ~v1_relat_1(B_11) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.49/1.33  tff(c_450, plain, (![C_13]: (k5_relat_1('#skF_3', k5_relat_1(k6_relat_1('#skF_2'), C_13))=k5_relat_1('#skF_3', C_13) | ~v1_relat_1(C_13) | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_380, c_10])).
% 2.49/1.33  tff(c_489, plain, (![C_85]: (k5_relat_1('#skF_3', k5_relat_1(k6_relat_1('#skF_2'), C_85))=k5_relat_1('#skF_3', C_85) | ~v1_relat_1(C_85))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8, c_450])).
% 2.49/1.33  tff(c_536, plain, (![B_86]: (k5_relat_1('#skF_3', k7_relat_1(B_86, '#skF_2'))=k5_relat_1('#skF_3', B_86) | ~v1_relat_1(B_86) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_20, c_489])).
% 2.49/1.33  tff(c_22, plain, (k5_relat_1('#skF_3', k7_relat_1('#skF_4', '#skF_2'))!=k5_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.49/1.33  tff(c_548, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_536, c_22])).
% 2.49/1.33  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_548])).
% 2.49/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.33  
% 2.49/1.33  Inference rules
% 2.49/1.33  ----------------------
% 2.49/1.33  #Ref     : 0
% 2.49/1.33  #Sup     : 117
% 2.49/1.33  #Fact    : 0
% 2.49/1.33  #Define  : 0
% 2.49/1.33  #Split   : 0
% 2.49/1.33  #Chain   : 0
% 2.49/1.33  #Close   : 0
% 2.49/1.33  
% 2.49/1.33  Ordering : KBO
% 2.49/1.33  
% 2.49/1.33  Simplification rules
% 2.49/1.33  ----------------------
% 2.49/1.33  #Subsume      : 7
% 2.49/1.33  #Demod        : 52
% 2.49/1.33  #Tautology    : 29
% 2.49/1.33  #SimpNegUnit  : 0
% 2.49/1.33  #BackRed      : 0
% 2.49/1.33  
% 2.49/1.33  #Partial instantiations: 0
% 2.49/1.33  #Strategies tried      : 1
% 2.49/1.33  
% 2.49/1.33  Timing (in seconds)
% 2.49/1.33  ----------------------
% 2.49/1.33  Preprocessing        : 0.28
% 2.49/1.33  Parsing              : 0.16
% 2.49/1.33  CNF conversion       : 0.02
% 2.49/1.33  Main loop            : 0.30
% 2.49/1.34  Inferencing          : 0.13
% 2.49/1.34  Reduction            : 0.08
% 2.49/1.34  Demodulation         : 0.06
% 2.49/1.34  BG Simplification    : 0.02
% 2.49/1.34  Subsumption          : 0.06
% 2.49/1.34  Abstraction          : 0.02
% 2.49/1.34  MUC search           : 0.00
% 2.49/1.34  Cooper               : 0.00
% 2.49/1.34  Total                : 0.61
% 2.49/1.34  Index Insertion      : 0.00
% 2.49/1.34  Index Deletion       : 0.00
% 2.49/1.34  Index Matching       : 0.00
% 2.49/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
