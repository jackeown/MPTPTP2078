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
% DateTime   : Thu Dec  3 10:01:11 EST 2020

% Result     : Theorem 9.90s
% Output     : CNFRefutation 9.90s
% Verified   : 
% Statistics : Number of formulae       :   61 (  92 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  116 ( 180 expanded)
%              Number of equality atoms :   35 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( k7_relat_1(k7_relat_1(C_12,A_10),B_11) = k7_relat_1(C_12,k3_xboole_0(A_10,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    ! [B_40,A_41] :
      ( k7_relat_1(B_40,A_41) = B_40
      | ~ r1_tarski(k1_relat_1(B_40),A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_657,plain,(
    ! [B_73,A_74] :
      ( k7_relat_1(k7_relat_1(B_73,A_74),A_74) = k7_relat_1(B_73,A_74)
      | ~ v1_relat_1(k7_relat_1(B_73,A_74))
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_670,plain,(
    ! [A_8,B_9] :
      ( k7_relat_1(k7_relat_1(A_8,B_9),B_9) = k7_relat_1(A_8,B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_657])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_80,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,C_34)
      | ~ r1_tarski(B_35,C_34)
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,'#skF_3')
      | ~ r1_tarski(A_36,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_80])).

tff(c_99,plain,(
    ! [B_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,'#skF_2')),'#skF_3')
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_20,c_90])).

tff(c_1069,plain,(
    ! [B_87] :
      ( k7_relat_1(k7_relat_1(B_87,'#skF_2'),'#skF_3') = k7_relat_1(B_87,'#skF_2')
      | ~ v1_relat_1(k7_relat_1(B_87,'#skF_2'))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_99,c_118])).

tff(c_1087,plain,(
    ! [A_88] :
      ( k7_relat_1(k7_relat_1(A_88,'#skF_2'),'#skF_3') = k7_relat_1(A_88,'#skF_2')
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_12,c_1069])).

tff(c_3515,plain,(
    ! [A_174] :
      ( k7_relat_1(k7_relat_1(A_174,'#skF_2'),'#skF_2') = k7_relat_1(k7_relat_1(A_174,'#skF_2'),'#skF_3')
      | ~ v1_relat_1(k7_relat_1(A_174,'#skF_2'))
      | ~ v1_relat_1(A_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_1087])).

tff(c_3537,plain,(
    ! [A_175] :
      ( k7_relat_1(k7_relat_1(A_175,'#skF_2'),'#skF_2') = k7_relat_1(k7_relat_1(A_175,'#skF_2'),'#skF_3')
      | ~ v1_relat_1(A_175) ) ),
    inference(resolution,[status(thm)],[c_12,c_3515])).

tff(c_3691,plain,(
    ! [A_176] :
      ( k7_relat_1(k7_relat_1(A_176,'#skF_2'),'#skF_3') = k7_relat_1(A_176,k3_xboole_0('#skF_2','#skF_2'))
      | ~ v1_relat_1(A_176)
      | ~ v1_relat_1(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3537,c_14])).

tff(c_3792,plain,(
    ! [C_12] :
      ( k7_relat_1(C_12,k3_xboole_0('#skF_2','#skF_2')) = k7_relat_1(C_12,k3_xboole_0('#skF_2','#skF_3'))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3691])).

tff(c_5367,plain,(
    ! [C_199] :
      ( k7_relat_1(C_199,k3_xboole_0('#skF_2','#skF_2')) = k7_relat_1(C_199,k3_xboole_0('#skF_3','#skF_2'))
      | ~ v1_relat_1(C_199)
      | ~ v1_relat_1(C_199)
      | ~ v1_relat_1(C_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3792])).

tff(c_231,plain,(
    ! [C_52,A_53,B_54] :
      ( k7_relat_1(k7_relat_1(C_52,A_53),B_54) = k7_relat_1(C_52,A_53)
      | ~ r1_tarski(A_53,B_54)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_868,plain,(
    ! [C_79,A_80,B_81] :
      ( k7_relat_1(C_79,k3_xboole_0(A_80,B_81)) = k7_relat_1(C_79,A_80)
      | ~ r1_tarski(A_80,B_81)
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(C_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_231])).

tff(c_956,plain,(
    ! [C_79,B_2,A_1] :
      ( k7_relat_1(C_79,k3_xboole_0(B_2,A_1)) = k7_relat_1(C_79,A_1)
      | ~ r1_tarski(A_1,B_2)
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(C_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_868])).

tff(c_5434,plain,(
    ! [C_199] :
      ( k7_relat_1(C_199,k3_xboole_0('#skF_3','#skF_2')) = k7_relat_1(C_199,'#skF_2')
      | ~ r1_tarski('#skF_2','#skF_2')
      | ~ v1_relat_1(C_199)
      | ~ v1_relat_1(C_199)
      | ~ v1_relat_1(C_199)
      | ~ v1_relat_1(C_199)
      | ~ v1_relat_1(C_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5367,c_956])).

tff(c_5668,plain,(
    ! [C_203] :
      ( k7_relat_1(C_203,k3_xboole_0('#skF_3','#skF_2')) = k7_relat_1(C_203,'#skF_2')
      | ~ v1_relat_1(C_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5434])).

tff(c_5790,plain,(
    ! [C_203] :
      ( k9_relat_1(C_203,k3_xboole_0('#skF_3','#skF_2')) = k2_relat_1(k7_relat_1(C_203,'#skF_2'))
      | ~ v1_relat_1(C_203)
      | ~ v1_relat_1(C_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5668,c_18])).

tff(c_132,plain,(
    ! [C_42,A_43,B_44] :
      ( k7_relat_1(k7_relat_1(C_42,A_43),B_44) = k7_relat_1(C_42,k3_xboole_0(A_43,B_44))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1971,plain,(
    ! [C_118,A_119,B_120] :
      ( k2_relat_1(k7_relat_1(C_118,k3_xboole_0(A_119,B_120))) = k9_relat_1(k7_relat_1(C_118,A_119),B_120)
      | ~ v1_relat_1(k7_relat_1(C_118,A_119))
      | ~ v1_relat_1(C_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_18])).

tff(c_12512,plain,(
    ! [C_316,A_317,B_318] :
      ( k9_relat_1(k7_relat_1(C_316,A_317),B_318) = k9_relat_1(C_316,k3_xboole_0(A_317,B_318))
      | ~ v1_relat_1(C_316)
      | ~ v1_relat_1(k7_relat_1(C_316,A_317))
      | ~ v1_relat_1(C_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1971,c_18])).

tff(c_12608,plain,(
    ! [A_319,B_320,B_321] :
      ( k9_relat_1(k7_relat_1(A_319,B_320),B_321) = k9_relat_1(A_319,k3_xboole_0(B_320,B_321))
      | ~ v1_relat_1(A_319) ) ),
    inference(resolution,[status(thm)],[c_12,c_12512])).

tff(c_24,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12661,plain,
    ( k9_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12608,c_24])).

tff(c_12824,plain,(
    k9_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k9_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12661])).

tff(c_12829,plain,
    ( k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5790,c_12824])).

tff(c_12831,plain,(
    k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_12829])).

tff(c_12834,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_12831])).

tff(c_12838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:56:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.90/3.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.90/3.42  
% 9.90/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.90/3.42  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 9.90/3.42  
% 9.90/3.42  %Foreground sorts:
% 9.90/3.42  
% 9.90/3.42  
% 9.90/3.42  %Background operators:
% 9.90/3.42  
% 9.90/3.42  
% 9.90/3.42  %Foreground operators:
% 9.90/3.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.90/3.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.90/3.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.90/3.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.90/3.42  tff('#skF_2', type, '#skF_2': $i).
% 9.90/3.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.90/3.42  tff('#skF_3', type, '#skF_3': $i).
% 9.90/3.42  tff('#skF_1', type, '#skF_1': $i).
% 9.90/3.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.90/3.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.90/3.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.90/3.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.90/3.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.90/3.42  
% 9.90/3.44  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 9.90/3.44  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 9.90/3.44  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.90/3.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.90/3.44  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 9.90/3.44  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.90/3.44  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 9.90/3.44  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 9.90/3.44  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.90/3.44  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 9.90/3.44  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.90/3.44  tff(c_18, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.90/3.44  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.90/3.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.90/3.44  tff(c_14, plain, (![C_12, A_10, B_11]: (k7_relat_1(k7_relat_1(C_12, A_10), B_11)=k7_relat_1(C_12, k3_xboole_0(A_10, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.90/3.44  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.90/3.44  tff(c_20, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.90/3.44  tff(c_118, plain, (![B_40, A_41]: (k7_relat_1(B_40, A_41)=B_40 | ~r1_tarski(k1_relat_1(B_40), A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.90/3.44  tff(c_657, plain, (![B_73, A_74]: (k7_relat_1(k7_relat_1(B_73, A_74), A_74)=k7_relat_1(B_73, A_74) | ~v1_relat_1(k7_relat_1(B_73, A_74)) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_20, c_118])).
% 9.90/3.44  tff(c_670, plain, (![A_8, B_9]: (k7_relat_1(k7_relat_1(A_8, B_9), B_9)=k7_relat_1(A_8, B_9) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_12, c_657])).
% 9.90/3.44  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.90/3.44  tff(c_80, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, C_34) | ~r1_tarski(B_35, C_34) | ~r1_tarski(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.90/3.44  tff(c_90, plain, (![A_36]: (r1_tarski(A_36, '#skF_3') | ~r1_tarski(A_36, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_80])).
% 9.90/3.44  tff(c_99, plain, (![B_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, '#skF_2')), '#skF_3') | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_20, c_90])).
% 9.90/3.44  tff(c_1069, plain, (![B_87]: (k7_relat_1(k7_relat_1(B_87, '#skF_2'), '#skF_3')=k7_relat_1(B_87, '#skF_2') | ~v1_relat_1(k7_relat_1(B_87, '#skF_2')) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_99, c_118])).
% 9.90/3.44  tff(c_1087, plain, (![A_88]: (k7_relat_1(k7_relat_1(A_88, '#skF_2'), '#skF_3')=k7_relat_1(A_88, '#skF_2') | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_12, c_1069])).
% 9.90/3.44  tff(c_3515, plain, (![A_174]: (k7_relat_1(k7_relat_1(A_174, '#skF_2'), '#skF_2')=k7_relat_1(k7_relat_1(A_174, '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1(A_174, '#skF_2')) | ~v1_relat_1(A_174))), inference(superposition, [status(thm), theory('equality')], [c_670, c_1087])).
% 9.90/3.44  tff(c_3537, plain, (![A_175]: (k7_relat_1(k7_relat_1(A_175, '#skF_2'), '#skF_2')=k7_relat_1(k7_relat_1(A_175, '#skF_2'), '#skF_3') | ~v1_relat_1(A_175))), inference(resolution, [status(thm)], [c_12, c_3515])).
% 9.90/3.44  tff(c_3691, plain, (![A_176]: (k7_relat_1(k7_relat_1(A_176, '#skF_2'), '#skF_3')=k7_relat_1(A_176, k3_xboole_0('#skF_2', '#skF_2')) | ~v1_relat_1(A_176) | ~v1_relat_1(A_176))), inference(superposition, [status(thm), theory('equality')], [c_3537, c_14])).
% 9.90/3.44  tff(c_3792, plain, (![C_12]: (k7_relat_1(C_12, k3_xboole_0('#skF_2', '#skF_2'))=k7_relat_1(C_12, k3_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1(C_12) | ~v1_relat_1(C_12) | ~v1_relat_1(C_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3691])).
% 9.90/3.44  tff(c_5367, plain, (![C_199]: (k7_relat_1(C_199, k3_xboole_0('#skF_2', '#skF_2'))=k7_relat_1(C_199, k3_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1(C_199) | ~v1_relat_1(C_199) | ~v1_relat_1(C_199))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3792])).
% 9.90/3.44  tff(c_231, plain, (![C_52, A_53, B_54]: (k7_relat_1(k7_relat_1(C_52, A_53), B_54)=k7_relat_1(C_52, A_53) | ~r1_tarski(A_53, B_54) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.90/3.44  tff(c_868, plain, (![C_79, A_80, B_81]: (k7_relat_1(C_79, k3_xboole_0(A_80, B_81))=k7_relat_1(C_79, A_80) | ~r1_tarski(A_80, B_81) | ~v1_relat_1(C_79) | ~v1_relat_1(C_79))), inference(superposition, [status(thm), theory('equality')], [c_14, c_231])).
% 9.90/3.44  tff(c_956, plain, (![C_79, B_2, A_1]: (k7_relat_1(C_79, k3_xboole_0(B_2, A_1))=k7_relat_1(C_79, A_1) | ~r1_tarski(A_1, B_2) | ~v1_relat_1(C_79) | ~v1_relat_1(C_79))), inference(superposition, [status(thm), theory('equality')], [c_2, c_868])).
% 9.90/3.44  tff(c_5434, plain, (![C_199]: (k7_relat_1(C_199, k3_xboole_0('#skF_3', '#skF_2'))=k7_relat_1(C_199, '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1(C_199) | ~v1_relat_1(C_199) | ~v1_relat_1(C_199) | ~v1_relat_1(C_199) | ~v1_relat_1(C_199))), inference(superposition, [status(thm), theory('equality')], [c_5367, c_956])).
% 9.90/3.44  tff(c_5668, plain, (![C_203]: (k7_relat_1(C_203, k3_xboole_0('#skF_3', '#skF_2'))=k7_relat_1(C_203, '#skF_2') | ~v1_relat_1(C_203))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5434])).
% 9.90/3.44  tff(c_5790, plain, (![C_203]: (k9_relat_1(C_203, k3_xboole_0('#skF_3', '#skF_2'))=k2_relat_1(k7_relat_1(C_203, '#skF_2')) | ~v1_relat_1(C_203) | ~v1_relat_1(C_203))), inference(superposition, [status(thm), theory('equality')], [c_5668, c_18])).
% 9.90/3.44  tff(c_132, plain, (![C_42, A_43, B_44]: (k7_relat_1(k7_relat_1(C_42, A_43), B_44)=k7_relat_1(C_42, k3_xboole_0(A_43, B_44)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.90/3.44  tff(c_1971, plain, (![C_118, A_119, B_120]: (k2_relat_1(k7_relat_1(C_118, k3_xboole_0(A_119, B_120)))=k9_relat_1(k7_relat_1(C_118, A_119), B_120) | ~v1_relat_1(k7_relat_1(C_118, A_119)) | ~v1_relat_1(C_118))), inference(superposition, [status(thm), theory('equality')], [c_132, c_18])).
% 9.90/3.44  tff(c_12512, plain, (![C_316, A_317, B_318]: (k9_relat_1(k7_relat_1(C_316, A_317), B_318)=k9_relat_1(C_316, k3_xboole_0(A_317, B_318)) | ~v1_relat_1(C_316) | ~v1_relat_1(k7_relat_1(C_316, A_317)) | ~v1_relat_1(C_316))), inference(superposition, [status(thm), theory('equality')], [c_1971, c_18])).
% 9.90/3.44  tff(c_12608, plain, (![A_319, B_320, B_321]: (k9_relat_1(k7_relat_1(A_319, B_320), B_321)=k9_relat_1(A_319, k3_xboole_0(B_320, B_321)) | ~v1_relat_1(A_319))), inference(resolution, [status(thm)], [c_12, c_12512])).
% 9.90/3.44  tff(c_24, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.90/3.44  tff(c_12661, plain, (k9_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12608, c_24])).
% 9.90/3.44  tff(c_12824, plain, (k9_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12661])).
% 9.90/3.44  tff(c_12829, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5790, c_12824])).
% 9.90/3.44  tff(c_12831, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_12829])).
% 9.90/3.44  tff(c_12834, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_12831])).
% 9.90/3.44  tff(c_12838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_12834])).
% 9.90/3.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.90/3.44  
% 9.90/3.44  Inference rules
% 9.90/3.44  ----------------------
% 9.90/3.44  #Ref     : 0
% 9.90/3.44  #Sup     : 3639
% 9.90/3.44  #Fact    : 0
% 9.90/3.44  #Define  : 0
% 9.90/3.44  #Split   : 1
% 9.90/3.44  #Chain   : 0
% 9.90/3.44  #Close   : 0
% 9.90/3.44  
% 9.90/3.44  Ordering : KBO
% 9.90/3.44  
% 9.90/3.44  Simplification rules
% 9.90/3.44  ----------------------
% 9.90/3.44  #Subsume      : 873
% 9.90/3.44  #Demod        : 201
% 9.90/3.44  #Tautology    : 279
% 9.90/3.44  #SimpNegUnit  : 0
% 9.90/3.44  #BackRed      : 0
% 9.90/3.44  
% 9.90/3.44  #Partial instantiations: 0
% 9.90/3.44  #Strategies tried      : 1
% 9.90/3.44  
% 9.90/3.44  Timing (in seconds)
% 9.90/3.44  ----------------------
% 9.90/3.44  Preprocessing        : 0.28
% 9.90/3.44  Parsing              : 0.16
% 9.90/3.44  CNF conversion       : 0.02
% 9.90/3.44  Main loop            : 2.39
% 9.90/3.44  Inferencing          : 0.71
% 9.90/3.44  Reduction            : 0.64
% 9.90/3.44  Demodulation         : 0.47
% 9.90/3.44  BG Simplification    : 0.11
% 9.90/3.44  Subsumption          : 0.79
% 9.90/3.45  Abstraction          : 0.12
% 9.90/3.45  MUC search           : 0.00
% 9.90/3.45  Cooper               : 0.00
% 9.90/3.45  Total                : 2.71
% 9.90/3.45  Index Insertion      : 0.00
% 9.90/3.45  Index Deletion       : 0.00
% 9.90/3.45  Index Matching       : 0.00
% 9.90/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
