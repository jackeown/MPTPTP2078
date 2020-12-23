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
% DateTime   : Thu Dec  3 09:55:30 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 146 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :   80 ( 166 expanded)
%              Number of equality atoms :   53 ( 102 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_18,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_147,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_375,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k3_subset_1(A_58,B_59),k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k3_subset_1(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2312,plain,(
    ! [A_102,B_103] :
      ( k4_xboole_0(A_102,k3_subset_1(A_102,B_103)) = k3_subset_1(A_102,k3_subset_1(A_102,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(resolution,[status(thm)],[c_375,c_20])).

tff(c_2318,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_2312])).

tff(c_2325,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2318])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_16] : k1_subset_1(A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_subset_1(A_27)) = k2_subset_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_35,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_subset_1(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_37,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_xboole_0) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_35])).

tff(c_30,plain,(
    ! [A_28] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,(
    ! [A_28] : k3_subset_1(A_28,k3_subset_1(A_28,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_142])).

tff(c_149,plain,(
    ! [A_28] : k3_subset_1(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_146])).

tff(c_389,plain,(
    ! [A_27] :
      ( m1_subset_1(A_27,k1_zfmisc_1(A_27))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_375])).

tff(c_396,plain,(
    ! [A_60] : m1_subset_1(A_60,k1_zfmisc_1(A_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_389])).

tff(c_399,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k3_subset_1(A_60,A_60) ),
    inference(resolution,[status(thm)],[c_396,c_20])).

tff(c_406,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_399])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_433,plain,(
    ! [A_61] : k5_xboole_0(A_61,k1_xboole_0) = k2_xboole_0(A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_10])).

tff(c_456,plain,(
    ! [A_61] : k5_xboole_0(A_61,k1_xboole_0) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_433])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_423,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(B_8,k4_xboole_0(A_7,B_8))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_8])).

tff(c_453,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(B_8,A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_423])).

tff(c_236,plain,(
    ! [A_51,B_52,C_53] : k4_xboole_0(k4_xboole_0(A_51,B_52),C_53) = k4_xboole_0(A_51,k2_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_778,plain,(
    ! [C_73,A_74,B_75] : k5_xboole_0(C_73,k4_xboole_0(A_74,k2_xboole_0(B_75,C_73))) = k2_xboole_0(C_73,k4_xboole_0(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_10])).

tff(c_791,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_778])).

tff(c_835,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_791])).

tff(c_2337,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2325,c_835])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k3_subset_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_171])).

tff(c_200,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_6])).

tff(c_206,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_200])).

tff(c_2386,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_206])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k3_subset_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_657,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_subset_1(A_67,B_68,C_69) = k2_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3560,plain,(
    ! [A_118,B_119,B_120] :
      ( k4_subset_1(A_118,B_119,k3_subset_1(A_118,B_120)) = k2_xboole_0(B_119,k3_subset_1(A_118,B_120))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_118)) ) ),
    inference(resolution,[status(thm)],[c_22,c_657])).

tff(c_4129,plain,(
    ! [B_127] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_127)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_127))
      | ~ m1_subset_1(B_127,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_3560])).

tff(c_4140,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_4129])).

tff(c_4149,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2386,c_4140])).

tff(c_4151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_4149])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.86  
% 4.63/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.86  %$ m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.63/1.86  
% 4.63/1.86  %Foreground sorts:
% 4.63/1.86  
% 4.63/1.86  
% 4.63/1.86  %Background operators:
% 4.63/1.86  
% 4.63/1.86  
% 4.63/1.86  %Foreground operators:
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.63/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.63/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.63/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.63/1.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.63/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.63/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.63/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.63/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.86  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.63/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.63/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.86  
% 4.63/1.87  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.63/1.87  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.63/1.87  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.63/1.87  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.63/1.87  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.63/1.87  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.63/1.87  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.63/1.87  tff(f_63, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 4.63/1.87  tff(f_65, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.63/1.87  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.63/1.87  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.63/1.87  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.63/1.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.63/1.87  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.63/1.87  tff(c_18, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.87  tff(c_32, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.63/1.87  tff(c_36, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32])).
% 4.63/1.87  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.63/1.87  tff(c_142, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.63/1.87  tff(c_147, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_142])).
% 4.63/1.87  tff(c_375, plain, (![A_58, B_59]: (m1_subset_1(k3_subset_1(A_58, B_59), k1_zfmisc_1(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.87  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k3_subset_1(A_18, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.63/1.87  tff(c_2312, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k3_subset_1(A_102, B_103))=k3_subset_1(A_102, k3_subset_1(A_102, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(resolution, [status(thm)], [c_375, c_20])).
% 4.63/1.87  tff(c_2318, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_2312])).
% 4.63/1.87  tff(c_2325, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2318])).
% 4.63/1.87  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.63/1.87  tff(c_16, plain, (![A_16]: (k1_subset_1(A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.87  tff(c_28, plain, (![A_27]: (k3_subset_1(A_27, k1_subset_1(A_27))=k2_subset_1(A_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.63/1.87  tff(c_35, plain, (![A_27]: (k3_subset_1(A_27, k1_subset_1(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28])).
% 4.63/1.87  tff(c_37, plain, (![A_27]: (k3_subset_1(A_27, k1_xboole_0)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_35])).
% 4.63/1.87  tff(c_30, plain, (![A_28]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.63/1.87  tff(c_146, plain, (![A_28]: (k3_subset_1(A_28, k3_subset_1(A_28, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_142])).
% 4.63/1.87  tff(c_149, plain, (![A_28]: (k3_subset_1(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37, c_146])).
% 4.63/1.87  tff(c_389, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_375])).
% 4.63/1.87  tff(c_396, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1(A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_389])).
% 4.63/1.87  tff(c_399, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k3_subset_1(A_60, A_60))), inference(resolution, [status(thm)], [c_396, c_20])).
% 4.63/1.87  tff(c_406, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_399])).
% 4.63/1.87  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.87  tff(c_433, plain, (![A_61]: (k5_xboole_0(A_61, k1_xboole_0)=k2_xboole_0(A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_406, c_10])).
% 4.63/1.87  tff(c_456, plain, (![A_61]: (k5_xboole_0(A_61, k1_xboole_0)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_433])).
% 4.63/1.87  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.87  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.63/1.87  tff(c_423, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(B_8, k4_xboole_0(A_7, B_8)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_406, c_8])).
% 4.63/1.87  tff(c_453, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(B_8, A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_423])).
% 4.63/1.87  tff(c_236, plain, (![A_51, B_52, C_53]: (k4_xboole_0(k4_xboole_0(A_51, B_52), C_53)=k4_xboole_0(A_51, k2_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.63/1.87  tff(c_778, plain, (![C_73, A_74, B_75]: (k5_xboole_0(C_73, k4_xboole_0(A_74, k2_xboole_0(B_75, C_73)))=k2_xboole_0(C_73, k4_xboole_0(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_236, c_10])).
% 4.63/1.87  tff(c_791, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k5_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_453, c_778])).
% 4.63/1.87  tff(c_835, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_456, c_791])).
% 4.63/1.87  tff(c_2337, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2325, c_835])).
% 4.63/1.87  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.63/1.87  tff(c_171, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k3_subset_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.63/1.87  tff(c_178, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_171])).
% 4.63/1.87  tff(c_200, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_178, c_6])).
% 4.63/1.87  tff(c_206, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_200])).
% 4.63/1.87  tff(c_2386, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_206])).
% 4.63/1.87  tff(c_22, plain, (![A_20, B_21]: (m1_subset_1(k3_subset_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.87  tff(c_657, plain, (![A_67, B_68, C_69]: (k4_subset_1(A_67, B_68, C_69)=k2_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.63/1.87  tff(c_3560, plain, (![A_118, B_119, B_120]: (k4_subset_1(A_118, B_119, k3_subset_1(A_118, B_120))=k2_xboole_0(B_119, k3_subset_1(A_118, B_120)) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_120, k1_zfmisc_1(A_118)))), inference(resolution, [status(thm)], [c_22, c_657])).
% 4.63/1.87  tff(c_4129, plain, (![B_127]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_127))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_127)) | ~m1_subset_1(B_127, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_3560])).
% 4.63/1.87  tff(c_4140, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_4129])).
% 4.63/1.87  tff(c_4149, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2386, c_4140])).
% 4.63/1.87  tff(c_4151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_4149])).
% 4.63/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.87  
% 4.63/1.87  Inference rules
% 4.63/1.87  ----------------------
% 4.63/1.87  #Ref     : 0
% 4.63/1.87  #Sup     : 1026
% 4.63/1.87  #Fact    : 0
% 4.63/1.87  #Define  : 0
% 4.63/1.87  #Split   : 0
% 4.63/1.87  #Chain   : 0
% 4.63/1.87  #Close   : 0
% 4.63/1.87  
% 4.63/1.87  Ordering : KBO
% 4.63/1.87  
% 4.63/1.87  Simplification rules
% 4.63/1.87  ----------------------
% 4.63/1.87  #Subsume      : 1
% 4.63/1.87  #Demod        : 977
% 4.63/1.87  #Tautology    : 704
% 4.63/1.87  #SimpNegUnit  : 1
% 4.63/1.87  #BackRed      : 7
% 4.63/1.87  
% 4.63/1.87  #Partial instantiations: 0
% 4.63/1.87  #Strategies tried      : 1
% 4.63/1.87  
% 4.63/1.87  Timing (in seconds)
% 4.63/1.87  ----------------------
% 4.63/1.88  Preprocessing        : 0.28
% 4.63/1.88  Parsing              : 0.15
% 4.63/1.88  CNF conversion       : 0.02
% 4.63/1.88  Main loop            : 0.76
% 4.63/1.88  Inferencing          : 0.22
% 4.63/1.88  Reduction            : 0.36
% 4.63/1.88  Demodulation         : 0.31
% 4.63/1.88  BG Simplification    : 0.03
% 4.63/1.88  Subsumption          : 0.10
% 4.63/1.88  Abstraction          : 0.04
% 4.63/1.88  MUC search           : 0.00
% 4.63/1.88  Cooper               : 0.00
% 4.63/1.88  Total                : 1.07
% 4.63/1.88  Index Insertion      : 0.00
% 4.63/1.88  Index Deletion       : 0.00
% 4.63/1.88  Index Matching       : 0.00
% 4.63/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
