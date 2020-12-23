%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:55 EST 2020

% Result     : Theorem 15.06s
% Output     : CNFRefutation 15.06s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 143 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 136 expanded)
%              Number of equality atoms :   65 ( 135 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_24,plain,(
    ! [A_24] : k5_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [B_37,A_38] : k5_xboole_0(B_37,A_38) = k5_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [B_37] : k5_xboole_0(k1_xboole_0,B_37) = B_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_24])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_324,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k4_xboole_0(B_46,A_45)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_347,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = k2_xboole_0(k1_xboole_0,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_324])).

tff(c_353,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_347])).

tff(c_1688,plain,(
    ! [A_90,B_91,C_92] : k3_xboole_0(k4_xboole_0(A_90,B_91),k4_xboole_0(A_90,C_92)) = k4_xboole_0(A_90,k2_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1818,plain,(
    ! [A_8,C_92] : k4_xboole_0(A_8,k2_xboole_0(k1_xboole_0,C_92)) = k3_xboole_0(A_8,k4_xboole_0(A_8,C_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1688])).

tff(c_2193,plain,(
    ! [A_101,C_102] : k3_xboole_0(A_101,k4_xboole_0(A_101,C_102)) = k4_xboole_0(A_101,C_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_1818])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_255,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_270,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_255])).

tff(c_273,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_270])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_354,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_363,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,k3_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_18])).

tff(c_383,plain,(
    ! [A_47,B_48] : k3_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_363])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_657,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k3_xboole_0(B_62,A_61)) = k4_xboole_0(A_61,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_354])).

tff(c_680,plain,(
    ! [A_47,B_48] : k4_xboole_0(k3_xboole_0(A_47,B_48),k3_xboole_0(A_47,B_48)) = k4_xboole_0(k3_xboole_0(A_47,B_48),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_657])).

tff(c_709,plain,(
    ! [A_47,B_48] : k4_xboole_0(k3_xboole_0(A_47,B_48),A_47) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_680])).

tff(c_2305,plain,(
    ! [A_103,C_104] : k4_xboole_0(k4_xboole_0(A_103,C_104),A_103) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2193,c_709])).

tff(c_30,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2340,plain,(
    ! [A_103,C_104] : k2_xboole_0(A_103,k4_xboole_0(A_103,C_104)) = k5_xboole_0(A_103,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2305,c_30])).

tff(c_2414,plain,(
    ! [A_103,C_104] : k2_xboole_0(A_103,k4_xboole_0(A_103,C_104)) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2340])).

tff(c_471,plain,(
    ! [A_52,B_53] : k4_xboole_0(k2_xboole_0(A_52,B_53),B_53) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_477,plain,(
    ! [B_53,A_52] : k5_xboole_0(B_53,k4_xboole_0(A_52,B_53)) = k2_xboole_0(B_53,k2_xboole_0(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_30])).

tff(c_499,plain,(
    ! [B_53,A_52] : k2_xboole_0(B_53,k2_xboole_0(A_52,B_53)) = k2_xboole_0(B_53,A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_477])).

tff(c_1803,plain,(
    ! [A_8,B_91] : k4_xboole_0(A_8,k2_xboole_0(B_91,A_8)) = k3_xboole_0(k4_xboole_0(A_8,B_91),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_1688])).

tff(c_1851,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k2_xboole_0(B_94,A_93)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1803])).

tff(c_1907,plain,(
    ! [A_52,B_53] : k4_xboole_0(k2_xboole_0(A_52,B_53),k2_xboole_0(B_53,A_52)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_1851])).

tff(c_8788,plain,(
    ! [A_187,B_188] : k4_xboole_0(k2_xboole_0(A_187,B_188),k2_xboole_0(B_188,A_187)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_1851])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | k4_xboole_0(B_7,A_6) != k4_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8868,plain,(
    ! [B_188,A_187] :
      ( k2_xboole_0(B_188,A_187) = k2_xboole_0(A_187,B_188)
      | k4_xboole_0(k2_xboole_0(B_188,A_187),k2_xboole_0(A_187,B_188)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8788,c_8])).

tff(c_8965,plain,(
    ! [B_188,A_187] : k2_xboole_0(B_188,A_187) = k2_xboole_0(A_187,B_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_8868])).

tff(c_340,plain,(
    ! [A_16,B_17] : k5_xboole_0(k4_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(k4_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_324])).

tff(c_25772,plain,(
    ! [A_321,B_322] : k5_xboole_0(k4_xboole_0(A_321,B_322),k3_xboole_0(A_321,B_322)) = A_321 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2414,c_8965,c_340])).

tff(c_28,plain,(
    ! [A_28] : k5_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_821,plain,(
    ! [A_67,B_68,C_69] : k5_xboole_0(k5_xboole_0(A_67,B_68),C_69) = k5_xboole_0(A_67,k5_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_885,plain,(
    ! [A_28,C_69] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_69)) = k5_xboole_0(k1_xboole_0,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_821])).

tff(c_898,plain,(
    ! [A_28,C_69] : k5_xboole_0(A_28,k5_xboole_0(A_28,C_69)) = C_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_885])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_899,plain,(
    ! [A_70,C_71] : k5_xboole_0(A_70,k5_xboole_0(A_70,C_71)) = C_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_885])).

tff(c_964,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k5_xboole_0(B_73,A_72)) = B_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_899])).

tff(c_997,plain,(
    ! [A_28,C_69] : k5_xboole_0(k5_xboole_0(A_28,C_69),C_69) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_964])).

tff(c_25805,plain,(
    ! [A_321,B_322] : k5_xboole_0(A_321,k3_xboole_0(A_321,B_322)) = k4_xboole_0(A_321,B_322) ),
    inference(superposition,[status(thm),theory(equality)],[c_25772,c_997])).

tff(c_32,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25805,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.06/7.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.06/7.82  
% 15.06/7.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.06/7.82  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 15.06/7.82  
% 15.06/7.82  %Foreground sorts:
% 15.06/7.82  
% 15.06/7.82  
% 15.06/7.82  %Background operators:
% 15.06/7.82  
% 15.06/7.82  
% 15.06/7.82  %Foreground operators:
% 15.06/7.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.06/7.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.06/7.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.06/7.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.06/7.82  tff('#skF_2', type, '#skF_2': $i).
% 15.06/7.82  tff('#skF_1', type, '#skF_1': $i).
% 15.06/7.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.06/7.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.06/7.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.06/7.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.06/7.82  
% 15.06/7.83  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 15.06/7.83  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 15.06/7.83  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 15.06/7.83  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 15.06/7.83  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 15.06/7.83  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 15.06/7.83  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.06/7.83  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 15.06/7.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.06/7.83  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 15.06/7.83  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 15.06/7.83  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 15.06/7.83  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 15.06/7.83  tff(f_60, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.06/7.83  tff(c_24, plain, (![A_24]: (k5_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.06/7.83  tff(c_122, plain, (![B_37, A_38]: (k5_xboole_0(B_37, A_38)=k5_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.06/7.83  tff(c_142, plain, (![B_37]: (k5_xboole_0(k1_xboole_0, B_37)=B_37)), inference(superposition, [status(thm), theory('equality')], [c_122, c_24])).
% 15.06/7.83  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.06/7.83  tff(c_324, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k4_xboole_0(B_46, A_45))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.06/7.83  tff(c_347, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=k2_xboole_0(k1_xboole_0, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_324])).
% 15.06/7.83  tff(c_353, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_347])).
% 15.06/7.83  tff(c_1688, plain, (![A_90, B_91, C_92]: (k3_xboole_0(k4_xboole_0(A_90, B_91), k4_xboole_0(A_90, C_92))=k4_xboole_0(A_90, k2_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.06/7.83  tff(c_1818, plain, (![A_8, C_92]: (k4_xboole_0(A_8, k2_xboole_0(k1_xboole_0, C_92))=k3_xboole_0(A_8, k4_xboole_0(A_8, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1688])).
% 15.06/7.83  tff(c_2193, plain, (![A_101, C_102]: (k3_xboole_0(A_101, k4_xboole_0(A_101, C_102))=k4_xboole_0(A_101, C_102))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_1818])).
% 15.06/7.83  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.06/7.83  tff(c_255, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.06/7.83  tff(c_270, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_255])).
% 15.06/7.83  tff(c_273, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_270])).
% 15.06/7.83  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.06/7.83  tff(c_354, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.06/7.83  tff(c_363, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, k3_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_354, c_18])).
% 15.06/7.83  tff(c_383, plain, (![A_47, B_48]: (k3_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_363])).
% 15.06/7.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.06/7.83  tff(c_657, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k3_xboole_0(B_62, A_61))=k4_xboole_0(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_354])).
% 15.06/7.83  tff(c_680, plain, (![A_47, B_48]: (k4_xboole_0(k3_xboole_0(A_47, B_48), k3_xboole_0(A_47, B_48))=k4_xboole_0(k3_xboole_0(A_47, B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_383, c_657])).
% 15.06/7.83  tff(c_709, plain, (![A_47, B_48]: (k4_xboole_0(k3_xboole_0(A_47, B_48), A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_680])).
% 15.06/7.83  tff(c_2305, plain, (![A_103, C_104]: (k4_xboole_0(k4_xboole_0(A_103, C_104), A_103)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2193, c_709])).
% 15.06/7.83  tff(c_30, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.06/7.83  tff(c_2340, plain, (![A_103, C_104]: (k2_xboole_0(A_103, k4_xboole_0(A_103, C_104))=k5_xboole_0(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2305, c_30])).
% 15.06/7.83  tff(c_2414, plain, (![A_103, C_104]: (k2_xboole_0(A_103, k4_xboole_0(A_103, C_104))=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2340])).
% 15.06/7.83  tff(c_471, plain, (![A_52, B_53]: (k4_xboole_0(k2_xboole_0(A_52, B_53), B_53)=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.06/7.83  tff(c_477, plain, (![B_53, A_52]: (k5_xboole_0(B_53, k4_xboole_0(A_52, B_53))=k2_xboole_0(B_53, k2_xboole_0(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_471, c_30])).
% 15.06/7.83  tff(c_499, plain, (![B_53, A_52]: (k2_xboole_0(B_53, k2_xboole_0(A_52, B_53))=k2_xboole_0(B_53, A_52))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_477])).
% 15.06/7.83  tff(c_1803, plain, (![A_8, B_91]: (k4_xboole_0(A_8, k2_xboole_0(B_91, A_8))=k3_xboole_0(k4_xboole_0(A_8, B_91), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_273, c_1688])).
% 15.06/7.83  tff(c_1851, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k2_xboole_0(B_94, A_93))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1803])).
% 15.06/7.83  tff(c_1907, plain, (![A_52, B_53]: (k4_xboole_0(k2_xboole_0(A_52, B_53), k2_xboole_0(B_53, A_52))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_499, c_1851])).
% 15.06/7.83  tff(c_8788, plain, (![A_187, B_188]: (k4_xboole_0(k2_xboole_0(A_187, B_188), k2_xboole_0(B_188, A_187))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_499, c_1851])).
% 15.06/7.83  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | k4_xboole_0(B_7, A_6)!=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.06/7.83  tff(c_8868, plain, (![B_188, A_187]: (k2_xboole_0(B_188, A_187)=k2_xboole_0(A_187, B_188) | k4_xboole_0(k2_xboole_0(B_188, A_187), k2_xboole_0(A_187, B_188))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8788, c_8])).
% 15.06/7.83  tff(c_8965, plain, (![B_188, A_187]: (k2_xboole_0(B_188, A_187)=k2_xboole_0(A_187, B_188))), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_8868])).
% 15.06/7.84  tff(c_340, plain, (![A_16, B_17]: (k5_xboole_0(k4_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(k4_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_18, c_324])).
% 15.06/7.84  tff(c_25772, plain, (![A_321, B_322]: (k5_xboole_0(k4_xboole_0(A_321, B_322), k3_xboole_0(A_321, B_322))=A_321)), inference(demodulation, [status(thm), theory('equality')], [c_2414, c_8965, c_340])).
% 15.06/7.84  tff(c_28, plain, (![A_28]: (k5_xboole_0(A_28, A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.06/7.84  tff(c_821, plain, (![A_67, B_68, C_69]: (k5_xboole_0(k5_xboole_0(A_67, B_68), C_69)=k5_xboole_0(A_67, k5_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.06/7.84  tff(c_885, plain, (![A_28, C_69]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_69))=k5_xboole_0(k1_xboole_0, C_69))), inference(superposition, [status(thm), theory('equality')], [c_28, c_821])).
% 15.06/7.84  tff(c_898, plain, (![A_28, C_69]: (k5_xboole_0(A_28, k5_xboole_0(A_28, C_69))=C_69)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_885])).
% 15.06/7.84  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.06/7.84  tff(c_899, plain, (![A_70, C_71]: (k5_xboole_0(A_70, k5_xboole_0(A_70, C_71))=C_71)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_885])).
% 15.06/7.84  tff(c_964, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k5_xboole_0(B_73, A_72))=B_73)), inference(superposition, [status(thm), theory('equality')], [c_4, c_899])).
% 15.06/7.84  tff(c_997, plain, (![A_28, C_69]: (k5_xboole_0(k5_xboole_0(A_28, C_69), C_69)=A_28)), inference(superposition, [status(thm), theory('equality')], [c_898, c_964])).
% 15.06/7.84  tff(c_25805, plain, (![A_321, B_322]: (k5_xboole_0(A_321, k3_xboole_0(A_321, B_322))=k4_xboole_0(A_321, B_322))), inference(superposition, [status(thm), theory('equality')], [c_25772, c_997])).
% 15.06/7.84  tff(c_32, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.06/7.84  tff(c_54188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25805, c_32])).
% 15.06/7.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.06/7.84  
% 15.06/7.84  Inference rules
% 15.06/7.84  ----------------------
% 15.06/7.84  #Ref     : 2
% 15.06/7.84  #Sup     : 13772
% 15.06/7.84  #Fact    : 0
% 15.06/7.84  #Define  : 0
% 15.06/7.84  #Split   : 2
% 15.06/7.84  #Chain   : 0
% 15.06/7.84  #Close   : 0
% 15.06/7.84  
% 15.06/7.84  Ordering : KBO
% 15.06/7.84  
% 15.06/7.84  Simplification rules
% 15.06/7.84  ----------------------
% 15.06/7.84  #Subsume      : 776
% 15.06/7.84  #Demod        : 14706
% 15.06/7.84  #Tautology    : 8055
% 15.06/7.84  #SimpNegUnit  : 0
% 15.06/7.84  #BackRed      : 6
% 15.06/7.84  
% 15.06/7.84  #Partial instantiations: 0
% 15.06/7.84  #Strategies tried      : 1
% 15.06/7.84  
% 15.06/7.84  Timing (in seconds)
% 15.06/7.84  ----------------------
% 15.06/7.84  Preprocessing        : 0.28
% 15.06/7.84  Parsing              : 0.15
% 15.06/7.84  CNF conversion       : 0.02
% 15.06/7.84  Main loop            : 6.77
% 15.06/7.84  Inferencing          : 1.03
% 15.06/7.84  Reduction            : 4.34
% 15.06/7.84  Demodulation         : 4.00
% 15.06/7.84  BG Simplification    : 0.14
% 15.06/7.84  Subsumption          : 1.00
% 15.06/7.84  Abstraction          : 0.25
% 15.06/7.84  MUC search           : 0.00
% 15.06/7.84  Cooper               : 0.00
% 15.06/7.84  Total                : 7.09
% 15.06/7.84  Index Insertion      : 0.00
% 15.06/7.84  Index Deletion       : 0.00
% 15.06/7.84  Index Matching       : 0.00
% 15.06/7.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
