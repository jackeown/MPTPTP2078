%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:43 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 100 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :   39 (  80 expanded)
%              Number of equality atoms :   38 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_22,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_28,B_29,C_30,D_31] : k3_enumset1(A_28,A_28,B_29,C_30,D_31) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [B_33,C_34,E_36,A_32,D_35] : k4_enumset1(A_32,A_32,B_33,C_34,D_35,E_36) = k3_enumset1(A_32,B_33,C_34,D_35,E_36) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1531,plain,(
    ! [D_138,F_134,A_137,E_136,B_135,C_139] : k2_xboole_0(k1_tarski(A_137),k3_enumset1(B_135,C_139,D_138,E_136,F_134)) = k4_enumset1(A_137,B_135,C_139,D_138,E_136,F_134) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,(
    ! [A_63,B_64] : k3_tarski(k2_tarski(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_215,plain,(
    ! [A_70,B_71] : k3_tarski(k2_tarski(A_70,B_71)) = k2_xboole_0(B_71,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_138])).

tff(c_255,plain,(
    ! [B_72,A_73] : k2_xboole_0(B_72,A_73) = k2_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_215])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_115,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_6])).

tff(c_123,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_38])).

tff(c_276,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_123])).

tff(c_333,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_8])).

tff(c_336,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_333])).

tff(c_36,plain,(
    ! [A_52,B_53] : k2_xboole_0(k1_tarski(A_52),B_53) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_348,plain,(
    ! [A_52,B_53] : k2_xboole_0(k1_tarski(A_52),B_53) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_36])).

tff(c_1584,plain,(
    ! [C_143,A_145,E_142,B_141,F_144,D_140] : k4_enumset1(A_145,B_141,C_143,D_140,E_142,F_144) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_348])).

tff(c_1587,plain,(
    ! [C_148,D_150,A_149,B_147,E_146] : k3_enumset1(A_149,B_147,C_148,D_150,E_146) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1584])).

tff(c_1590,plain,(
    ! [A_151,B_152,C_153,D_154] : k2_enumset1(A_151,B_152,C_153,D_154) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1587])).

tff(c_1593,plain,(
    ! [A_155,B_156,C_157] : k1_enumset1(A_155,B_156,C_157) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1590])).

tff(c_1595,plain,(
    ! [A_23,B_24] : k2_tarski(A_23,B_24) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1593])).

tff(c_346,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_115])).

tff(c_1597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1595,c_346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:59:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.50  
% 3.02/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.51  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.02/1.51  
% 3.02/1.51  %Foreground sorts:
% 3.02/1.51  
% 3.02/1.51  
% 3.02/1.51  %Background operators:
% 3.02/1.51  
% 3.02/1.51  
% 3.02/1.51  %Foreground operators:
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.02/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.51  
% 3.02/1.52  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.02/1.52  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.02/1.52  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.02/1.52  tff(f_53, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.02/1.52  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 3.02/1.52  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.02/1.52  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.02/1.52  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.02/1.52  tff(f_66, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.02/1.52  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.02/1.52  tff(f_62, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.02/1.52  tff(c_22, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.52  tff(c_24, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.02/1.52  tff(c_26, plain, (![A_28, B_29, C_30, D_31]: (k3_enumset1(A_28, A_28, B_29, C_30, D_31)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.52  tff(c_28, plain, (![B_33, C_34, E_36, A_32, D_35]: (k4_enumset1(A_32, A_32, B_33, C_34, D_35, E_36)=k3_enumset1(A_32, B_33, C_34, D_35, E_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.02/1.52  tff(c_1531, plain, (![D_138, F_134, A_137, E_136, B_135, C_139]: (k2_xboole_0(k1_tarski(A_137), k3_enumset1(B_135, C_139, D_138, E_136, F_134))=k4_enumset1(A_137, B_135, C_139, D_138, E_136, F_134))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.52  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.52  tff(c_34, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.02/1.52  tff(c_16, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.52  tff(c_138, plain, (![A_63, B_64]: (k3_tarski(k2_tarski(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.02/1.52  tff(c_215, plain, (![A_70, B_71]: (k3_tarski(k2_tarski(A_70, B_71))=k2_xboole_0(B_71, A_70))), inference(superposition, [status(thm), theory('equality')], [c_16, c_138])).
% 3.02/1.52  tff(c_255, plain, (![B_72, A_73]: (k2_xboole_0(B_72, A_73)=k2_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_34, c_215])).
% 3.02/1.52  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.02/1.52  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.52  tff(c_75, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_8])).
% 3.02/1.52  tff(c_115, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_75, c_6])).
% 3.02/1.52  tff(c_123, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_115, c_38])).
% 3.02/1.52  tff(c_276, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_255, c_123])).
% 3.02/1.52  tff(c_333, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_276, c_8])).
% 3.02/1.52  tff(c_336, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_333])).
% 3.02/1.52  tff(c_36, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.02/1.52  tff(c_348, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), B_53)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_36])).
% 3.02/1.52  tff(c_1584, plain, (![C_143, A_145, E_142, B_141, F_144, D_140]: (k4_enumset1(A_145, B_141, C_143, D_140, E_142, F_144)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1531, c_348])).
% 3.02/1.52  tff(c_1587, plain, (![C_148, D_150, A_149, B_147, E_146]: (k3_enumset1(A_149, B_147, C_148, D_150, E_146)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1584])).
% 3.02/1.52  tff(c_1590, plain, (![A_151, B_152, C_153, D_154]: (k2_enumset1(A_151, B_152, C_153, D_154)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1587])).
% 3.02/1.52  tff(c_1593, plain, (![A_155, B_156, C_157]: (k1_enumset1(A_155, B_156, C_157)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1590])).
% 3.02/1.52  tff(c_1595, plain, (![A_23, B_24]: (k2_tarski(A_23, B_24)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1593])).
% 3.02/1.52  tff(c_346, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_336, c_115])).
% 3.02/1.52  tff(c_1597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1595, c_346])).
% 3.02/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.52  
% 3.02/1.52  Inference rules
% 3.02/1.52  ----------------------
% 3.02/1.52  #Ref     : 0
% 3.02/1.52  #Sup     : 405
% 3.02/1.52  #Fact    : 0
% 3.02/1.52  #Define  : 0
% 3.02/1.52  #Split   : 0
% 3.02/1.52  #Chain   : 0
% 3.02/1.52  #Close   : 0
% 3.02/1.52  
% 3.02/1.52  Ordering : KBO
% 3.02/1.52  
% 3.02/1.52  Simplification rules
% 3.02/1.52  ----------------------
% 3.02/1.52  #Subsume      : 18
% 3.02/1.52  #Demod        : 278
% 3.02/1.52  #Tautology    : 298
% 3.02/1.52  #SimpNegUnit  : 1
% 3.02/1.52  #BackRed      : 20
% 3.02/1.52  
% 3.02/1.52  #Partial instantiations: 0
% 3.02/1.52  #Strategies tried      : 1
% 3.02/1.52  
% 3.02/1.52  Timing (in seconds)
% 3.02/1.52  ----------------------
% 3.02/1.52  Preprocessing        : 0.31
% 3.02/1.52  Parsing              : 0.17
% 3.02/1.52  CNF conversion       : 0.02
% 3.02/1.52  Main loop            : 0.44
% 3.02/1.52  Inferencing          : 0.15
% 3.02/1.52  Reduction            : 0.18
% 3.02/1.52  Demodulation         : 0.15
% 3.02/1.52  BG Simplification    : 0.02
% 3.02/1.52  Subsumption          : 0.06
% 3.02/1.52  Abstraction          : 0.03
% 3.02/1.52  MUC search           : 0.00
% 3.02/1.52  Cooper               : 0.00
% 3.02/1.52  Total                : 0.78
% 3.02/1.52  Index Insertion      : 0.00
% 3.02/1.52  Index Deletion       : 0.00
% 3.02/1.52  Index Matching       : 0.00
% 3.02/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
