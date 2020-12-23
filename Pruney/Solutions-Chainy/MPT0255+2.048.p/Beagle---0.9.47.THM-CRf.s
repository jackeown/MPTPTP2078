%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:45 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   80 (1155 expanded)
%              Number of leaves         :   27 ( 413 expanded)
%              Depth                    :   17
%              Number of atoms          :   78 (1372 expanded)
%              Number of equality atoms :   55 ( 958 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_166,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    ! [A_49] : k2_xboole_0(k1_xboole_0,A_49) = A_49 ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [A_49] : k2_xboole_0(A_49,k1_xboole_0) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_2])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,A_32) = k2_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_52])).

tff(c_174,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_390,plain,(
    ! [A_69,B_70,C_71] : k4_xboole_0(k4_xboole_0(A_69,B_70),C_71) = k4_xboole_0(A_69,k2_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_679,plain,(
    ! [C_91,A_92,B_93] : k5_xboole_0(C_91,k4_xboole_0(A_92,k2_xboole_0(B_93,C_91))) = k2_xboole_0(C_91,k4_xboole_0(A_92,B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_18])).

tff(c_715,plain,(
    ! [A_7,A_92] : k5_xboole_0(A_7,k4_xboole_0(A_92,A_7)) = k2_xboole_0(A_7,k4_xboole_0(A_92,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_679])).

tff(c_739,plain,(
    ! [A_94,A_95] : k2_xboole_0(A_94,k4_xboole_0(A_95,k1_xboole_0)) = k2_xboole_0(A_94,A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_715])).

tff(c_757,plain,(
    ! [A_95] : k4_xboole_0(A_95,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_174])).

tff(c_804,plain,(
    ! [A_95] : k4_xboole_0(A_95,k1_xboole_0) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_757])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_173,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_166])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_402,plain,(
    ! [A_8,B_9,C_10,C_71] : k4_xboole_0(k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)),C_71) = k4_xboole_0(k4_xboole_0(A_8,B_9),k2_xboole_0(C_10,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_390])).

tff(c_1201,plain,(
    ! [A_111,B_112,C_113,C_114] : k4_xboole_0(A_111,k2_xboole_0(k2_xboole_0(B_112,C_113),C_114)) = k4_xboole_0(A_111,k2_xboole_0(B_112,k2_xboole_0(C_113,C_114))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_402])).

tff(c_1316,plain,(
    ! [A_115,B_116,C_117] : k4_xboole_0(A_115,k2_xboole_0(B_116,k2_xboole_0(B_116,C_117))) = k4_xboole_0(A_115,k2_xboole_0(B_116,C_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_1201])).

tff(c_1410,plain,(
    ! [A_115] : k4_xboole_0(A_115,k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0)) = k4_xboole_0(A_115,k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1316])).

tff(c_1434,plain,(
    ! [A_115] : k4_xboole_0(A_115,k2_tarski('#skF_1','#skF_2')) = A_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_174,c_2,c_34,c_1410])).

tff(c_730,plain,(
    ! [A_92] : k2_xboole_0('#skF_3',k4_xboole_0(A_92,k2_tarski('#skF_1','#skF_2'))) = k5_xboole_0('#skF_3',k4_xboole_0(A_92,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_679])).

tff(c_837,plain,(
    ! [A_92] : k2_xboole_0('#skF_3',k4_xboole_0(A_92,k2_tarski('#skF_1','#skF_2'))) = k5_xboole_0('#skF_3',A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_730])).

tff(c_1466,plain,(
    ! [A_92] : k5_xboole_0('#skF_3',A_92) = k2_xboole_0('#skF_3',A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1434,c_837])).

tff(c_1401,plain,(
    ! [A_115] : k4_xboole_0(A_115,k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) = k4_xboole_0(A_115,k2_xboole_0('#skF_3',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1316])).

tff(c_1433,plain,(
    ! [A_115] : k4_xboole_0(A_115,'#skF_3') = A_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_227,c_93,c_1401])).

tff(c_1497,plain,(
    ! [A_120] : k5_xboole_0('#skF_3',A_120) = k2_xboole_0('#skF_3',A_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1434,c_837])).

tff(c_362,plain,(
    ! [A_66,B_67,C_68] : k5_xboole_0(k5_xboole_0(A_66,B_67),C_68) = k5_xboole_0(A_66,k5_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_381,plain,(
    ! [A_14,B_15,C_68] : k5_xboole_0(A_14,k5_xboole_0(k4_xboole_0(B_15,A_14),C_68)) = k5_xboole_0(k2_xboole_0(A_14,B_15),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_362])).

tff(c_1508,plain,(
    ! [B_15,C_68] : k2_xboole_0('#skF_3',k5_xboole_0(k4_xboole_0(B_15,'#skF_3'),C_68)) = k5_xboole_0(k2_xboole_0('#skF_3',B_15),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_381])).

tff(c_1985,plain,(
    ! [B_132,C_133] : k5_xboole_0(k2_xboole_0('#skF_3',B_132),C_133) = k2_xboole_0('#skF_3',k5_xboole_0(B_132,C_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_1508])).

tff(c_2046,plain,(
    ! [C_133] : k2_xboole_0('#skF_3',k5_xboole_0('#skF_3',C_133)) = k5_xboole_0('#skF_3',C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_1985])).

tff(c_2073,plain,(
    ! [C_134] : k2_xboole_0('#skF_3',k2_xboole_0('#skF_3',C_134)) = k2_xboole_0('#skF_3',C_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1466,c_1466,c_2046])).

tff(c_2132,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2073])).

tff(c_2158,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_93,c_2132])).

tff(c_314,plain,(
    ! [B_53,C_54,A_55] :
      ( r2_hidden(B_53,C_54)
      | ~ r1_tarski(k2_tarski(A_55,B_53),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_322,plain,(
    ! [B_53,A_55] : r2_hidden(B_53,k2_tarski(A_55,B_53)) ),
    inference(resolution,[status(thm)],[c_8,c_314])).

tff(c_20,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_410,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(k2_tarski(A_72,B_73),C_74)
      | ~ r2_hidden(B_73,C_74)
      | ~ r2_hidden(A_72,C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_434,plain,(
    ! [A_75,C_76] :
      ( r1_tarski(k1_tarski(A_75),C_76)
      | ~ r2_hidden(A_75,C_76)
      | ~ r2_hidden(A_75,C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_410])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_454,plain,(
    ! [A_78,C_79] :
      ( k2_xboole_0(k1_tarski(A_78),C_79) = C_79
      | ~ r2_hidden(A_78,C_79) ) ),
    inference(resolution,[status(thm)],[c_434,c_10])).

tff(c_32,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_508,plain,(
    ! [C_80,A_81] :
      ( k1_xboole_0 != C_80
      | ~ r2_hidden(A_81,C_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_32])).

tff(c_518,plain,(
    ! [A_55,B_53] : k2_tarski(A_55,B_53) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_322,c_508])).

tff(c_2306,plain,(
    ! [A_55,B_53] : k2_tarski(A_55,B_53) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_518])).

tff(c_2553,plain,(
    ! [A_145] : k2_xboole_0(A_145,'#skF_3') = A_145 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_227])).

tff(c_2315,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_34])).

tff(c_2563,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2553,c_2315])).

tff(c_2631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2306,c_2563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.68  
% 3.94/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.69  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.94/1.69  
% 3.94/1.69  %Foreground sorts:
% 3.94/1.69  
% 3.94/1.69  
% 3.94/1.69  %Background operators:
% 3.94/1.69  
% 3.94/1.69  
% 3.94/1.69  %Foreground operators:
% 3.94/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.94/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.94/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.94/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.94/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.94/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.94/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.94/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.94/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.94/1.69  
% 3.94/1.70  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.94/1.70  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.94/1.70  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.94/1.70  tff(f_64, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.94/1.70  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.94/1.70  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.94/1.70  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.94/1.70  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.94/1.70  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.94/1.70  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.94/1.70  tff(f_60, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.94/1.70  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.94/1.70  tff(c_166, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.94/1.70  tff(c_213, plain, (![A_49]: (k2_xboole_0(k1_xboole_0, A_49)=A_49)), inference(resolution, [status(thm)], [c_12, c_166])).
% 3.94/1.70  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.94/1.70  tff(c_227, plain, (![A_49]: (k2_xboole_0(A_49, k1_xboole_0)=A_49)), inference(superposition, [status(thm), theory('equality')], [c_213, c_2])).
% 3.94/1.70  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.94/1.70  tff(c_52, plain, (![B_31, A_32]: (k2_xboole_0(B_31, A_32)=k2_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.94/1.70  tff(c_93, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_52])).
% 3.94/1.70  tff(c_174, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(resolution, [status(thm)], [c_12, c_166])).
% 3.94/1.70  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.94/1.70  tff(c_390, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k4_xboole_0(A_69, B_70), C_71)=k4_xboole_0(A_69, k2_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.94/1.70  tff(c_679, plain, (![C_91, A_92, B_93]: (k5_xboole_0(C_91, k4_xboole_0(A_92, k2_xboole_0(B_93, C_91)))=k2_xboole_0(C_91, k4_xboole_0(A_92, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_390, c_18])).
% 3.94/1.70  tff(c_715, plain, (![A_7, A_92]: (k5_xboole_0(A_7, k4_xboole_0(A_92, A_7))=k2_xboole_0(A_7, k4_xboole_0(A_92, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_174, c_679])).
% 3.94/1.70  tff(c_739, plain, (![A_94, A_95]: (k2_xboole_0(A_94, k4_xboole_0(A_95, k1_xboole_0))=k2_xboole_0(A_94, A_95))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_715])).
% 3.94/1.70  tff(c_757, plain, (![A_95]: (k4_xboole_0(A_95, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_95))), inference(superposition, [status(thm), theory('equality')], [c_739, c_174])).
% 3.94/1.70  tff(c_804, plain, (![A_95]: (k4_xboole_0(A_95, k1_xboole_0)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_174, c_757])).
% 3.94/1.70  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.94/1.70  tff(c_173, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_166])).
% 3.94/1.70  tff(c_14, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.94/1.70  tff(c_402, plain, (![A_8, B_9, C_10, C_71]: (k4_xboole_0(k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)), C_71)=k4_xboole_0(k4_xboole_0(A_8, B_9), k2_xboole_0(C_10, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_390])).
% 3.94/1.70  tff(c_1201, plain, (![A_111, B_112, C_113, C_114]: (k4_xboole_0(A_111, k2_xboole_0(k2_xboole_0(B_112, C_113), C_114))=k4_xboole_0(A_111, k2_xboole_0(B_112, k2_xboole_0(C_113, C_114))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_402])).
% 3.94/1.70  tff(c_1316, plain, (![A_115, B_116, C_117]: (k4_xboole_0(A_115, k2_xboole_0(B_116, k2_xboole_0(B_116, C_117)))=k4_xboole_0(A_115, k2_xboole_0(B_116, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_173, c_1201])).
% 3.94/1.70  tff(c_1410, plain, (![A_115]: (k4_xboole_0(A_115, k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0))=k4_xboole_0(A_115, k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1316])).
% 3.94/1.70  tff(c_1434, plain, (![A_115]: (k4_xboole_0(A_115, k2_tarski('#skF_1', '#skF_2'))=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_804, c_174, c_2, c_34, c_1410])).
% 3.94/1.70  tff(c_730, plain, (![A_92]: (k2_xboole_0('#skF_3', k4_xboole_0(A_92, k2_tarski('#skF_1', '#skF_2')))=k5_xboole_0('#skF_3', k4_xboole_0(A_92, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_679])).
% 3.94/1.70  tff(c_837, plain, (![A_92]: (k2_xboole_0('#skF_3', k4_xboole_0(A_92, k2_tarski('#skF_1', '#skF_2')))=k5_xboole_0('#skF_3', A_92))), inference(demodulation, [status(thm), theory('equality')], [c_804, c_730])).
% 3.94/1.70  tff(c_1466, plain, (![A_92]: (k5_xboole_0('#skF_3', A_92)=k2_xboole_0('#skF_3', A_92))), inference(demodulation, [status(thm), theory('equality')], [c_1434, c_837])).
% 3.94/1.70  tff(c_1401, plain, (![A_115]: (k4_xboole_0(A_115, k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))=k4_xboole_0(A_115, k2_xboole_0('#skF_3', k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_1316])).
% 3.94/1.70  tff(c_1433, plain, (![A_115]: (k4_xboole_0(A_115, '#skF_3')=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_804, c_227, c_93, c_1401])).
% 3.94/1.70  tff(c_1497, plain, (![A_120]: (k5_xboole_0('#skF_3', A_120)=k2_xboole_0('#skF_3', A_120))), inference(demodulation, [status(thm), theory('equality')], [c_1434, c_837])).
% 3.94/1.70  tff(c_362, plain, (![A_66, B_67, C_68]: (k5_xboole_0(k5_xboole_0(A_66, B_67), C_68)=k5_xboole_0(A_66, k5_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.94/1.70  tff(c_381, plain, (![A_14, B_15, C_68]: (k5_xboole_0(A_14, k5_xboole_0(k4_xboole_0(B_15, A_14), C_68))=k5_xboole_0(k2_xboole_0(A_14, B_15), C_68))), inference(superposition, [status(thm), theory('equality')], [c_18, c_362])).
% 3.94/1.70  tff(c_1508, plain, (![B_15, C_68]: (k2_xboole_0('#skF_3', k5_xboole_0(k4_xboole_0(B_15, '#skF_3'), C_68))=k5_xboole_0(k2_xboole_0('#skF_3', B_15), C_68))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_381])).
% 3.94/1.70  tff(c_1985, plain, (![B_132, C_133]: (k5_xboole_0(k2_xboole_0('#skF_3', B_132), C_133)=k2_xboole_0('#skF_3', k5_xboole_0(B_132, C_133)))), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_1508])).
% 3.94/1.70  tff(c_2046, plain, (![C_133]: (k2_xboole_0('#skF_3', k5_xboole_0('#skF_3', C_133))=k5_xboole_0('#skF_3', C_133))), inference(superposition, [status(thm), theory('equality')], [c_173, c_1985])).
% 3.94/1.70  tff(c_2073, plain, (![C_134]: (k2_xboole_0('#skF_3', k2_xboole_0('#skF_3', C_134))=k2_xboole_0('#skF_3', C_134))), inference(demodulation, [status(thm), theory('equality')], [c_1466, c_1466, c_2046])).
% 3.94/1.70  tff(c_2132, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_93, c_2073])).
% 3.94/1.70  tff(c_2158, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_93, c_2132])).
% 3.94/1.70  tff(c_314, plain, (![B_53, C_54, A_55]: (r2_hidden(B_53, C_54) | ~r1_tarski(k2_tarski(A_55, B_53), C_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.94/1.70  tff(c_322, plain, (![B_53, A_55]: (r2_hidden(B_53, k2_tarski(A_55, B_53)))), inference(resolution, [status(thm)], [c_8, c_314])).
% 3.94/1.70  tff(c_20, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.94/1.70  tff(c_410, plain, (![A_72, B_73, C_74]: (r1_tarski(k2_tarski(A_72, B_73), C_74) | ~r2_hidden(B_73, C_74) | ~r2_hidden(A_72, C_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.94/1.70  tff(c_434, plain, (![A_75, C_76]: (r1_tarski(k1_tarski(A_75), C_76) | ~r2_hidden(A_75, C_76) | ~r2_hidden(A_75, C_76))), inference(superposition, [status(thm), theory('equality')], [c_20, c_410])).
% 3.94/1.70  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.94/1.70  tff(c_454, plain, (![A_78, C_79]: (k2_xboole_0(k1_tarski(A_78), C_79)=C_79 | ~r2_hidden(A_78, C_79))), inference(resolution, [status(thm)], [c_434, c_10])).
% 3.94/1.70  tff(c_32, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.94/1.70  tff(c_508, plain, (![C_80, A_81]: (k1_xboole_0!=C_80 | ~r2_hidden(A_81, C_80))), inference(superposition, [status(thm), theory('equality')], [c_454, c_32])).
% 3.94/1.70  tff(c_518, plain, (![A_55, B_53]: (k2_tarski(A_55, B_53)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_322, c_508])).
% 3.94/1.70  tff(c_2306, plain, (![A_55, B_53]: (k2_tarski(A_55, B_53)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_518])).
% 3.94/1.70  tff(c_2553, plain, (![A_145]: (k2_xboole_0(A_145, '#skF_3')=A_145)), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_227])).
% 3.94/1.70  tff(c_2315, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_34])).
% 3.94/1.70  tff(c_2563, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2553, c_2315])).
% 3.94/1.70  tff(c_2631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2306, c_2563])).
% 3.94/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.70  
% 3.94/1.70  Inference rules
% 3.94/1.70  ----------------------
% 3.94/1.70  #Ref     : 0
% 3.94/1.70  #Sup     : 607
% 3.94/1.70  #Fact    : 0
% 3.94/1.70  #Define  : 0
% 3.94/1.70  #Split   : 1
% 3.94/1.70  #Chain   : 0
% 3.94/1.70  #Close   : 0
% 3.94/1.70  
% 3.94/1.70  Ordering : KBO
% 3.94/1.70  
% 3.94/1.70  Simplification rules
% 3.94/1.70  ----------------------
% 3.94/1.70  #Subsume      : 67
% 3.94/1.70  #Demod        : 452
% 3.94/1.70  #Tautology    : 273
% 3.94/1.70  #SimpNegUnit  : 15
% 3.94/1.70  #BackRed      : 20
% 3.94/1.70  
% 3.94/1.70  #Partial instantiations: 0
% 3.94/1.70  #Strategies tried      : 1
% 3.94/1.70  
% 3.94/1.70  Timing (in seconds)
% 3.94/1.70  ----------------------
% 3.94/1.71  Preprocessing        : 0.29
% 3.94/1.71  Parsing              : 0.16
% 3.94/1.71  CNF conversion       : 0.02
% 3.94/1.71  Main loop            : 0.63
% 3.94/1.71  Inferencing          : 0.21
% 3.94/1.71  Reduction            : 0.28
% 3.94/1.71  Demodulation         : 0.23
% 3.94/1.71  BG Simplification    : 0.03
% 3.94/1.71  Subsumption          : 0.09
% 3.94/1.71  Abstraction          : 0.04
% 3.94/1.71  MUC search           : 0.00
% 3.94/1.71  Cooper               : 0.00
% 3.94/1.71  Total                : 0.96
% 3.94/1.71  Index Insertion      : 0.00
% 3.94/1.71  Index Deletion       : 0.00
% 3.94/1.71  Index Matching       : 0.00
% 3.94/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
