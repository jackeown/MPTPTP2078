%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:59 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 109 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 101 expanded)
%              Number of equality atoms :   56 (  83 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_44,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_455,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = A_82
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_477,plain,(
    ! [A_9,B_10] : k3_xboole_0(k3_xboole_0(A_9,B_10),A_9) = k3_xboole_0(A_9,B_10) ),
    inference(resolution,[status(thm)],[c_12,c_455])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_822,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1946,plain,(
    ! [B_132,A_133] : k5_xboole_0(B_132,k3_xboole_0(A_133,B_132)) = k4_xboole_0(B_132,A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_822])).

tff(c_1966,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_1946])).

tff(c_4692,plain,(
    ! [A_190,B_191] : k4_xboole_0(A_190,k3_xboole_0(A_190,B_191)) = k4_xboole_0(A_190,B_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1966])).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_207,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    ! [A_63,B_64] : k3_xboole_0(k4_xboole_0(A_63,B_64),B_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_207])).

tff(c_239,plain,(
    ! [B_64,A_63] : k3_xboole_0(B_64,k4_xboole_0(A_63,B_64)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_2])).

tff(c_34,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1116,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k3_xboole_0(A_108,B_109)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1137,plain,(
    ! [A_29,B_30] : k5_xboole_0(k2_xboole_0(A_29,B_30),k3_xboole_0(A_29,k4_xboole_0(B_30,A_29))) = k2_xboole_0(A_29,k4_xboole_0(B_30,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1116])).

tff(c_1171,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_239,c_1137])).

tff(c_4698,plain,(
    ! [A_190,B_191] : k2_xboole_0(k3_xboole_0(A_190,B_191),k4_xboole_0(A_190,B_191)) = k2_xboole_0(k3_xboole_0(A_190,B_191),A_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_4692,c_1171])).

tff(c_4793,plain,(
    ! [A_190,B_191] : k2_xboole_0(k3_xboole_0(A_190,B_191),A_190) = A_190 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4698])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1381,plain,(
    ! [A_115,B_116,C_117] : k2_xboole_0(k3_xboole_0(A_115,B_116),k3_xboole_0(A_115,C_117)) = k3_xboole_0(A_115,k2_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3685,plain,(
    ! [A_175,B_176] : k3_xboole_0(A_175,k2_xboole_0(B_176,A_175)) = k2_xboole_0(k3_xboole_0(A_175,B_176),A_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1381])).

tff(c_3837,plain,(
    k2_xboole_0(k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')),k1_tarski('#skF_2')) = k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3685])).

tff(c_3860,plain,(
    k2_xboole_0(k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')),k1_tarski('#skF_2')) = k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_3837])).

tff(c_1460,plain,(
    ! [A_5,B_116] : k3_xboole_0(A_5,k2_xboole_0(B_116,A_5)) = k2_xboole_0(k3_xboole_0(A_5,B_116),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1381])).

tff(c_3989,plain,(
    k2_xboole_0(k3_xboole_0(k1_tarski('#skF_2'),k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))),k1_tarski('#skF_2')) = k3_xboole_0(k1_tarski('#skF_2'),k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3860,c_1460])).

tff(c_4935,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4793,c_3989])).

tff(c_600,plain,(
    ! [A_86,B_87] : k2_xboole_0(k3_xboole_0(A_86,B_87),k4_xboole_0(A_86,B_87)) = A_86 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_646,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_600])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_987,plain,(
    ! [A_104,B_105] : k4_xboole_0(k3_xboole_0(A_104,B_105),A_104) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_20])).

tff(c_996,plain,(
    ! [A_104,B_105] : k2_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = k5_xboole_0(A_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_34])).

tff(c_1041,plain,(
    ! [A_104,B_105] : k2_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_996])).

tff(c_14,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1439,plain,(
    ! [A_11,B_12,C_117] : k3_xboole_0(A_11,k2_xboole_0(k2_xboole_0(A_11,B_12),C_117)) = k2_xboole_0(A_11,k3_xboole_0(A_11,C_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1381])).

tff(c_2744,plain,(
    ! [A_148,B_149,C_150] : k3_xboole_0(A_148,k2_xboole_0(k2_xboole_0(A_148,B_149),C_150)) = A_148 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_1439])).

tff(c_100,plain,(
    ! [B_51,A_52] : k3_xboole_0(B_51,A_52) = k3_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    ! [B_51,A_52] : r1_tarski(k3_xboole_0(B_51,A_52),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_12])).

tff(c_3068,plain,(
    ! [A_154,B_155,C_156] : r1_tarski(A_154,k2_xboole_0(k2_xboole_0(A_154,B_155),C_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2744,c_115])).

tff(c_3135,plain,(
    ! [B_157,A_158,C_159] : r1_tarski(k3_xboole_0(B_157,A_158),k2_xboole_0(A_158,C_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_3068])).

tff(c_3177,plain,(
    ! [B_157,A_20,B_21] : r1_tarski(k3_xboole_0(B_157,k3_xboole_0(A_20,B_21)),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3135])).

tff(c_4972,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4935,c_3177])).

tff(c_42,plain,(
    ! [B_38,A_37] :
      ( B_38 = A_37
      | ~ r1_tarski(k1_tarski(A_37),k1_tarski(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5074,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4972,c_42])).

tff(c_5079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_5074])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:15:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.75  
% 5.89/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.75  %$ r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.89/2.75  
% 5.89/2.75  %Foreground sorts:
% 5.89/2.75  
% 5.89/2.75  
% 5.89/2.75  %Background operators:
% 5.89/2.75  
% 5.89/2.75  
% 5.89/2.75  %Foreground operators:
% 5.89/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.89/2.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.89/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.89/2.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.89/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.89/2.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.89/2.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.89/2.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.89/2.75  tff('#skF_2', type, '#skF_2': $i).
% 5.89/2.75  tff('#skF_1', type, '#skF_1': $i).
% 5.89/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.89/2.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.89/2.75  
% 5.89/2.77  tff(f_76, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 5.89/2.77  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.89/2.77  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.89/2.77  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.89/2.77  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.89/2.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.89/2.77  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.89/2.77  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.89/2.77  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.89/2.77  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.89/2.77  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.89/2.77  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.89/2.77  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 5.89/2.77  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.89/2.77  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.89/2.77  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 5.89/2.77  tff(c_44, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.89/2.77  tff(c_22, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.89/2.77  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.89/2.77  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.89/2.77  tff(c_455, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=A_82 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.89/2.77  tff(c_477, plain, (![A_9, B_10]: (k3_xboole_0(k3_xboole_0(A_9, B_10), A_9)=k3_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_455])).
% 5.89/2.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.89/2.77  tff(c_822, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.89/2.77  tff(c_1946, plain, (![B_132, A_133]: (k5_xboole_0(B_132, k3_xboole_0(A_133, B_132))=k4_xboole_0(B_132, A_133))), inference(superposition, [status(thm), theory('equality')], [c_2, c_822])).
% 5.89/2.77  tff(c_1966, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_477, c_1946])).
% 5.89/2.77  tff(c_4692, plain, (![A_190, B_191]: (k4_xboole_0(A_190, k3_xboole_0(A_190, B_191))=k4_xboole_0(A_190, B_191))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1966])).
% 5.89/2.77  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.89/2.77  tff(c_26, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.89/2.77  tff(c_207, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.89/2.77  tff(c_231, plain, (![A_63, B_64]: (k3_xboole_0(k4_xboole_0(A_63, B_64), B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_207])).
% 5.89/2.77  tff(c_239, plain, (![B_64, A_63]: (k3_xboole_0(B_64, k4_xboole_0(A_63, B_64))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_2])).
% 5.89/2.77  tff(c_34, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.89/2.77  tff(c_1116, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k3_xboole_0(A_108, B_109))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.89/2.77  tff(c_1137, plain, (![A_29, B_30]: (k5_xboole_0(k2_xboole_0(A_29, B_30), k3_xboole_0(A_29, k4_xboole_0(B_30, A_29)))=k2_xboole_0(A_29, k4_xboole_0(B_30, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1116])).
% 5.89/2.77  tff(c_1171, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_239, c_1137])).
% 5.89/2.77  tff(c_4698, plain, (![A_190, B_191]: (k2_xboole_0(k3_xboole_0(A_190, B_191), k4_xboole_0(A_190, B_191))=k2_xboole_0(k3_xboole_0(A_190, B_191), A_190))), inference(superposition, [status(thm), theory('equality')], [c_4692, c_1171])).
% 5.89/2.77  tff(c_4793, plain, (![A_190, B_191]: (k2_xboole_0(k3_xboole_0(A_190, B_191), A_190)=A_190)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4698])).
% 5.89/2.77  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.89/2.77  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.89/2.77  tff(c_1381, plain, (![A_115, B_116, C_117]: (k2_xboole_0(k3_xboole_0(A_115, B_116), k3_xboole_0(A_115, C_117))=k3_xboole_0(A_115, k2_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.89/2.77  tff(c_3685, plain, (![A_175, B_176]: (k3_xboole_0(A_175, k2_xboole_0(B_176, A_175))=k2_xboole_0(k3_xboole_0(A_175, B_176), A_175))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1381])).
% 5.89/2.77  tff(c_3837, plain, (k2_xboole_0(k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1')), k1_tarski('#skF_2'))=k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3685])).
% 5.89/2.77  tff(c_3860, plain, (k2_xboole_0(k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')), k1_tarski('#skF_2'))=k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_3837])).
% 5.89/2.77  tff(c_1460, plain, (![A_5, B_116]: (k3_xboole_0(A_5, k2_xboole_0(B_116, A_5))=k2_xboole_0(k3_xboole_0(A_5, B_116), A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1381])).
% 5.89/2.77  tff(c_3989, plain, (k2_xboole_0(k3_xboole_0(k1_tarski('#skF_2'), k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), k1_tarski('#skF_2'))=k3_xboole_0(k1_tarski('#skF_2'), k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3860, c_1460])).
% 5.89/2.77  tff(c_4935, plain, (k3_xboole_0(k1_tarski('#skF_2'), k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4793, c_3989])).
% 5.89/2.77  tff(c_600, plain, (![A_86, B_87]: (k2_xboole_0(k3_xboole_0(A_86, B_87), k4_xboole_0(A_86, B_87))=A_86)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.89/2.77  tff(c_646, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_600])).
% 5.89/2.77  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.89/2.77  tff(c_987, plain, (![A_104, B_105]: (k4_xboole_0(k3_xboole_0(A_104, B_105), A_104)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_600, c_20])).
% 5.89/2.77  tff(c_996, plain, (![A_104, B_105]: (k2_xboole_0(A_104, k3_xboole_0(A_104, B_105))=k5_xboole_0(A_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_987, c_34])).
% 5.89/2.77  tff(c_1041, plain, (![A_104, B_105]: (k2_xboole_0(A_104, k3_xboole_0(A_104, B_105))=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_996])).
% 5.89/2.77  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.89/2.77  tff(c_1439, plain, (![A_11, B_12, C_117]: (k3_xboole_0(A_11, k2_xboole_0(k2_xboole_0(A_11, B_12), C_117))=k2_xboole_0(A_11, k3_xboole_0(A_11, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1381])).
% 5.89/2.78  tff(c_2744, plain, (![A_148, B_149, C_150]: (k3_xboole_0(A_148, k2_xboole_0(k2_xboole_0(A_148, B_149), C_150))=A_148)), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_1439])).
% 5.89/2.78  tff(c_100, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=k3_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.89/2.78  tff(c_115, plain, (![B_51, A_52]: (r1_tarski(k3_xboole_0(B_51, A_52), A_52))), inference(superposition, [status(thm), theory('equality')], [c_100, c_12])).
% 5.89/2.78  tff(c_3068, plain, (![A_154, B_155, C_156]: (r1_tarski(A_154, k2_xboole_0(k2_xboole_0(A_154, B_155), C_156)))), inference(superposition, [status(thm), theory('equality')], [c_2744, c_115])).
% 5.89/2.78  tff(c_3135, plain, (![B_157, A_158, C_159]: (r1_tarski(k3_xboole_0(B_157, A_158), k2_xboole_0(A_158, C_159)))), inference(superposition, [status(thm), theory('equality')], [c_646, c_3068])).
% 5.89/2.78  tff(c_3177, plain, (![B_157, A_20, B_21]: (r1_tarski(k3_xboole_0(B_157, k3_xboole_0(A_20, B_21)), A_20))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3135])).
% 5.89/2.78  tff(c_4972, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4935, c_3177])).
% 5.89/2.78  tff(c_42, plain, (![B_38, A_37]: (B_38=A_37 | ~r1_tarski(k1_tarski(A_37), k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.89/2.78  tff(c_5074, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_4972, c_42])).
% 5.89/2.78  tff(c_5079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_5074])).
% 5.89/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.78  
% 5.89/2.78  Inference rules
% 5.89/2.78  ----------------------
% 5.89/2.78  #Ref     : 0
% 5.89/2.78  #Sup     : 1256
% 5.89/2.78  #Fact    : 0
% 5.89/2.78  #Define  : 0
% 5.89/2.78  #Split   : 0
% 5.89/2.78  #Chain   : 0
% 5.89/2.78  #Close   : 0
% 5.89/2.78  
% 5.89/2.78  Ordering : KBO
% 5.89/2.78  
% 5.89/2.78  Simplification rules
% 5.89/2.78  ----------------------
% 5.89/2.78  #Subsume      : 12
% 5.89/2.78  #Demod        : 1183
% 5.89/2.78  #Tautology    : 903
% 5.89/2.78  #SimpNegUnit  : 1
% 5.89/2.78  #BackRed      : 3
% 5.89/2.78  
% 5.89/2.78  #Partial instantiations: 0
% 5.89/2.78  #Strategies tried      : 1
% 5.89/2.78  
% 5.89/2.78  Timing (in seconds)
% 5.89/2.78  ----------------------
% 5.89/2.78  Preprocessing        : 0.48
% 5.89/2.78  Parsing              : 0.25
% 5.89/2.78  CNF conversion       : 0.03
% 5.89/2.78  Main loop            : 1.33
% 5.89/2.78  Inferencing          : 0.42
% 5.89/2.78  Reduction            : 0.61
% 5.89/2.78  Demodulation         : 0.51
% 5.89/2.78  BG Simplification    : 0.05
% 5.89/2.78  Subsumption          : 0.17
% 5.89/2.78  Abstraction          : 0.07
% 5.89/2.78  MUC search           : 0.00
% 5.89/2.78  Cooper               : 0.00
% 5.89/2.78  Total                : 1.86
% 5.89/2.78  Index Insertion      : 0.00
% 5.89/2.78  Index Deletion       : 0.00
% 5.89/2.78  Index Matching       : 0.00
% 5.89/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
