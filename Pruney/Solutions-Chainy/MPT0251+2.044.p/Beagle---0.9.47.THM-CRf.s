%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:52 EST 2020

% Result     : Theorem 12.06s
% Output     : CNFRefutation 12.16s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 175 expanded)
%              Number of leaves         :   39 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 265 expanded)
%              Number of equality atoms :   46 (  93 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_81,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_77,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_99,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_78,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [A_29] : r1_xboole_0(A_29,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    ! [A_26] : r1_tarski(k1_xboole_0,A_26) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_206,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_213,plain,(
    ! [A_26] : k3_xboole_0(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_206])).

tff(c_1301,plain,(
    ! [A_166,B_167,C_168] :
      ( r2_hidden('#skF_1'(A_166,B_167,C_168),A_166)
      | r2_hidden('#skF_2'(A_166,B_167,C_168),C_168)
      | k3_xboole_0(A_166,B_167) = C_168 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_120,plain,(
    ! [B_54,A_55] :
      ( r1_xboole_0(B_54,A_55)
      | ~ r1_xboole_0(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_123,plain,(
    ! [A_29] : r1_xboole_0(k1_xboole_0,A_29) ),
    inference(resolution,[status(thm)],[c_56,c_120])).

tff(c_406,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | ~ r2_hidden(C_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_412,plain,(
    ! [A_26,C_83] :
      ( ~ r1_xboole_0(k1_xboole_0,A_26)
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_406])).

tff(c_414,plain,(
    ! [C_83] : ~ r2_hidden(C_83,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_412])).

tff(c_1332,plain,(
    ! [B_167,C_168] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_167,C_168),C_168)
      | k3_xboole_0(k1_xboole_0,B_167) = C_168 ) ),
    inference(resolution,[status(thm)],[c_1301,c_414])).

tff(c_1388,plain,(
    ! [B_169,C_170] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_169,C_170),C_170)
      | k1_xboole_0 = C_170 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_1332])).

tff(c_38,plain,(
    ! [A_14,B_15,C_18] :
      ( ~ r1_xboole_0(A_14,B_15)
      | ~ r2_hidden(C_18,k3_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1434,plain,(
    ! [A_171,B_172] :
      ( ~ r1_xboole_0(A_171,B_172)
      | k3_xboole_0(A_171,B_172) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1388,c_38])).

tff(c_1451,plain,(
    ! [A_29] : k3_xboole_0(A_29,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_1434])).

tff(c_1530,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden('#skF_1'(A_174,B_175,C_176),B_175)
      | r2_hidden('#skF_2'(A_174,B_175,C_176),C_176)
      | k3_xboole_0(A_174,B_175) = C_176 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1561,plain,(
    ! [A_174,C_176] :
      ( r2_hidden('#skF_2'(A_174,k1_xboole_0,C_176),C_176)
      | k3_xboole_0(A_174,k1_xboole_0) = C_176 ) ),
    inference(resolution,[status(thm)],[c_1530,c_414])).

tff(c_1607,plain,(
    ! [A_174,C_176] :
      ( r2_hidden('#skF_2'(A_174,k1_xboole_0,C_176),C_176)
      | k1_xboole_0 = C_176 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1561])).

tff(c_618,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_3'(A_106,B_107),k3_xboole_0(A_106,B_107))
      | r1_xboole_0(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_634,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_3'(A_106,B_107),B_107)
      | r1_xboole_0(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_618,c_4])).

tff(c_44,plain,(
    ! [B_20] : r1_tarski(B_20,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_214,plain,(
    ! [B_20] : k3_xboole_0(B_20,B_20) = B_20 ),
    inference(resolution,[status(thm)],[c_44,c_206])).

tff(c_434,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_443,plain,(
    ! [B_20] : k5_xboole_0(B_20,B_20) = k4_xboole_0(B_20,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_434])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_684,plain,(
    ! [A_112,B_113] : k5_xboole_0(k5_xboole_0(A_112,B_113),k3_xboole_0(A_112,B_113)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_708,plain,(
    ! [B_20] : k5_xboole_0(k5_xboole_0(B_20,B_20),B_20) = k2_xboole_0(B_20,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_684])).

tff(c_718,plain,(
    ! [B_20] : k5_xboole_0(k4_xboole_0(B_20,B_20),B_20) = B_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_20,c_708])).

tff(c_1183,plain,(
    ! [A_156,C_157,B_158] :
      ( r2_hidden(A_156,C_157)
      | ~ r2_hidden(A_156,B_158)
      | r2_hidden(A_156,k5_xboole_0(B_158,C_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2671,plain,(
    ! [A_231,B_232] :
      ( r2_hidden(A_231,B_232)
      | ~ r2_hidden(A_231,k4_xboole_0(B_232,B_232))
      | r2_hidden(A_231,B_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_1183])).

tff(c_2733,plain,(
    ! [A_106,B_232] :
      ( r2_hidden('#skF_3'(A_106,k4_xboole_0(B_232,B_232)),B_232)
      | r1_xboole_0(A_106,k4_xboole_0(B_232,B_232)) ) ),
    inference(resolution,[status(thm)],[c_634,c_2671])).

tff(c_1025,plain,(
    ! [A_139,C_140,B_141] :
      ( ~ r2_hidden(A_139,C_140)
      | ~ r2_hidden(A_139,B_141)
      | ~ r2_hidden(A_139,k5_xboole_0(B_141,C_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1282,plain,(
    ! [A_164,B_165] :
      ( ~ r2_hidden(A_164,B_165)
      | ~ r2_hidden(A_164,k4_xboole_0(B_165,B_165))
      | ~ r2_hidden(A_164,B_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_1025])).

tff(c_26631,plain,(
    ! [A_652,B_653] :
      ( ~ r2_hidden('#skF_3'(A_652,k4_xboole_0(B_653,B_653)),B_653)
      | r1_xboole_0(A_652,k4_xboole_0(B_653,B_653)) ) ),
    inference(resolution,[status(thm)],[c_634,c_1282])).

tff(c_26844,plain,(
    ! [A_658,B_659] : r1_xboole_0(A_658,k4_xboole_0(B_659,B_659)) ),
    inference(resolution,[status(thm)],[c_2733,c_26631])).

tff(c_409,plain,(
    ! [B_20,C_83] :
      ( ~ r1_xboole_0(B_20,B_20)
      | ~ r2_hidden(C_83,B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_406])).

tff(c_27287,plain,(
    ! [C_662,B_663] : ~ r2_hidden(C_662,k4_xboole_0(B_663,B_663)) ),
    inference(resolution,[status(thm)],[c_26844,c_409])).

tff(c_27584,plain,(
    ! [B_663] : k4_xboole_0(B_663,B_663) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1607,c_27287])).

tff(c_241,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k1_tarski(A_71),B_72)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_958,plain,(
    ! [A_135,B_136] :
      ( k3_xboole_0(k1_tarski(A_135),B_136) = k1_tarski(A_135)
      | ~ r2_hidden(A_135,B_136) ) ),
    inference(resolution,[status(thm)],[c_241,c_50])).

tff(c_46,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_979,plain,(
    ! [A_135,B_136] :
      ( k5_xboole_0(k1_tarski(A_135),k1_tarski(A_135)) = k4_xboole_0(k1_tarski(A_135),B_136)
      | ~ r2_hidden(A_135,B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_46])).

tff(c_998,plain,(
    ! [A_135,B_136] :
      ( k4_xboole_0(k1_tarski(A_135),k1_tarski(A_135)) = k4_xboole_0(k1_tarski(A_135),B_136)
      | ~ r2_hidden(A_135,B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_979])).

tff(c_30409,plain,(
    ! [A_714,B_715] :
      ( k4_xboole_0(k1_tarski(A_714),B_715) = k1_xboole_0
      | ~ r2_hidden(A_714,B_715) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27584,c_998])).

tff(c_54,plain,(
    ! [A_27,B_28] : k2_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30472,plain,(
    ! [B_715,A_714] :
      ( k2_xboole_0(B_715,k1_tarski(A_714)) = k2_xboole_0(B_715,k1_xboole_0)
      | ~ r2_hidden(A_714,B_715) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30409,c_54])).

tff(c_30684,plain,(
    ! [B_720,A_721] :
      ( k2_xboole_0(B_720,k1_tarski(A_721)) = B_720
      | ~ r2_hidden(A_721,B_720) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_30472])).

tff(c_60,plain,(
    ! [B_33,A_32] : k2_tarski(B_33,A_32) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_162,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_250,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_162])).

tff(c_74,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_256,plain,(
    ! [B_74,A_73] : k2_xboole_0(B_74,A_73) = k2_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_74])).

tff(c_76,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_277,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_76])).

tff(c_30690,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30684,c_277])).

tff(c_30728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_30690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:33:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.06/5.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.06/5.09  
% 12.06/5.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.06/5.09  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 12.06/5.09  
% 12.06/5.09  %Foreground sorts:
% 12.06/5.09  
% 12.06/5.09  
% 12.06/5.09  %Background operators:
% 12.06/5.09  
% 12.06/5.09  
% 12.06/5.09  %Foreground operators:
% 12.06/5.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.06/5.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.06/5.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.06/5.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.06/5.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.06/5.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.06/5.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.06/5.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.06/5.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.06/5.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.06/5.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.06/5.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.06/5.09  tff('#skF_5', type, '#skF_5': $i).
% 12.06/5.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.06/5.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.06/5.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.06/5.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.06/5.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.06/5.09  tff('#skF_4', type, '#skF_4': $i).
% 12.06/5.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.06/5.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.06/5.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.06/5.09  
% 12.16/5.11  tff(f_104, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 12.16/5.11  tff(f_71, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 12.16/5.11  tff(f_81, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.16/5.11  tff(f_77, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.16/5.11  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.16/5.11  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 12.16/5.11  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.16/5.11  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 12.16/5.11  tff(f_67, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.16/5.11  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.16/5.11  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 12.16/5.11  tff(f_83, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 12.16/5.11  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 12.16/5.11  tff(f_97, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 12.16/5.11  tff(f_79, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.16/5.11  tff(f_85, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.16/5.11  tff(f_99, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 12.16/5.11  tff(c_78, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.16/5.11  tff(c_48, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.16/5.11  tff(c_56, plain, (![A_29]: (r1_xboole_0(A_29, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.16/5.11  tff(c_52, plain, (![A_26]: (r1_tarski(k1_xboole_0, A_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.16/5.11  tff(c_206, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.16/5.11  tff(c_213, plain, (![A_26]: (k3_xboole_0(k1_xboole_0, A_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_206])).
% 12.16/5.11  tff(c_1301, plain, (![A_166, B_167, C_168]: (r2_hidden('#skF_1'(A_166, B_167, C_168), A_166) | r2_hidden('#skF_2'(A_166, B_167, C_168), C_168) | k3_xboole_0(A_166, B_167)=C_168)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.16/5.11  tff(c_120, plain, (![B_54, A_55]: (r1_xboole_0(B_54, A_55) | ~r1_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.16/5.11  tff(c_123, plain, (![A_29]: (r1_xboole_0(k1_xboole_0, A_29))), inference(resolution, [status(thm)], [c_56, c_120])).
% 12.16/5.11  tff(c_406, plain, (![A_81, B_82, C_83]: (~r1_xboole_0(A_81, B_82) | ~r2_hidden(C_83, k3_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.16/5.11  tff(c_412, plain, (![A_26, C_83]: (~r1_xboole_0(k1_xboole_0, A_26) | ~r2_hidden(C_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_213, c_406])).
% 12.16/5.11  tff(c_414, plain, (![C_83]: (~r2_hidden(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_412])).
% 12.16/5.11  tff(c_1332, plain, (![B_167, C_168]: (r2_hidden('#skF_2'(k1_xboole_0, B_167, C_168), C_168) | k3_xboole_0(k1_xboole_0, B_167)=C_168)), inference(resolution, [status(thm)], [c_1301, c_414])).
% 12.16/5.11  tff(c_1388, plain, (![B_169, C_170]: (r2_hidden('#skF_2'(k1_xboole_0, B_169, C_170), C_170) | k1_xboole_0=C_170)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_1332])).
% 12.16/5.11  tff(c_38, plain, (![A_14, B_15, C_18]: (~r1_xboole_0(A_14, B_15) | ~r2_hidden(C_18, k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.16/5.11  tff(c_1434, plain, (![A_171, B_172]: (~r1_xboole_0(A_171, B_172) | k3_xboole_0(A_171, B_172)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1388, c_38])).
% 12.16/5.11  tff(c_1451, plain, (![A_29]: (k3_xboole_0(A_29, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_1434])).
% 12.16/5.11  tff(c_1530, plain, (![A_174, B_175, C_176]: (r2_hidden('#skF_1'(A_174, B_175, C_176), B_175) | r2_hidden('#skF_2'(A_174, B_175, C_176), C_176) | k3_xboole_0(A_174, B_175)=C_176)), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.16/5.11  tff(c_1561, plain, (![A_174, C_176]: (r2_hidden('#skF_2'(A_174, k1_xboole_0, C_176), C_176) | k3_xboole_0(A_174, k1_xboole_0)=C_176)), inference(resolution, [status(thm)], [c_1530, c_414])).
% 12.16/5.11  tff(c_1607, plain, (![A_174, C_176]: (r2_hidden('#skF_2'(A_174, k1_xboole_0, C_176), C_176) | k1_xboole_0=C_176)), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1561])).
% 12.16/5.11  tff(c_618, plain, (![A_106, B_107]: (r2_hidden('#skF_3'(A_106, B_107), k3_xboole_0(A_106, B_107)) | r1_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.16/5.11  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.16/5.11  tff(c_634, plain, (![A_106, B_107]: (r2_hidden('#skF_3'(A_106, B_107), B_107) | r1_xboole_0(A_106, B_107))), inference(resolution, [status(thm)], [c_618, c_4])).
% 12.16/5.11  tff(c_44, plain, (![B_20]: (r1_tarski(B_20, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.16/5.11  tff(c_214, plain, (![B_20]: (k3_xboole_0(B_20, B_20)=B_20)), inference(resolution, [status(thm)], [c_44, c_206])).
% 12.16/5.11  tff(c_434, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.16/5.11  tff(c_443, plain, (![B_20]: (k5_xboole_0(B_20, B_20)=k4_xboole_0(B_20, B_20))), inference(superposition, [status(thm), theory('equality')], [c_214, c_434])).
% 12.16/5.11  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.16/5.11  tff(c_684, plain, (![A_112, B_113]: (k5_xboole_0(k5_xboole_0(A_112, B_113), k3_xboole_0(A_112, B_113))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.16/5.11  tff(c_708, plain, (![B_20]: (k5_xboole_0(k5_xboole_0(B_20, B_20), B_20)=k2_xboole_0(B_20, B_20))), inference(superposition, [status(thm), theory('equality')], [c_214, c_684])).
% 12.16/5.11  tff(c_718, plain, (![B_20]: (k5_xboole_0(k4_xboole_0(B_20, B_20), B_20)=B_20)), inference(demodulation, [status(thm), theory('equality')], [c_443, c_20, c_708])).
% 12.16/5.11  tff(c_1183, plain, (![A_156, C_157, B_158]: (r2_hidden(A_156, C_157) | ~r2_hidden(A_156, B_158) | r2_hidden(A_156, k5_xboole_0(B_158, C_157)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.16/5.11  tff(c_2671, plain, (![A_231, B_232]: (r2_hidden(A_231, B_232) | ~r2_hidden(A_231, k4_xboole_0(B_232, B_232)) | r2_hidden(A_231, B_232))), inference(superposition, [status(thm), theory('equality')], [c_718, c_1183])).
% 12.16/5.11  tff(c_2733, plain, (![A_106, B_232]: (r2_hidden('#skF_3'(A_106, k4_xboole_0(B_232, B_232)), B_232) | r1_xboole_0(A_106, k4_xboole_0(B_232, B_232)))), inference(resolution, [status(thm)], [c_634, c_2671])).
% 12.16/5.11  tff(c_1025, plain, (![A_139, C_140, B_141]: (~r2_hidden(A_139, C_140) | ~r2_hidden(A_139, B_141) | ~r2_hidden(A_139, k5_xboole_0(B_141, C_140)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.16/5.11  tff(c_1282, plain, (![A_164, B_165]: (~r2_hidden(A_164, B_165) | ~r2_hidden(A_164, k4_xboole_0(B_165, B_165)) | ~r2_hidden(A_164, B_165))), inference(superposition, [status(thm), theory('equality')], [c_718, c_1025])).
% 12.16/5.11  tff(c_26631, plain, (![A_652, B_653]: (~r2_hidden('#skF_3'(A_652, k4_xboole_0(B_653, B_653)), B_653) | r1_xboole_0(A_652, k4_xboole_0(B_653, B_653)))), inference(resolution, [status(thm)], [c_634, c_1282])).
% 12.16/5.11  tff(c_26844, plain, (![A_658, B_659]: (r1_xboole_0(A_658, k4_xboole_0(B_659, B_659)))), inference(resolution, [status(thm)], [c_2733, c_26631])).
% 12.16/5.11  tff(c_409, plain, (![B_20, C_83]: (~r1_xboole_0(B_20, B_20) | ~r2_hidden(C_83, B_20))), inference(superposition, [status(thm), theory('equality')], [c_214, c_406])).
% 12.16/5.11  tff(c_27287, plain, (![C_662, B_663]: (~r2_hidden(C_662, k4_xboole_0(B_663, B_663)))), inference(resolution, [status(thm)], [c_26844, c_409])).
% 12.16/5.11  tff(c_27584, plain, (![B_663]: (k4_xboole_0(B_663, B_663)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1607, c_27287])).
% 12.16/5.11  tff(c_241, plain, (![A_71, B_72]: (r1_tarski(k1_tarski(A_71), B_72) | ~r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.16/5.11  tff(c_50, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.16/5.11  tff(c_958, plain, (![A_135, B_136]: (k3_xboole_0(k1_tarski(A_135), B_136)=k1_tarski(A_135) | ~r2_hidden(A_135, B_136))), inference(resolution, [status(thm)], [c_241, c_50])).
% 12.16/5.11  tff(c_46, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.16/5.11  tff(c_979, plain, (![A_135, B_136]: (k5_xboole_0(k1_tarski(A_135), k1_tarski(A_135))=k4_xboole_0(k1_tarski(A_135), B_136) | ~r2_hidden(A_135, B_136))), inference(superposition, [status(thm), theory('equality')], [c_958, c_46])).
% 12.16/5.11  tff(c_998, plain, (![A_135, B_136]: (k4_xboole_0(k1_tarski(A_135), k1_tarski(A_135))=k4_xboole_0(k1_tarski(A_135), B_136) | ~r2_hidden(A_135, B_136))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_979])).
% 12.16/5.11  tff(c_30409, plain, (![A_714, B_715]: (k4_xboole_0(k1_tarski(A_714), B_715)=k1_xboole_0 | ~r2_hidden(A_714, B_715))), inference(demodulation, [status(thm), theory('equality')], [c_27584, c_998])).
% 12.16/5.11  tff(c_54, plain, (![A_27, B_28]: (k2_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.16/5.11  tff(c_30472, plain, (![B_715, A_714]: (k2_xboole_0(B_715, k1_tarski(A_714))=k2_xboole_0(B_715, k1_xboole_0) | ~r2_hidden(A_714, B_715))), inference(superposition, [status(thm), theory('equality')], [c_30409, c_54])).
% 12.16/5.11  tff(c_30684, plain, (![B_720, A_721]: (k2_xboole_0(B_720, k1_tarski(A_721))=B_720 | ~r2_hidden(A_721, B_720))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_30472])).
% 12.16/5.11  tff(c_60, plain, (![B_33, A_32]: (k2_tarski(B_33, A_32)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.16/5.11  tff(c_162, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.16/5.11  tff(c_250, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_60, c_162])).
% 12.16/5.11  tff(c_74, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.16/5.11  tff(c_256, plain, (![B_74, A_73]: (k2_xboole_0(B_74, A_73)=k2_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_250, c_74])).
% 12.16/5.11  tff(c_76, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.16/5.11  tff(c_277, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_76])).
% 12.16/5.11  tff(c_30690, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30684, c_277])).
% 12.16/5.11  tff(c_30728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_30690])).
% 12.16/5.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.16/5.11  
% 12.16/5.11  Inference rules
% 12.16/5.11  ----------------------
% 12.16/5.11  #Ref     : 0
% 12.16/5.11  #Sup     : 7524
% 12.16/5.11  #Fact    : 8
% 12.16/5.11  #Define  : 0
% 12.16/5.11  #Split   : 0
% 12.16/5.11  #Chain   : 0
% 12.16/5.11  #Close   : 0
% 12.16/5.11  
% 12.16/5.11  Ordering : KBO
% 12.16/5.11  
% 12.16/5.11  Simplification rules
% 12.16/5.11  ----------------------
% 12.16/5.11  #Subsume      : 2526
% 12.16/5.11  #Demod        : 3760
% 12.16/5.11  #Tautology    : 1715
% 12.16/5.11  #SimpNegUnit  : 173
% 12.16/5.11  #BackRed      : 37
% 12.16/5.11  
% 12.16/5.11  #Partial instantiations: 0
% 12.16/5.11  #Strategies tried      : 1
% 12.16/5.11  
% 12.16/5.11  Timing (in seconds)
% 12.16/5.11  ----------------------
% 12.16/5.11  Preprocessing        : 0.33
% 12.16/5.11  Parsing              : 0.17
% 12.16/5.11  CNF conversion       : 0.02
% 12.16/5.11  Main loop            : 4.02
% 12.16/5.11  Inferencing          : 0.92
% 12.16/5.11  Reduction            : 1.13
% 12.16/5.11  Demodulation         : 0.86
% 12.16/5.11  BG Simplification    : 0.11
% 12.16/5.11  Subsumption          : 1.63
% 12.16/5.11  Abstraction          : 0.16
% 12.16/5.11  MUC search           : 0.00
% 12.16/5.11  Cooper               : 0.00
% 12.16/5.11  Total                : 4.38
% 12.16/5.11  Index Insertion      : 0.00
% 12.16/5.11  Index Deletion       : 0.00
% 12.16/5.11  Index Matching       : 0.00
% 12.16/5.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
