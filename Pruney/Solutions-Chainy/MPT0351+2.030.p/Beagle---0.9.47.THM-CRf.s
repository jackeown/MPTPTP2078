%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:40 EST 2020

% Result     : Theorem 11.30s
% Output     : CNFRefutation 11.30s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 200 expanded)
%              Number of leaves         :   43 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 288 expanded)
%              Number of equality atoms :   57 ( 119 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_64,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_89,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_91,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_34,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_161,plain,(
    ! [B_59,A_60] : k3_tarski(k2_tarski(B_59,A_60)) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_146])).

tff(c_40,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_167,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_40])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [A_30] : k2_subset_1(A_30) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [A_33] : m1_subset_1(k2_subset_1(A_33),k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_63,plain,(
    ! [A_33] : m1_subset_1(A_33,k1_zfmisc_1(A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48])).

tff(c_562,plain,(
    ! [A_111,B_112,C_113] :
      ( k4_subset_1(A_111,B_112,C_113) = k2_xboole_0(B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_853,plain,(
    ! [A_139,B_140] :
      ( k4_subset_1(A_139,B_140,A_139) = k2_xboole_0(B_140,A_139)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_63,c_562])).

tff(c_855,plain,(
    k4_subset_1('#skF_4','#skF_5','#skF_4') = k2_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_853])).

tff(c_861,plain,(
    k4_subset_1('#skF_4','#skF_5','#skF_4') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_855])).

tff(c_60,plain,(
    k4_subset_1('#skF_4','#skF_5',k2_subset_1('#skF_4')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_65,plain,(
    k4_subset_1('#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_60])).

tff(c_894,plain,(
    k2_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_861,c_65])).

tff(c_26,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    ! [A_29] : k1_subset_1(A_29) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    ! [A_43] : k3_subset_1(A_43,k1_subset_1(A_43)) = k2_subset_1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    ! [A_43] : k3_subset_1(A_43,k1_subset_1(A_43)) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_66,plain,(
    ! [A_43] : k3_subset_1(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_58,plain,(
    ! [A_44] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_307,plain,(
    ! [A_88,B_89] :
      ( k3_subset_1(A_88,k3_subset_1(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_311,plain,(
    ! [A_44] : k3_subset_1(A_44,k3_subset_1(A_44,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_307])).

tff(c_316,plain,(
    ! [A_44] : k3_subset_1(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_311])).

tff(c_344,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k3_subset_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_353,plain,(
    ! [A_33] : k4_xboole_0(A_33,A_33) = k3_subset_1(A_33,A_33) ),
    inference(resolution,[status(thm)],[c_63,c_344])).

tff(c_380,plain,(
    ! [A_97] : k4_xboole_0(A_97,A_97) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_353])).

tff(c_32,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_392,plain,(
    ! [A_97] : k5_xboole_0(A_97,k1_xboole_0) = k2_xboole_0(A_97,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_32])).

tff(c_407,plain,(
    ! [A_97] : k5_xboole_0(A_97,k1_xboole_0) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_392])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [D_72,A_73,B_74] :
      ( r2_hidden(D_72,A_73)
      | ~ r2_hidden(D_72,k4_xboole_0(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2072,plain,(
    ! [A_195,B_196,B_197] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_195,B_196),B_197),A_195)
      | r1_tarski(k4_xboole_0(A_195,B_196),B_197) ) ),
    inference(resolution,[status(thm)],[c_6,c_256])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2170,plain,(
    ! [A_195,B_196] : r1_tarski(k4_xboole_0(A_195,B_196),A_195) ),
    inference(resolution,[status(thm)],[c_2072,c_4])).

tff(c_340,plain,(
    ! [C_91,A_92,B_93] :
      ( r2_hidden(C_91,A_92)
      | ~ r2_hidden(C_91,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1909,plain,(
    ! [A_187,B_188,A_189] :
      ( r2_hidden('#skF_1'(A_187,B_188),A_189)
      | ~ m1_subset_1(A_187,k1_zfmisc_1(A_189))
      | r1_tarski(A_187,B_188) ) ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_1979,plain,(
    ! [A_190,A_191] :
      ( ~ m1_subset_1(A_190,k1_zfmisc_1(A_191))
      | r1_tarski(A_190,A_191) ) ),
    inference(resolution,[status(thm)],[c_1909,c_4])).

tff(c_1989,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1979])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1997,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1989,c_28])).

tff(c_30,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_303,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1475,plain,(
    ! [A_167,B_168,B_169] :
      ( r2_hidden('#skF_1'(A_167,B_168),B_169)
      | ~ r1_tarski(A_167,B_169)
      | r1_tarski(A_167,B_168) ) ),
    inference(resolution,[status(thm)],[c_6,c_303])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17185,plain,(
    ! [A_566,B_567,B_568,A_569] :
      ( ~ r2_hidden('#skF_1'(A_566,B_567),B_568)
      | ~ r1_tarski(A_566,k4_xboole_0(A_569,B_568))
      | r1_tarski(A_566,B_567) ) ),
    inference(resolution,[status(thm)],[c_1475,c_10])).

tff(c_17420,plain,(
    ! [A_573,A_574,B_575] :
      ( ~ r1_tarski(A_573,k4_xboole_0(A_574,A_573))
      | r1_tarski(A_573,B_575) ) ),
    inference(resolution,[status(thm)],[c_6,c_17185])).

tff(c_18157,plain,(
    ! [A_604,B_605,B_606] :
      ( ~ r1_tarski(k4_xboole_0(A_604,B_605),k3_xboole_0(A_604,B_605))
      | r1_tarski(k4_xboole_0(A_604,B_605),B_606) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_17420])).

tff(c_18199,plain,(
    ! [B_606] :
      ( ~ r1_tarski(k4_xboole_0('#skF_5','#skF_4'),'#skF_5')
      | r1_tarski(k4_xboole_0('#skF_5','#skF_4'),B_606) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1997,c_18157])).

tff(c_18273,plain,(
    ! [B_607] : r1_tarski(k4_xboole_0('#skF_5','#skF_4'),B_607) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2170,c_18199])).

tff(c_358,plain,(
    ! [A_33] : k4_xboole_0(A_33,A_33) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_353])).

tff(c_938,plain,(
    ! [A_143,B_144,C_145] :
      ( r2_hidden('#skF_2'(A_143,B_144,C_145),A_143)
      | r2_hidden('#skF_3'(A_143,B_144,C_145),C_145)
      | k4_xboole_0(A_143,B_144) = C_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_953,plain,(
    ! [A_143,C_145] :
      ( r2_hidden('#skF_3'(A_143,A_143,C_145),C_145)
      | k4_xboole_0(A_143,A_143) = C_145 ) ),
    inference(resolution,[status(thm)],[c_938,c_22])).

tff(c_1041,plain,(
    ! [A_146,C_147] :
      ( r2_hidden('#skF_3'(A_146,A_146,C_147),C_147)
      | k1_xboole_0 = C_147 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_953])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1091,plain,(
    ! [A_146,A_6,B_7] :
      ( r2_hidden('#skF_3'(A_146,A_146,k4_xboole_0(A_6,B_7)),A_6)
      | k4_xboole_0(A_6,B_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1041,c_12])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1546,plain,(
    ! [A_172,C_173,B_174] :
      ( r2_hidden('#skF_3'(A_172,A_172,C_173),B_174)
      | ~ r1_tarski(C_173,B_174)
      | k1_xboole_0 = C_173 ) ),
    inference(resolution,[status(thm)],[c_1041,c_2])).

tff(c_354,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_344])).

tff(c_461,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_5')
      | ~ r2_hidden(D_11,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_10])).

tff(c_7929,plain,(
    ! [A_350,C_351] :
      ( ~ r2_hidden('#skF_3'(A_350,A_350,C_351),'#skF_5')
      | ~ r1_tarski(C_351,k3_subset_1('#skF_4','#skF_5'))
      | k1_xboole_0 = C_351 ) ),
    inference(resolution,[status(thm)],[c_1546,c_461])).

tff(c_7983,plain,(
    ! [B_7] :
      ( ~ r1_tarski(k4_xboole_0('#skF_5',B_7),k3_subset_1('#skF_4','#skF_5'))
      | k4_xboole_0('#skF_5',B_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1091,c_7929])).

tff(c_18386,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18273,c_7983])).

tff(c_18683,plain,(
    k5_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18386,c_32])).

tff(c_18806,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_18683])).

tff(c_18808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_894,c_18806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.30/4.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.30/4.27  
% 11.30/4.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.30/4.27  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 11.30/4.27  
% 11.30/4.27  %Foreground sorts:
% 11.30/4.27  
% 11.30/4.27  
% 11.30/4.27  %Background operators:
% 11.30/4.27  
% 11.30/4.27  
% 11.30/4.27  %Foreground operators:
% 11.30/4.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.30/4.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.30/4.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.30/4.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.30/4.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.30/4.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.30/4.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.30/4.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.30/4.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.30/4.27  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.30/4.27  tff('#skF_5', type, '#skF_5': $i).
% 11.30/4.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.30/4.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.30/4.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.30/4.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.30/4.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.30/4.27  tff('#skF_4', type, '#skF_4': $i).
% 11.30/4.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.30/4.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.30/4.27  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 11.30/4.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.30/4.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.30/4.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.30/4.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.30/4.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.30/4.27  
% 11.30/4.29  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.30/4.29  tff(f_60, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.30/4.29  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 11.30/4.29  tff(f_64, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 11.30/4.29  tff(f_70, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.30/4.29  tff(f_87, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.30/4.29  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 11.30/4.29  tff(f_62, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 11.30/4.29  tff(f_89, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 11.30/4.29  tff(f_91, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.30/4.29  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.30/4.29  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.30/4.29  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.30/4.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.30/4.29  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.30/4.29  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 11.30/4.29  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.30/4.29  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.30/4.29  tff(c_34, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.30/4.29  tff(c_146, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.30/4.29  tff(c_161, plain, (![B_59, A_60]: (k3_tarski(k2_tarski(B_59, A_60))=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_34, c_146])).
% 11.30/4.29  tff(c_40, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.30/4.29  tff(c_167, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_161, c_40])).
% 11.30/4.29  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.30/4.29  tff(c_44, plain, (![A_30]: (k2_subset_1(A_30)=A_30)), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.30/4.29  tff(c_48, plain, (![A_33]: (m1_subset_1(k2_subset_1(A_33), k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.30/4.29  tff(c_63, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48])).
% 11.30/4.29  tff(c_562, plain, (![A_111, B_112, C_113]: (k4_subset_1(A_111, B_112, C_113)=k2_xboole_0(B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.30/4.29  tff(c_853, plain, (![A_139, B_140]: (k4_subset_1(A_139, B_140, A_139)=k2_xboole_0(B_140, A_139) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(resolution, [status(thm)], [c_63, c_562])).
% 11.30/4.29  tff(c_855, plain, (k4_subset_1('#skF_4', '#skF_5', '#skF_4')=k2_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_853])).
% 11.30/4.29  tff(c_861, plain, (k4_subset_1('#skF_4', '#skF_5', '#skF_4')=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_855])).
% 11.30/4.29  tff(c_60, plain, (k4_subset_1('#skF_4', '#skF_5', k2_subset_1('#skF_4'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.30/4.29  tff(c_65, plain, (k4_subset_1('#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_60])).
% 11.30/4.29  tff(c_894, plain, (k2_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_861, c_65])).
% 11.30/4.29  tff(c_26, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.30/4.29  tff(c_42, plain, (![A_29]: (k1_subset_1(A_29)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.30/4.29  tff(c_56, plain, (![A_43]: (k3_subset_1(A_43, k1_subset_1(A_43))=k2_subset_1(A_43))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.30/4.29  tff(c_64, plain, (![A_43]: (k3_subset_1(A_43, k1_subset_1(A_43))=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 11.30/4.29  tff(c_66, plain, (![A_43]: (k3_subset_1(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64])).
% 11.30/4.29  tff(c_58, plain, (![A_44]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.30/4.29  tff(c_307, plain, (![A_88, B_89]: (k3_subset_1(A_88, k3_subset_1(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.30/4.29  tff(c_311, plain, (![A_44]: (k3_subset_1(A_44, k3_subset_1(A_44, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_307])).
% 11.30/4.29  tff(c_316, plain, (![A_44]: (k3_subset_1(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_311])).
% 11.30/4.29  tff(c_344, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k3_subset_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.30/4.29  tff(c_353, plain, (![A_33]: (k4_xboole_0(A_33, A_33)=k3_subset_1(A_33, A_33))), inference(resolution, [status(thm)], [c_63, c_344])).
% 11.30/4.29  tff(c_380, plain, (![A_97]: (k4_xboole_0(A_97, A_97)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_316, c_353])).
% 11.30/4.29  tff(c_32, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.30/4.29  tff(c_392, plain, (![A_97]: (k5_xboole_0(A_97, k1_xboole_0)=k2_xboole_0(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_380, c_32])).
% 11.30/4.29  tff(c_407, plain, (![A_97]: (k5_xboole_0(A_97, k1_xboole_0)=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_392])).
% 11.30/4.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.30/4.29  tff(c_256, plain, (![D_72, A_73, B_74]: (r2_hidden(D_72, A_73) | ~r2_hidden(D_72, k4_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.30/4.29  tff(c_2072, plain, (![A_195, B_196, B_197]: (r2_hidden('#skF_1'(k4_xboole_0(A_195, B_196), B_197), A_195) | r1_tarski(k4_xboole_0(A_195, B_196), B_197))), inference(resolution, [status(thm)], [c_6, c_256])).
% 11.30/4.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.30/4.29  tff(c_2170, plain, (![A_195, B_196]: (r1_tarski(k4_xboole_0(A_195, B_196), A_195))), inference(resolution, [status(thm)], [c_2072, c_4])).
% 11.30/4.29  tff(c_340, plain, (![C_91, A_92, B_93]: (r2_hidden(C_91, A_92) | ~r2_hidden(C_91, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.30/4.29  tff(c_1909, plain, (![A_187, B_188, A_189]: (r2_hidden('#skF_1'(A_187, B_188), A_189) | ~m1_subset_1(A_187, k1_zfmisc_1(A_189)) | r1_tarski(A_187, B_188))), inference(resolution, [status(thm)], [c_6, c_340])).
% 11.30/4.29  tff(c_1979, plain, (![A_190, A_191]: (~m1_subset_1(A_190, k1_zfmisc_1(A_191)) | r1_tarski(A_190, A_191))), inference(resolution, [status(thm)], [c_1909, c_4])).
% 11.30/4.29  tff(c_1989, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_1979])).
% 11.30/4.29  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.30/4.29  tff(c_1997, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_1989, c_28])).
% 11.30/4.29  tff(c_30, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.30/4.29  tff(c_303, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.30/4.29  tff(c_1475, plain, (![A_167, B_168, B_169]: (r2_hidden('#skF_1'(A_167, B_168), B_169) | ~r1_tarski(A_167, B_169) | r1_tarski(A_167, B_168))), inference(resolution, [status(thm)], [c_6, c_303])).
% 11.30/4.29  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.30/4.29  tff(c_17185, plain, (![A_566, B_567, B_568, A_569]: (~r2_hidden('#skF_1'(A_566, B_567), B_568) | ~r1_tarski(A_566, k4_xboole_0(A_569, B_568)) | r1_tarski(A_566, B_567))), inference(resolution, [status(thm)], [c_1475, c_10])).
% 11.30/4.29  tff(c_17420, plain, (![A_573, A_574, B_575]: (~r1_tarski(A_573, k4_xboole_0(A_574, A_573)) | r1_tarski(A_573, B_575))), inference(resolution, [status(thm)], [c_6, c_17185])).
% 11.30/4.29  tff(c_18157, plain, (![A_604, B_605, B_606]: (~r1_tarski(k4_xboole_0(A_604, B_605), k3_xboole_0(A_604, B_605)) | r1_tarski(k4_xboole_0(A_604, B_605), B_606))), inference(superposition, [status(thm), theory('equality')], [c_30, c_17420])).
% 11.30/4.29  tff(c_18199, plain, (![B_606]: (~r1_tarski(k4_xboole_0('#skF_5', '#skF_4'), '#skF_5') | r1_tarski(k4_xboole_0('#skF_5', '#skF_4'), B_606))), inference(superposition, [status(thm), theory('equality')], [c_1997, c_18157])).
% 11.30/4.29  tff(c_18273, plain, (![B_607]: (r1_tarski(k4_xboole_0('#skF_5', '#skF_4'), B_607))), inference(demodulation, [status(thm), theory('equality')], [c_2170, c_18199])).
% 11.30/4.29  tff(c_358, plain, (![A_33]: (k4_xboole_0(A_33, A_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_316, c_353])).
% 11.30/4.29  tff(c_938, plain, (![A_143, B_144, C_145]: (r2_hidden('#skF_2'(A_143, B_144, C_145), A_143) | r2_hidden('#skF_3'(A_143, B_144, C_145), C_145) | k4_xboole_0(A_143, B_144)=C_145)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.30/4.29  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.30/4.29  tff(c_953, plain, (![A_143, C_145]: (r2_hidden('#skF_3'(A_143, A_143, C_145), C_145) | k4_xboole_0(A_143, A_143)=C_145)), inference(resolution, [status(thm)], [c_938, c_22])).
% 11.30/4.29  tff(c_1041, plain, (![A_146, C_147]: (r2_hidden('#skF_3'(A_146, A_146, C_147), C_147) | k1_xboole_0=C_147)), inference(demodulation, [status(thm), theory('equality')], [c_358, c_953])).
% 11.30/4.29  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.30/4.29  tff(c_1091, plain, (![A_146, A_6, B_7]: (r2_hidden('#skF_3'(A_146, A_146, k4_xboole_0(A_6, B_7)), A_6) | k4_xboole_0(A_6, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1041, c_12])).
% 11.30/4.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.30/4.29  tff(c_1546, plain, (![A_172, C_173, B_174]: (r2_hidden('#skF_3'(A_172, A_172, C_173), B_174) | ~r1_tarski(C_173, B_174) | k1_xboole_0=C_173)), inference(resolution, [status(thm)], [c_1041, c_2])).
% 11.30/4.29  tff(c_354, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_344])).
% 11.30/4.29  tff(c_461, plain, (![D_11]: (~r2_hidden(D_11, '#skF_5') | ~r2_hidden(D_11, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_354, c_10])).
% 11.30/4.29  tff(c_7929, plain, (![A_350, C_351]: (~r2_hidden('#skF_3'(A_350, A_350, C_351), '#skF_5') | ~r1_tarski(C_351, k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0=C_351)), inference(resolution, [status(thm)], [c_1546, c_461])).
% 11.30/4.29  tff(c_7983, plain, (![B_7]: (~r1_tarski(k4_xboole_0('#skF_5', B_7), k3_subset_1('#skF_4', '#skF_5')) | k4_xboole_0('#skF_5', B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1091, c_7929])).
% 11.30/4.29  tff(c_18386, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_18273, c_7983])).
% 11.30/4.29  tff(c_18683, plain, (k5_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18386, c_32])).
% 11.30/4.29  tff(c_18806, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_407, c_18683])).
% 11.30/4.29  tff(c_18808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_894, c_18806])).
% 11.30/4.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.30/4.29  
% 11.30/4.29  Inference rules
% 11.30/4.29  ----------------------
% 11.30/4.29  #Ref     : 0
% 11.30/4.29  #Sup     : 4395
% 11.30/4.29  #Fact    : 0
% 11.30/4.29  #Define  : 0
% 11.30/4.29  #Split   : 17
% 11.30/4.29  #Chain   : 0
% 11.30/4.29  #Close   : 0
% 11.30/4.29  
% 11.30/4.29  Ordering : KBO
% 11.30/4.29  
% 11.30/4.29  Simplification rules
% 11.30/4.29  ----------------------
% 11.30/4.29  #Subsume      : 1180
% 11.30/4.29  #Demod        : 3891
% 11.30/4.29  #Tautology    : 1068
% 11.30/4.29  #SimpNegUnit  : 108
% 11.30/4.29  #BackRed      : 39
% 11.30/4.29  
% 11.30/4.29  #Partial instantiations: 0
% 11.30/4.29  #Strategies tried      : 1
% 11.30/4.29  
% 11.30/4.29  Timing (in seconds)
% 11.30/4.29  ----------------------
% 11.30/4.29  Preprocessing        : 0.33
% 11.30/4.29  Parsing              : 0.17
% 11.30/4.29  CNF conversion       : 0.02
% 11.30/4.29  Main loop            : 3.19
% 11.30/4.29  Inferencing          : 0.69
% 11.30/4.30  Reduction            : 1.39
% 11.30/4.30  Demodulation         : 1.11
% 11.30/4.30  BG Simplification    : 0.08
% 11.30/4.30  Subsumption          : 0.84
% 11.30/4.30  Abstraction          : 0.11
% 11.30/4.30  MUC search           : 0.00
% 11.30/4.30  Cooper               : 0.00
% 11.30/4.30  Total                : 3.56
% 11.30/4.30  Index Insertion      : 0.00
% 11.30/4.30  Index Deletion       : 0.00
% 11.30/4.30  Index Matching       : 0.00
% 11.30/4.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
