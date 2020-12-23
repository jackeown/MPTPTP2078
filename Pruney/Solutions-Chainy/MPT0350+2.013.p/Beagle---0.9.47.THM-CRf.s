%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:27 EST 2020

% Result     : Theorem 36.49s
% Output     : CNFRefutation 36.49s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 191 expanded)
%              Number of leaves         :   49 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 207 expanded)
%              Number of equality atoms :   54 ( 138 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_93,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_104,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_78,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_24,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_203,plain,(
    ! [A_96,B_97] : k3_tarski(k2_tarski(A_96,B_97)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_228,plain,(
    ! [B_102,A_103] : k3_tarski(k2_tarski(B_102,A_103)) = k2_xboole_0(A_103,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_203])).

tff(c_56,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_234,plain,(
    ! [B_102,A_103] : k2_xboole_0(B_102,A_103) = k2_xboole_0(A_103,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_56])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_478,plain,(
    ! [A_134,B_135] :
      ( k4_xboole_0(A_134,B_135) = k3_subset_1(A_134,B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_487,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_478])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_491,plain,(
    k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_14])).

tff(c_494,plain,(
    k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_491])).

tff(c_72,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k3_subset_1(A_77,B_78),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2007,plain,(
    ! [A_195,B_196,C_197] :
      ( k4_subset_1(A_195,B_196,C_197) = k2_xboole_0(B_196,C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(A_195))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(A_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58417,plain,(
    ! [A_523,B_524,B_525] :
      ( k4_subset_1(A_523,B_524,k3_subset_1(A_523,B_525)) = k2_xboole_0(B_524,k3_subset_1(A_523,B_525))
      | ~ m1_subset_1(B_524,k1_zfmisc_1(A_523))
      | ~ m1_subset_1(B_525,k1_zfmisc_1(A_523)) ) ),
    inference(resolution,[status(thm)],[c_72,c_2007])).

tff(c_58455,plain,(
    ! [B_526] :
      ( k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6',B_526)) = k2_xboole_0('#skF_7',k3_subset_1('#skF_6',B_526))
      | ~ m1_subset_1(B_526,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_80,c_58417])).

tff(c_58482,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_80,c_58455])).

tff(c_58498,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_58482])).

tff(c_68,plain,(
    ! [A_74] : k2_subset_1(A_74) = A_74 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_81,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_78])).

tff(c_58499,plain,(
    k2_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58498,c_81])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_509,plain,(
    ! [A_138,B_139,C_140] : k5_xboole_0(k5_xboole_0(A_138,B_139),C_140) = k5_xboole_0(A_138,k5_xboole_0(B_139,C_140)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_681,plain,(
    ! [A_144,C_145] : k5_xboole_0(A_144,k5_xboole_0(A_144,C_145)) = k5_xboole_0(k1_xboole_0,C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_509])).

tff(c_749,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,A_18) = k5_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_681])).

tff(c_767,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_749])).

tff(c_554,plain,(
    ! [A_18,C_140] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_140)) = k5_xboole_0(k1_xboole_0,C_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_509])).

tff(c_839,plain,(
    ! [A_18,C_140] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_140)) = C_140 ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_554])).

tff(c_527,plain,(
    ! [A_138,B_139] : k5_xboole_0(A_138,k5_xboole_0(B_139,k5_xboole_0(A_138,B_139))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_20])).

tff(c_1075,plain,(
    ! [A_159,C_160] : k5_xboole_0(A_159,k5_xboole_0(A_159,C_160)) = C_160 ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_554])).

tff(c_1125,plain,(
    ! [B_139,A_138] : k5_xboole_0(B_139,k5_xboole_0(A_138,B_139)) = k5_xboole_0(A_138,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_1075])).

tff(c_1224,plain,(
    ! [B_164,A_165] : k5_xboole_0(B_164,k5_xboole_0(A_165,B_164)) = A_165 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1125])).

tff(c_1260,plain,(
    ! [A_18,C_140] : k5_xboole_0(k5_xboole_0(A_18,C_140),C_140) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_1224])).

tff(c_74,plain,(
    ! [A_79] : ~ v1_xboole_0(k1_zfmisc_1(A_79)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    ! [A_71] : k3_tarski(k1_zfmisc_1(A_71)) = A_71 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [B_73,A_72] :
      ( r2_hidden(B_73,A_72)
      | ~ m1_subset_1(B_73,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_471,plain,(
    ! [C_131,A_132,D_133] :
      ( r2_hidden(C_131,k3_tarski(A_132))
      | ~ r2_hidden(D_133,A_132)
      | ~ r2_hidden(C_131,D_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5689,plain,(
    ! [C_290,A_291,B_292] :
      ( r2_hidden(C_290,k3_tarski(A_291))
      | ~ r2_hidden(C_290,B_292)
      | ~ m1_subset_1(B_292,A_291)
      | v1_xboole_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_62,c_471])).

tff(c_102455,plain,(
    ! [A_641,B_642,A_643] :
      ( r2_hidden('#skF_1'(A_641,B_642),k3_tarski(A_643))
      | ~ m1_subset_1(A_641,A_643)
      | v1_xboole_0(A_643)
      | r1_tarski(A_641,B_642) ) ),
    inference(resolution,[status(thm)],[c_8,c_5689])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102484,plain,(
    ! [A_644,A_645] :
      ( ~ m1_subset_1(A_644,A_645)
      | v1_xboole_0(A_645)
      | r1_tarski(A_644,k3_tarski(A_645)) ) ),
    inference(resolution,[status(thm)],[c_102455,c_6])).

tff(c_102506,plain,(
    ! [A_644,A_71] :
      ( ~ m1_subset_1(A_644,k1_zfmisc_1(A_71))
      | v1_xboole_0(k1_zfmisc_1(A_71))
      | r1_tarski(A_644,A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_102484])).

tff(c_102512,plain,(
    ! [A_646,A_647] :
      ( ~ m1_subset_1(A_646,k1_zfmisc_1(A_647))
      | r1_tarski(A_646,A_647) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_102506])).

tff(c_102571,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_102512])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_102578,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_102571,c_12])).

tff(c_1630,plain,(
    ! [B_177,A_178] : k5_xboole_0(B_177,A_178) = k5_xboole_0(A_178,B_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_839])).

tff(c_22,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1699,plain,(
    ! [A_178,B_177] : k5_xboole_0(k5_xboole_0(A_178,B_177),k3_xboole_0(B_177,A_178)) = k2_xboole_0(B_177,A_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_22])).

tff(c_102597,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_7') = k2_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_102578,c_1699])).

tff(c_102703,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_234,c_102597])).

tff(c_102705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58499,c_102703])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.49/28.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.49/28.06  
% 36.49/28.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.49/28.06  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 36.49/28.06  
% 36.49/28.06  %Foreground sorts:
% 36.49/28.06  
% 36.49/28.06  
% 36.49/28.06  %Background operators:
% 36.49/28.06  
% 36.49/28.06  
% 36.49/28.06  %Foreground operators:
% 36.49/28.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.49/28.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.49/28.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.49/28.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.49/28.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 36.49/28.06  tff('#skF_7', type, '#skF_7': $i).
% 36.49/28.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 36.49/28.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 36.49/28.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.49/28.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 36.49/28.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.49/28.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 36.49/28.06  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 36.49/28.06  tff('#skF_6', type, '#skF_6': $i).
% 36.49/28.06  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 36.49/28.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 36.49/28.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 36.49/28.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 36.49/28.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 36.49/28.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.49/28.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 36.49/28.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.49/28.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 36.49/28.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.49/28.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.49/28.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 36.49/28.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.49/28.06  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 36.49/28.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 36.49/28.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 36.49/28.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 36.49/28.06  
% 36.49/28.08  tff(f_52, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 36.49/28.08  tff(f_76, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 36.49/28.08  tff(f_115, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 36.49/28.08  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 36.49/28.08  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 36.49/28.08  tff(f_101, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 36.49/28.08  tff(f_110, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 36.49/28.08  tff(f_93, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 36.49/28.08  tff(f_44, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 36.49/28.08  tff(f_48, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 36.49/28.08  tff(f_46, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 36.49/28.08  tff(f_104, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 36.49/28.08  tff(f_78, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 36.49/28.08  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 36.49/28.08  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 36.49/28.08  tff(f_74, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 36.49/28.08  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 36.49/28.08  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 36.49/28.08  tff(c_24, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 36.49/28.08  tff(c_203, plain, (![A_96, B_97]: (k3_tarski(k2_tarski(A_96, B_97))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_76])).
% 36.49/28.08  tff(c_228, plain, (![B_102, A_103]: (k3_tarski(k2_tarski(B_102, A_103))=k2_xboole_0(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_24, c_203])).
% 36.49/28.08  tff(c_56, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 36.49/28.08  tff(c_234, plain, (![B_102, A_103]: (k2_xboole_0(B_102, A_103)=k2_xboole_0(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_228, c_56])).
% 36.49/28.08  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 36.49/28.08  tff(c_478, plain, (![A_134, B_135]: (k4_xboole_0(A_134, B_135)=k3_subset_1(A_134, B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 36.49/28.08  tff(c_487, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_80, c_478])).
% 36.49/28.08  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 36.49/28.08  tff(c_491, plain, (k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_487, c_14])).
% 36.49/28.08  tff(c_494, plain, (k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_491])).
% 36.49/28.08  tff(c_72, plain, (![A_77, B_78]: (m1_subset_1(k3_subset_1(A_77, B_78), k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 36.49/28.08  tff(c_2007, plain, (![A_195, B_196, C_197]: (k4_subset_1(A_195, B_196, C_197)=k2_xboole_0(B_196, C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(A_195)) | ~m1_subset_1(B_196, k1_zfmisc_1(A_195)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.49/28.08  tff(c_58417, plain, (![A_523, B_524, B_525]: (k4_subset_1(A_523, B_524, k3_subset_1(A_523, B_525))=k2_xboole_0(B_524, k3_subset_1(A_523, B_525)) | ~m1_subset_1(B_524, k1_zfmisc_1(A_523)) | ~m1_subset_1(B_525, k1_zfmisc_1(A_523)))), inference(resolution, [status(thm)], [c_72, c_2007])).
% 36.49/28.08  tff(c_58455, plain, (![B_526]: (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', B_526))=k2_xboole_0('#skF_7', k3_subset_1('#skF_6', B_526)) | ~m1_subset_1(B_526, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_80, c_58417])).
% 36.49/28.08  tff(c_58482, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_80, c_58455])).
% 36.49/28.08  tff(c_58498, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_58482])).
% 36.49/28.08  tff(c_68, plain, (![A_74]: (k2_subset_1(A_74)=A_74)), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.49/28.08  tff(c_78, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 36.49/28.08  tff(c_81, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_78])).
% 36.49/28.08  tff(c_58499, plain, (k2_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58498, c_81])).
% 36.49/28.08  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 36.49/28.08  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 36.49/28.08  tff(c_509, plain, (![A_138, B_139, C_140]: (k5_xboole_0(k5_xboole_0(A_138, B_139), C_140)=k5_xboole_0(A_138, k5_xboole_0(B_139, C_140)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 36.49/28.08  tff(c_681, plain, (![A_144, C_145]: (k5_xboole_0(A_144, k5_xboole_0(A_144, C_145))=k5_xboole_0(k1_xboole_0, C_145))), inference(superposition, [status(thm), theory('equality')], [c_20, c_509])).
% 36.49/28.08  tff(c_749, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, A_18)=k5_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_681])).
% 36.49/28.08  tff(c_767, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, A_18)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_749])).
% 36.49/28.08  tff(c_554, plain, (![A_18, C_140]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_140))=k5_xboole_0(k1_xboole_0, C_140))), inference(superposition, [status(thm), theory('equality')], [c_20, c_509])).
% 36.49/28.08  tff(c_839, plain, (![A_18, C_140]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_140))=C_140)), inference(demodulation, [status(thm), theory('equality')], [c_767, c_554])).
% 36.49/28.08  tff(c_527, plain, (![A_138, B_139]: (k5_xboole_0(A_138, k5_xboole_0(B_139, k5_xboole_0(A_138, B_139)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_509, c_20])).
% 36.49/28.08  tff(c_1075, plain, (![A_159, C_160]: (k5_xboole_0(A_159, k5_xboole_0(A_159, C_160))=C_160)), inference(demodulation, [status(thm), theory('equality')], [c_767, c_554])).
% 36.49/28.08  tff(c_1125, plain, (![B_139, A_138]: (k5_xboole_0(B_139, k5_xboole_0(A_138, B_139))=k5_xboole_0(A_138, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_527, c_1075])).
% 36.49/28.08  tff(c_1224, plain, (![B_164, A_165]: (k5_xboole_0(B_164, k5_xboole_0(A_165, B_164))=A_165)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1125])).
% 36.49/28.08  tff(c_1260, plain, (![A_18, C_140]: (k5_xboole_0(k5_xboole_0(A_18, C_140), C_140)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_839, c_1224])).
% 36.49/28.08  tff(c_74, plain, (![A_79]: (~v1_xboole_0(k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 36.49/28.08  tff(c_58, plain, (![A_71]: (k3_tarski(k1_zfmisc_1(A_71))=A_71)), inference(cnfTransformation, [status(thm)], [f_78])).
% 36.49/28.08  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.49/28.08  tff(c_62, plain, (![B_73, A_72]: (r2_hidden(B_73, A_72) | ~m1_subset_1(B_73, A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.49/28.08  tff(c_471, plain, (![C_131, A_132, D_133]: (r2_hidden(C_131, k3_tarski(A_132)) | ~r2_hidden(D_133, A_132) | ~r2_hidden(C_131, D_133))), inference(cnfTransformation, [status(thm)], [f_74])).
% 36.49/28.08  tff(c_5689, plain, (![C_290, A_291, B_292]: (r2_hidden(C_290, k3_tarski(A_291)) | ~r2_hidden(C_290, B_292) | ~m1_subset_1(B_292, A_291) | v1_xboole_0(A_291))), inference(resolution, [status(thm)], [c_62, c_471])).
% 36.49/28.08  tff(c_102455, plain, (![A_641, B_642, A_643]: (r2_hidden('#skF_1'(A_641, B_642), k3_tarski(A_643)) | ~m1_subset_1(A_641, A_643) | v1_xboole_0(A_643) | r1_tarski(A_641, B_642))), inference(resolution, [status(thm)], [c_8, c_5689])).
% 36.49/28.08  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 36.49/28.08  tff(c_102484, plain, (![A_644, A_645]: (~m1_subset_1(A_644, A_645) | v1_xboole_0(A_645) | r1_tarski(A_644, k3_tarski(A_645)))), inference(resolution, [status(thm)], [c_102455, c_6])).
% 36.49/28.08  tff(c_102506, plain, (![A_644, A_71]: (~m1_subset_1(A_644, k1_zfmisc_1(A_71)) | v1_xboole_0(k1_zfmisc_1(A_71)) | r1_tarski(A_644, A_71))), inference(superposition, [status(thm), theory('equality')], [c_58, c_102484])).
% 36.49/28.08  tff(c_102512, plain, (![A_646, A_647]: (~m1_subset_1(A_646, k1_zfmisc_1(A_647)) | r1_tarski(A_646, A_647))), inference(negUnitSimplification, [status(thm)], [c_74, c_102506])).
% 36.49/28.08  tff(c_102571, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_102512])).
% 36.49/28.08  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.49/28.08  tff(c_102578, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_102571, c_12])).
% 36.49/28.08  tff(c_1630, plain, (![B_177, A_178]: (k5_xboole_0(B_177, A_178)=k5_xboole_0(A_178, B_177))), inference(superposition, [status(thm), theory('equality')], [c_1224, c_839])).
% 36.49/28.08  tff(c_22, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 36.49/28.08  tff(c_1699, plain, (![A_178, B_177]: (k5_xboole_0(k5_xboole_0(A_178, B_177), k3_xboole_0(B_177, A_178))=k2_xboole_0(B_177, A_178))), inference(superposition, [status(thm), theory('equality')], [c_1630, c_22])).
% 36.49/28.08  tff(c_102597, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_7')=k2_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_102578, c_1699])).
% 36.49/28.08  tff(c_102703, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_234, c_102597])).
% 36.49/28.08  tff(c_102705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58499, c_102703])).
% 36.49/28.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.49/28.08  
% 36.49/28.08  Inference rules
% 36.49/28.08  ----------------------
% 36.49/28.08  #Ref     : 0
% 36.49/28.08  #Sup     : 27126
% 36.49/28.08  #Fact    : 0
% 36.49/28.08  #Define  : 0
% 36.49/28.08  #Split   : 0
% 36.49/28.08  #Chain   : 0
% 36.49/28.08  #Close   : 0
% 36.49/28.08  
% 36.49/28.08  Ordering : KBO
% 36.49/28.08  
% 36.49/28.08  Simplification rules
% 36.49/28.08  ----------------------
% 36.49/28.08  #Subsume      : 1440
% 36.49/28.08  #Demod        : 42443
% 36.49/28.08  #Tautology    : 9437
% 36.49/28.08  #SimpNegUnit  : 53
% 36.49/28.08  #BackRed      : 14
% 36.49/28.08  
% 36.49/28.08  #Partial instantiations: 0
% 36.49/28.08  #Strategies tried      : 1
% 36.49/28.08  
% 36.49/28.08  Timing (in seconds)
% 36.49/28.08  ----------------------
% 36.49/28.08  Preprocessing        : 0.35
% 36.49/28.08  Parsing              : 0.18
% 36.49/28.08  CNF conversion       : 0.03
% 36.49/28.08  Main loop            : 26.97
% 36.49/28.08  Inferencing          : 2.15
% 36.49/28.09  Reduction            : 20.03
% 36.49/28.09  Demodulation         : 19.16
% 36.49/28.09  BG Simplification    : 0.40
% 36.49/28.09  Subsumption          : 3.61
% 36.49/28.09  Abstraction          : 0.67
% 36.49/28.09  MUC search           : 0.00
% 36.49/28.09  Cooper               : 0.00
% 36.49/28.09  Total                : 27.35
% 36.49/28.09  Index Insertion      : 0.00
% 36.49/28.09  Index Deletion       : 0.00
% 36.49/28.09  Index Matching       : 0.00
% 36.49/28.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
