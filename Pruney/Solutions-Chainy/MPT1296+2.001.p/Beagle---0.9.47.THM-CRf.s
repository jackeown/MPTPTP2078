%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:40 EST 2020

% Result     : Theorem 8.30s
% Output     : CNFRefutation 8.47s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 174 expanded)
%              Number of leaves         :   44 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 251 expanded)
%              Number of equality atoms :   64 ( 121 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_subset_1 > k4_subset_1 > k8_setfam_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_733,plain,(
    ! [A_109,B_110] :
      ( m1_subset_1(k7_setfam_1(A_109,B_110),k1_zfmisc_1(k1_zfmisc_1(A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_461,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k5_setfam_1(A_92,B_93),k1_zfmisc_1(A_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_475,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k5_setfam_1(A_92,B_93),A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(resolution,[status(thm)],[c_461,c_44])).

tff(c_746,plain,(
    ! [A_109,B_110] :
      ( r1_tarski(k5_setfam_1(A_109,k7_setfam_1(A_109,B_110)),A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(resolution,[status(thm)],[c_733,c_475])).

tff(c_52,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_925,plain,(
    ! [A_118,B_119] :
      ( k8_setfam_1(A_118,B_119) = k6_setfam_1(A_118,B_119)
      | k1_xboole_0 = B_119
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(A_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_947,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_925])).

tff(c_959,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_947])).

tff(c_607,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1(k8_setfam_1(A_101,B_102),k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(A_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_751,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k8_setfam_1(A_111,B_112),A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(resolution,[status(thm)],[c_607,c_44])).

tff(c_776,plain,(
    r1_tarski(k8_setfam_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_751])).

tff(c_964,plain,(
    r1_tarski(k6_setfam_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_776])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,B_54) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_14,c_124])).

tff(c_30,plain,(
    ! [A_23] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1014,plain,(
    ! [A_121,B_122,C_123] :
      ( k4_subset_1(A_121,B_122,C_123) = k2_xboole_0(B_122,C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(A_121))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2352,plain,(
    ! [B_184,B_185,A_186] :
      ( k4_subset_1(B_184,B_185,A_186) = k2_xboole_0(B_185,A_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(B_184))
      | ~ r1_tarski(A_186,B_184) ) ),
    inference(resolution,[status(thm)],[c_46,c_1014])).

tff(c_2372,plain,(
    ! [A_23,A_186] :
      ( k4_subset_1(A_23,k1_xboole_0,A_186) = k2_xboole_0(k1_xboole_0,A_186)
      | ~ r1_tarski(A_186,A_23) ) ),
    inference(resolution,[status(thm)],[c_30,c_2352])).

tff(c_2383,plain,(
    ! [A_187,A_188] :
      ( k4_subset_1(A_187,k1_xboole_0,A_188) = A_188
      | ~ r1_tarski(A_188,A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2372])).

tff(c_2430,plain,(
    k4_subset_1('#skF_1',k1_xboole_0,k6_setfam_1('#skF_1','#skF_2')) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_964,c_2383])).

tff(c_16,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_174])).

tff(c_186,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_183])).

tff(c_18,plain,(
    ! [A_10] : k1_subset_1(A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = k2_subset_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = k2_subset_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_26])).

tff(c_312,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k3_subset_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_324,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = k3_subset_1(A_23,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_312])).

tff(c_329,plain,(
    ! [A_23] : k2_subset_1(A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_59,c_324])).

tff(c_48,plain,(
    ! [A_36,B_37] :
      ( k7_subset_1(A_36,k2_subset_1(A_36),k6_setfam_1(A_36,B_37)) = k5_setfam_1(A_36,k7_setfam_1(A_36,B_37))
      | k1_xboole_0 = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1166,plain,(
    ! [A_127,B_128] :
      ( k7_subset_1(A_127,A_127,k6_setfam_1(A_127,B_128)) = k5_setfam_1(A_127,k7_setfam_1(A_127,B_128))
      | k1_xboole_0 = B_128
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k1_zfmisc_1(A_127))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_48])).

tff(c_1182,plain,
    ( k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_1166])).

tff(c_1193,plain,(
    k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1182])).

tff(c_245,plain,(
    ! [A_77,B_78] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,B_78)) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_253,plain,(
    ! [A_23] : k3_subset_1(A_23,k3_subset_1(A_23,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_245])).

tff(c_258,plain,(
    ! [A_23] : k3_subset_1(A_23,k2_subset_1(A_23)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_253])).

tff(c_330,plain,(
    ! [A_23] : k3_subset_1(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_258])).

tff(c_32,plain,(
    ! [A_24] :
      ( k8_setfam_1(A_24,k1_xboole_0) = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_58,plain,(
    ! [A_24] : k8_setfam_1(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_623,plain,(
    ! [A_24] :
      ( m1_subset_1(A_24,k1_zfmisc_1(A_24))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_607])).

tff(c_630,plain,(
    ! [A_24] : m1_subset_1(A_24,k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_623])).

tff(c_1313,plain,(
    ! [A_134,B_135,C_136] :
      ( k4_subset_1(A_134,k3_subset_1(A_134,B_135),C_136) = k3_subset_1(A_134,k7_subset_1(A_134,B_135,C_136))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_134))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7667,plain,(
    ! [B_325,B_326,A_327] :
      ( k4_subset_1(B_325,k3_subset_1(B_325,B_326),A_327) = k3_subset_1(B_325,k7_subset_1(B_325,B_326,A_327))
      | ~ m1_subset_1(B_326,k1_zfmisc_1(B_325))
      | ~ r1_tarski(A_327,B_325) ) ),
    inference(resolution,[status(thm)],[c_46,c_1313])).

tff(c_7677,plain,(
    ! [A_24,A_327] :
      ( k4_subset_1(A_24,k3_subset_1(A_24,A_24),A_327) = k3_subset_1(A_24,k7_subset_1(A_24,A_24,A_327))
      | ~ r1_tarski(A_327,A_24) ) ),
    inference(resolution,[status(thm)],[c_630,c_7667])).

tff(c_10595,plain,(
    ! [A_401,A_402] :
      ( k3_subset_1(A_401,k7_subset_1(A_401,A_401,A_402)) = k4_subset_1(A_401,k1_xboole_0,A_402)
      | ~ r1_tarski(A_402,A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_7677])).

tff(c_10654,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k4_subset_1('#skF_1',k1_xboole_0,k6_setfam_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k6_setfam_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_10595])).

tff(c_10674,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_2430,c_10654])).

tff(c_255,plain,(
    ! [B_35,A_34] :
      ( k3_subset_1(B_35,k3_subset_1(B_35,A_34)) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_46,c_245])).

tff(c_10759,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10674,c_255])).

tff(c_10763,plain,(
    ~ r1_tarski(k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10759])).

tff(c_10767,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_746,c_10763])).

tff(c_10774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:07:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.30/2.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.30/2.92  
% 8.30/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.30/2.92  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_subset_1 > k4_subset_1 > k8_setfam_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.30/2.92  
% 8.30/2.92  %Foreground sorts:
% 8.30/2.92  
% 8.30/2.92  
% 8.30/2.92  %Background operators:
% 8.30/2.92  
% 8.30/2.92  
% 8.30/2.92  %Foreground operators:
% 8.30/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.30/2.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.30/2.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.30/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.30/2.92  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 8.30/2.92  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 8.30/2.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.30/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.30/2.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.30/2.92  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.30/2.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.30/2.92  tff('#skF_2', type, '#skF_2': $i).
% 8.30/2.92  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.30/2.92  tff('#skF_1', type, '#skF_1': $i).
% 8.30/2.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.30/2.92  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 8.30/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.30/2.92  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 8.30/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.30/2.92  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 8.30/2.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.30/2.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.30/2.92  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.30/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.30/2.92  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.30/2.92  
% 8.47/2.94  tff(f_120, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 8.47/2.94  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 8.47/2.94  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 8.47/2.94  tff(f_99, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.47/2.94  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 8.47/2.94  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 8.47/2.94  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.47/2.94  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.47/2.94  tff(f_70, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.47/2.94  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.47/2.94  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.47/2.94  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 8.47/2.94  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.47/2.94  tff(f_45, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 8.47/2.94  tff(f_61, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 8.47/2.94  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.47/2.94  tff(f_106, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_setfam_1)).
% 8.47/2.94  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.47/2.94  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 8.47/2.94  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.47/2.94  tff(c_733, plain, (![A_109, B_110]: (m1_subset_1(k7_setfam_1(A_109, B_110), k1_zfmisc_1(k1_zfmisc_1(A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.47/2.94  tff(c_461, plain, (![A_92, B_93]: (m1_subset_1(k5_setfam_1(A_92, B_93), k1_zfmisc_1(A_92)) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.47/2.94  tff(c_44, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.47/2.94  tff(c_475, plain, (![A_92, B_93]: (r1_tarski(k5_setfam_1(A_92, B_93), A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(resolution, [status(thm)], [c_461, c_44])).
% 8.47/2.94  tff(c_746, plain, (![A_109, B_110]: (r1_tarski(k5_setfam_1(A_109, k7_setfam_1(A_109, B_110)), A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(resolution, [status(thm)], [c_733, c_475])).
% 8.47/2.94  tff(c_52, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.47/2.94  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.47/2.94  tff(c_925, plain, (![A_118, B_119]: (k8_setfam_1(A_118, B_119)=k6_setfam_1(A_118, B_119) | k1_xboole_0=B_119 | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(A_118))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.47/2.94  tff(c_947, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_56, c_925])).
% 8.47/2.94  tff(c_959, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_947])).
% 8.47/2.94  tff(c_607, plain, (![A_101, B_102]: (m1_subset_1(k8_setfam_1(A_101, B_102), k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(k1_zfmisc_1(A_101))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.47/2.94  tff(c_751, plain, (![A_111, B_112]: (r1_tarski(k8_setfam_1(A_111, B_112), A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(resolution, [status(thm)], [c_607, c_44])).
% 8.47/2.94  tff(c_776, plain, (r1_tarski(k8_setfam_1('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_56, c_751])).
% 8.47/2.94  tff(c_964, plain, (r1_tarski(k6_setfam_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_959, c_776])).
% 8.47/2.94  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.47/2.94  tff(c_124, plain, (![A_53, B_54]: (k2_xboole_0(A_53, B_54)=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.47/2.94  tff(c_136, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_14, c_124])).
% 8.47/2.94  tff(c_30, plain, (![A_23]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.47/2.94  tff(c_46, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.47/2.94  tff(c_1014, plain, (![A_121, B_122, C_123]: (k4_subset_1(A_121, B_122, C_123)=k2_xboole_0(B_122, C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(A_121)) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.47/2.94  tff(c_2352, plain, (![B_184, B_185, A_186]: (k4_subset_1(B_184, B_185, A_186)=k2_xboole_0(B_185, A_186) | ~m1_subset_1(B_185, k1_zfmisc_1(B_184)) | ~r1_tarski(A_186, B_184))), inference(resolution, [status(thm)], [c_46, c_1014])).
% 8.47/2.94  tff(c_2372, plain, (![A_23, A_186]: (k4_subset_1(A_23, k1_xboole_0, A_186)=k2_xboole_0(k1_xboole_0, A_186) | ~r1_tarski(A_186, A_23))), inference(resolution, [status(thm)], [c_30, c_2352])).
% 8.47/2.94  tff(c_2383, plain, (![A_187, A_188]: (k4_subset_1(A_187, k1_xboole_0, A_188)=A_188 | ~r1_tarski(A_188, A_187))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2372])).
% 8.47/2.94  tff(c_2430, plain, (k4_subset_1('#skF_1', k1_xboole_0, k6_setfam_1('#skF_1', '#skF_2'))=k6_setfam_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_964, c_2383])).
% 8.47/2.94  tff(c_16, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.47/2.94  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.47/2.94  tff(c_174, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.47/2.94  tff(c_183, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_174])).
% 8.47/2.94  tff(c_186, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_183])).
% 8.47/2.94  tff(c_18, plain, (![A_10]: (k1_subset_1(A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.47/2.94  tff(c_26, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=k2_subset_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.47/2.94  tff(c_59, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=k2_subset_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_26])).
% 8.47/2.94  tff(c_312, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k3_subset_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.47/2.94  tff(c_324, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=k3_subset_1(A_23, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_312])).
% 8.47/2.94  tff(c_329, plain, (![A_23]: (k2_subset_1(A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_59, c_324])).
% 8.47/2.94  tff(c_48, plain, (![A_36, B_37]: (k7_subset_1(A_36, k2_subset_1(A_36), k6_setfam_1(A_36, B_37))=k5_setfam_1(A_36, k7_setfam_1(A_36, B_37)) | k1_xboole_0=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.47/2.94  tff(c_1166, plain, (![A_127, B_128]: (k7_subset_1(A_127, A_127, k6_setfam_1(A_127, B_128))=k5_setfam_1(A_127, k7_setfam_1(A_127, B_128)) | k1_xboole_0=B_128 | ~m1_subset_1(B_128, k1_zfmisc_1(k1_zfmisc_1(A_127))))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_48])).
% 8.47/2.94  tff(c_1182, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_56, c_1166])).
% 8.47/2.94  tff(c_1193, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1182])).
% 8.47/2.94  tff(c_245, plain, (![A_77, B_78]: (k3_subset_1(A_77, k3_subset_1(A_77, B_78))=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.47/2.94  tff(c_253, plain, (![A_23]: (k3_subset_1(A_23, k3_subset_1(A_23, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_245])).
% 8.47/2.94  tff(c_258, plain, (![A_23]: (k3_subset_1(A_23, k2_subset_1(A_23))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_253])).
% 8.47/2.94  tff(c_330, plain, (![A_23]: (k3_subset_1(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_329, c_258])).
% 8.47/2.94  tff(c_32, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.47/2.94  tff(c_58, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 8.47/2.94  tff(c_623, plain, (![A_24]: (m1_subset_1(A_24, k1_zfmisc_1(A_24)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(superposition, [status(thm), theory('equality')], [c_58, c_607])).
% 8.47/2.94  tff(c_630, plain, (![A_24]: (m1_subset_1(A_24, k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_623])).
% 8.47/2.94  tff(c_1313, plain, (![A_134, B_135, C_136]: (k4_subset_1(A_134, k3_subset_1(A_134, B_135), C_136)=k3_subset_1(A_134, k7_subset_1(A_134, B_135, C_136)) | ~m1_subset_1(C_136, k1_zfmisc_1(A_134)) | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.47/2.94  tff(c_7667, plain, (![B_325, B_326, A_327]: (k4_subset_1(B_325, k3_subset_1(B_325, B_326), A_327)=k3_subset_1(B_325, k7_subset_1(B_325, B_326, A_327)) | ~m1_subset_1(B_326, k1_zfmisc_1(B_325)) | ~r1_tarski(A_327, B_325))), inference(resolution, [status(thm)], [c_46, c_1313])).
% 8.47/2.94  tff(c_7677, plain, (![A_24, A_327]: (k4_subset_1(A_24, k3_subset_1(A_24, A_24), A_327)=k3_subset_1(A_24, k7_subset_1(A_24, A_24, A_327)) | ~r1_tarski(A_327, A_24))), inference(resolution, [status(thm)], [c_630, c_7667])).
% 8.47/2.94  tff(c_10595, plain, (![A_401, A_402]: (k3_subset_1(A_401, k7_subset_1(A_401, A_401, A_402))=k4_subset_1(A_401, k1_xboole_0, A_402) | ~r1_tarski(A_402, A_401))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_7677])).
% 8.47/2.94  tff(c_10654, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k4_subset_1('#skF_1', k1_xboole_0, k6_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(k6_setfam_1('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1193, c_10595])).
% 8.47/2.94  tff(c_10674, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_964, c_2430, c_10654])).
% 8.47/2.94  tff(c_255, plain, (![B_35, A_34]: (k3_subset_1(B_35, k3_subset_1(B_35, A_34))=A_34 | ~r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_46, c_245])).
% 8.47/2.94  tff(c_10759, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10674, c_255])).
% 8.47/2.94  tff(c_10763, plain, (~r1_tarski(k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_10759])).
% 8.47/2.94  tff(c_10767, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_746, c_10763])).
% 8.47/2.94  tff(c_10774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_10767])).
% 8.47/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.47/2.94  
% 8.47/2.94  Inference rules
% 8.47/2.94  ----------------------
% 8.47/2.94  #Ref     : 0
% 8.47/2.94  #Sup     : 2526
% 8.47/2.94  #Fact    : 0
% 8.47/2.94  #Define  : 0
% 8.47/2.94  #Split   : 7
% 8.47/2.94  #Chain   : 0
% 8.47/2.94  #Close   : 0
% 8.47/2.94  
% 8.47/2.94  Ordering : KBO
% 8.47/2.94  
% 8.47/2.94  Simplification rules
% 8.47/2.94  ----------------------
% 8.47/2.94  #Subsume      : 216
% 8.47/2.94  #Demod        : 2629
% 8.47/2.94  #Tautology    : 1525
% 8.47/2.94  #SimpNegUnit  : 6
% 8.47/2.94  #BackRed      : 17
% 8.47/2.94  
% 8.47/2.94  #Partial instantiations: 0
% 8.47/2.94  #Strategies tried      : 1
% 8.47/2.94  
% 8.47/2.94  Timing (in seconds)
% 8.47/2.94  ----------------------
% 8.47/2.94  Preprocessing        : 0.33
% 8.47/2.94  Parsing              : 0.18
% 8.47/2.94  CNF conversion       : 0.02
% 8.47/2.94  Main loop            : 1.85
% 8.47/2.94  Inferencing          : 0.53
% 8.47/2.94  Reduction            : 0.70
% 8.47/2.94  Demodulation         : 0.54
% 8.47/2.94  BG Simplification    : 0.06
% 8.47/2.94  Subsumption          : 0.43
% 8.47/2.94  Abstraction          : 0.08
% 8.47/2.94  MUC search           : 0.00
% 8.47/2.94  Cooper               : 0.00
% 8.47/2.94  Total                : 2.22
% 8.47/2.94  Index Insertion      : 0.00
% 8.47/2.94  Index Deletion       : 0.00
% 8.47/2.94  Index Matching       : 0.00
% 8.47/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
