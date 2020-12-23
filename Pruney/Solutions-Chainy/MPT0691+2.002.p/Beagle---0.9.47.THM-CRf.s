%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:40 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 233 expanded)
%              Number of leaves         :   45 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  132 ( 355 expanded)
%              Number of equality atoms :   60 ( 120 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_162,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,B_76)
      | k4_xboole_0(A_75,B_76) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_166,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_162,c_54])).

tff(c_58,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_361,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_373,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_361])).

tff(c_376,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_373])).

tff(c_397,plain,(
    ! [A_98,B_99] : k4_xboole_0(A_98,k4_xboole_0(A_98,B_99)) = k3_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_412,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_397])).

tff(c_430,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_412])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_370,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_361])).

tff(c_472,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_370])).

tff(c_42,plain,(
    ! [B_52,A_51] :
      ( k2_relat_1(k7_relat_1(B_52,A_51)) = k9_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [B_55,A_54] :
      ( r1_tarski(k7_relat_1(B_55,A_54),B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_181,plain,(
    ! [A_82,B_83] :
      ( k2_xboole_0(A_82,B_83) = B_83
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [B_55,A_54] :
      ( k2_xboole_0(k7_relat_1(B_55,A_54),B_55) = B_55
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_46,c_181])).

tff(c_198,plain,(
    ! [B_55,A_54] :
      ( k2_xboole_0(B_55,k7_relat_1(B_55,A_54)) = B_55
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_184])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_713,plain,(
    ! [A_124,B_125] : k2_xboole_0(A_124,k2_xboole_0(A_124,B_125)) = k2_xboole_0(A_124,B_125) ),
    inference(resolution,[status(thm)],[c_20,c_181])).

tff(c_1659,plain,(
    ! [A_161,B_162] : k2_xboole_0(A_161,k2_xboole_0(B_162,A_161)) = k2_xboole_0(A_161,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_713])).

tff(c_95,plain,(
    ! [B_67,A_68] : k2_xboole_0(B_67,A_68) = k2_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    ! [A_68,B_67] : r1_tarski(A_68,k2_xboole_0(B_67,A_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_20])).

tff(c_218,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,B_85) = k1_xboole_0
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_240,plain,(
    ! [A_68,B_67] : k4_xboole_0(A_68,k2_xboole_0(B_67,A_68)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_218])).

tff(c_2117,plain,(
    ! [B_177,A_178] : k4_xboole_0(k2_xboole_0(B_177,A_178),k2_xboole_0(A_178,B_177)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1659,c_240])).

tff(c_2160,plain,(
    ! [B_55,A_54] :
      ( k4_xboole_0(k2_xboole_0(k7_relat_1(B_55,A_54),B_55),B_55) = k1_xboole_0
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_2117])).

tff(c_4822,plain,(
    ! [B_234,A_235] :
      ( k4_xboole_0(k2_xboole_0(B_234,k7_relat_1(B_234,A_235)),B_234) = k1_xboole_0
      | ~ v1_relat_1(B_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2160])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_576,plain,(
    ! [B_107,A_108] :
      ( v1_relat_1(B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_108))
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_581,plain,(
    ! [A_109,B_110] :
      ( v1_relat_1(A_109)
      | ~ v1_relat_1(B_110)
      | ~ r1_tarski(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_38,c_576])).

tff(c_1519,plain,(
    ! [A_156,B_157] :
      ( v1_relat_1(A_156)
      | ~ v1_relat_1(B_157)
      | k4_xboole_0(A_156,B_157) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_581])).

tff(c_1529,plain,(
    ! [A_158] :
      ( v1_relat_1(A_158)
      | k4_xboole_0(A_158,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_1519])).

tff(c_613,plain,(
    ! [A_68,B_67] :
      ( v1_relat_1(A_68)
      | ~ v1_relat_1(k2_xboole_0(B_67,A_68)) ) ),
    inference(resolution,[status(thm)],[c_110,c_581])).

tff(c_1546,plain,(
    ! [A_68,B_67] :
      ( v1_relat_1(A_68)
      | k4_xboole_0(k2_xboole_0(B_67,A_68),'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1529,c_613])).

tff(c_4839,plain,(
    ! [A_235] :
      ( v1_relat_1(k7_relat_1('#skF_2',A_235))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4822,c_1546])).

tff(c_4884,plain,(
    ! [A_235] : v1_relat_1(k7_relat_1('#skF_2',A_235)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4839])).

tff(c_56,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_777,plain,(
    ! [B_126,A_127] :
      ( k1_relat_1(k7_relat_1(B_126,A_127)) = A_127
      | ~ r1_tarski(A_127,k1_relat_1(B_126))
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_795,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_777])).

tff(c_804,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_795])).

tff(c_611,plain,(
    ! [B_55,A_54] :
      ( v1_relat_1(k7_relat_1(B_55,A_54))
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_46,c_581])).

tff(c_50,plain,(
    ! [A_58] :
      ( k7_relat_1(A_58,k1_relat_1(A_58)) = A_58
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_811,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_50])).

tff(c_889,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_892,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_611,c_889])).

tff(c_896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_892])).

tff(c_897,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_44,plain,(
    ! [A_53] :
      ( k10_relat_1(A_53,k2_relat_1(A_53)) = k1_relat_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1192,plain,(
    ! [A_142,C_143,B_144] :
      ( k3_xboole_0(A_142,k10_relat_1(C_143,B_144)) = k10_relat_1(k7_relat_1(C_143,A_142),B_144)
      | ~ v1_relat_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4961,plain,(
    ! [A_241,A_242] :
      ( k10_relat_1(k7_relat_1(A_241,A_242),k2_relat_1(A_241)) = k3_xboole_0(A_242,k1_relat_1(A_241))
      | ~ v1_relat_1(A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1192])).

tff(c_4987,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_4961])).

tff(c_4998,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4884,c_4884,c_4,c_804,c_4987])).

tff(c_5016,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4998])).

tff(c_5031,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5016])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1198,plain,(
    ! [A_142,C_143,B_144] :
      ( k5_xboole_0(A_142,k10_relat_1(k7_relat_1(C_143,A_142),B_144)) = k4_xboole_0(A_142,k10_relat_1(C_143,B_144))
      | ~ v1_relat_1(C_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_10])).

tff(c_5037,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5031,c_1198])).

tff(c_5047,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_472,c_5037])).

tff(c_5049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_5047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:04:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.97  
% 5.13/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.97  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.13/1.97  
% 5.13/1.97  %Foreground sorts:
% 5.13/1.97  
% 5.13/1.97  
% 5.13/1.97  %Background operators:
% 5.13/1.97  
% 5.13/1.97  
% 5.13/1.97  %Foreground operators:
% 5.13/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.13/1.97  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.13/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/1.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.13/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.13/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.13/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.13/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.13/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.13/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.13/1.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.13/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.13/1.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.13/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/1.97  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.13/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/1.97  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.13/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.13/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.13/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.13/1.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.13/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.13/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/1.97  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.13/1.97  
% 5.13/1.99  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.13/1.99  tff(f_105, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 5.13/1.99  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.13/1.99  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.13/1.99  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.13/1.99  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.13/1.99  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.13/1.99  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.13/1.99  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.13/1.99  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 5.13/1.99  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.13/1.99  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.13/1.99  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.13/1.99  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.13/1.99  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 5.13/1.99  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 5.13/1.99  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.13/1.99  tff(f_98, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.13/1.99  tff(c_162, plain, (![A_75, B_76]: (r1_tarski(A_75, B_76) | k4_xboole_0(A_75, B_76)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.13/1.99  tff(c_54, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.13/1.99  tff(c_166, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_162, c_54])).
% 5.13/1.99  tff(c_58, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.13/1.99  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.13/1.99  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.13/1.99  tff(c_361, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.13/1.99  tff(c_373, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_361])).
% 5.13/1.99  tff(c_376, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_373])).
% 5.13/1.99  tff(c_397, plain, (![A_98, B_99]: (k4_xboole_0(A_98, k4_xboole_0(A_98, B_99))=k3_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.13/1.99  tff(c_412, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_376, c_397])).
% 5.13/1.99  tff(c_430, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_412])).
% 5.13/1.99  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.13/1.99  tff(c_370, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_361])).
% 5.13/1.99  tff(c_472, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_430, c_370])).
% 5.13/1.99  tff(c_42, plain, (![B_52, A_51]: (k2_relat_1(k7_relat_1(B_52, A_51))=k9_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.13/1.99  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.13/1.99  tff(c_46, plain, (![B_55, A_54]: (r1_tarski(k7_relat_1(B_55, A_54), B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.13/1.99  tff(c_181, plain, (![A_82, B_83]: (k2_xboole_0(A_82, B_83)=B_83 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.13/1.99  tff(c_184, plain, (![B_55, A_54]: (k2_xboole_0(k7_relat_1(B_55, A_54), B_55)=B_55 | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_46, c_181])).
% 5.13/1.99  tff(c_198, plain, (![B_55, A_54]: (k2_xboole_0(B_55, k7_relat_1(B_55, A_54))=B_55 | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_184])).
% 5.13/1.99  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.13/1.99  tff(c_713, plain, (![A_124, B_125]: (k2_xboole_0(A_124, k2_xboole_0(A_124, B_125))=k2_xboole_0(A_124, B_125))), inference(resolution, [status(thm)], [c_20, c_181])).
% 5.13/1.99  tff(c_1659, plain, (![A_161, B_162]: (k2_xboole_0(A_161, k2_xboole_0(B_162, A_161))=k2_xboole_0(A_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_2, c_713])).
% 5.13/1.99  tff(c_95, plain, (![B_67, A_68]: (k2_xboole_0(B_67, A_68)=k2_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.13/1.99  tff(c_110, plain, (![A_68, B_67]: (r1_tarski(A_68, k2_xboole_0(B_67, A_68)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_20])).
% 5.13/1.99  tff(c_218, plain, (![A_84, B_85]: (k4_xboole_0(A_84, B_85)=k1_xboole_0 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.13/1.99  tff(c_240, plain, (![A_68, B_67]: (k4_xboole_0(A_68, k2_xboole_0(B_67, A_68))=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_218])).
% 5.13/1.99  tff(c_2117, plain, (![B_177, A_178]: (k4_xboole_0(k2_xboole_0(B_177, A_178), k2_xboole_0(A_178, B_177))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1659, c_240])).
% 5.13/1.99  tff(c_2160, plain, (![B_55, A_54]: (k4_xboole_0(k2_xboole_0(k7_relat_1(B_55, A_54), B_55), B_55)=k1_xboole_0 | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_198, c_2117])).
% 5.13/1.99  tff(c_4822, plain, (![B_234, A_235]: (k4_xboole_0(k2_xboole_0(B_234, k7_relat_1(B_234, A_235)), B_234)=k1_xboole_0 | ~v1_relat_1(B_234))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2160])).
% 5.13/1.99  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.13/1.99  tff(c_38, plain, (![A_46, B_47]: (m1_subset_1(A_46, k1_zfmisc_1(B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.13/1.99  tff(c_576, plain, (![B_107, A_108]: (v1_relat_1(B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(A_108)) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.13/1.99  tff(c_581, plain, (![A_109, B_110]: (v1_relat_1(A_109) | ~v1_relat_1(B_110) | ~r1_tarski(A_109, B_110))), inference(resolution, [status(thm)], [c_38, c_576])).
% 5.13/1.99  tff(c_1519, plain, (![A_156, B_157]: (v1_relat_1(A_156) | ~v1_relat_1(B_157) | k4_xboole_0(A_156, B_157)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_581])).
% 5.13/1.99  tff(c_1529, plain, (![A_158]: (v1_relat_1(A_158) | k4_xboole_0(A_158, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_1519])).
% 5.13/1.99  tff(c_613, plain, (![A_68, B_67]: (v1_relat_1(A_68) | ~v1_relat_1(k2_xboole_0(B_67, A_68)))), inference(resolution, [status(thm)], [c_110, c_581])).
% 5.13/1.99  tff(c_1546, plain, (![A_68, B_67]: (v1_relat_1(A_68) | k4_xboole_0(k2_xboole_0(B_67, A_68), '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1529, c_613])).
% 5.13/1.99  tff(c_4839, plain, (![A_235]: (v1_relat_1(k7_relat_1('#skF_2', A_235)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4822, c_1546])).
% 5.13/1.99  tff(c_4884, plain, (![A_235]: (v1_relat_1(k7_relat_1('#skF_2', A_235)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4839])).
% 5.13/1.99  tff(c_56, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.13/1.99  tff(c_777, plain, (![B_126, A_127]: (k1_relat_1(k7_relat_1(B_126, A_127))=A_127 | ~r1_tarski(A_127, k1_relat_1(B_126)) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.13/1.99  tff(c_795, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_777])).
% 5.13/1.99  tff(c_804, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_795])).
% 5.13/1.99  tff(c_611, plain, (![B_55, A_54]: (v1_relat_1(k7_relat_1(B_55, A_54)) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_46, c_581])).
% 5.13/1.99  tff(c_50, plain, (![A_58]: (k7_relat_1(A_58, k1_relat_1(A_58))=A_58 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.13/1.99  tff(c_811, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_804, c_50])).
% 5.13/1.99  tff(c_889, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_811])).
% 5.13/1.99  tff(c_892, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_611, c_889])).
% 5.13/1.99  tff(c_896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_892])).
% 5.13/1.99  tff(c_897, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_811])).
% 5.13/1.99  tff(c_44, plain, (![A_53]: (k10_relat_1(A_53, k2_relat_1(A_53))=k1_relat_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.13/1.99  tff(c_1192, plain, (![A_142, C_143, B_144]: (k3_xboole_0(A_142, k10_relat_1(C_143, B_144))=k10_relat_1(k7_relat_1(C_143, A_142), B_144) | ~v1_relat_1(C_143))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.13/1.99  tff(c_4961, plain, (![A_241, A_242]: (k10_relat_1(k7_relat_1(A_241, A_242), k2_relat_1(A_241))=k3_xboole_0(A_242, k1_relat_1(A_241)) | ~v1_relat_1(A_241) | ~v1_relat_1(A_241))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1192])).
% 5.13/1.99  tff(c_4987, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_897, c_4961])).
% 5.13/1.99  tff(c_4998, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4884, c_4884, c_4, c_804, c_4987])).
% 5.13/1.99  tff(c_5016, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_4998])).
% 5.13/1.99  tff(c_5031, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5016])).
% 5.13/1.99  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.13/1.99  tff(c_1198, plain, (![A_142, C_143, B_144]: (k5_xboole_0(A_142, k10_relat_1(k7_relat_1(C_143, A_142), B_144))=k4_xboole_0(A_142, k10_relat_1(C_143, B_144)) | ~v1_relat_1(C_143))), inference(superposition, [status(thm), theory('equality')], [c_1192, c_10])).
% 5.13/1.99  tff(c_5037, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5031, c_1198])).
% 5.13/1.99  tff(c_5047, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_472, c_5037])).
% 5.13/1.99  tff(c_5049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_5047])).
% 5.13/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.99  
% 5.13/1.99  Inference rules
% 5.13/1.99  ----------------------
% 5.13/1.99  #Ref     : 0
% 5.13/1.99  #Sup     : 1231
% 5.13/1.99  #Fact    : 0
% 5.13/1.99  #Define  : 0
% 5.13/1.99  #Split   : 3
% 5.13/1.99  #Chain   : 0
% 5.13/1.99  #Close   : 0
% 5.13/1.99  
% 5.13/1.99  Ordering : KBO
% 5.13/1.99  
% 5.13/1.99  Simplification rules
% 5.13/1.99  ----------------------
% 5.13/1.99  #Subsume      : 300
% 5.13/1.99  #Demod        : 1364
% 5.13/1.99  #Tautology    : 762
% 5.13/1.99  #SimpNegUnit  : 18
% 5.13/1.99  #BackRed      : 0
% 5.13/1.99  
% 5.13/1.99  #Partial instantiations: 0
% 5.13/1.99  #Strategies tried      : 1
% 5.13/1.99  
% 5.13/1.99  Timing (in seconds)
% 5.13/1.99  ----------------------
% 5.13/1.99  Preprocessing        : 0.32
% 5.13/1.99  Parsing              : 0.17
% 5.13/1.99  CNF conversion       : 0.02
% 5.13/1.99  Main loop            : 0.86
% 5.13/1.99  Inferencing          : 0.27
% 5.13/1.99  Reduction            : 0.38
% 5.13/1.99  Demodulation         : 0.30
% 5.13/1.99  BG Simplification    : 0.03
% 5.13/1.99  Subsumption          : 0.14
% 5.13/1.99  Abstraction          : 0.04
% 5.13/1.99  MUC search           : 0.00
% 5.13/1.99  Cooper               : 0.00
% 5.13/1.99  Total                : 1.22
% 5.13/1.99  Index Insertion      : 0.00
% 5.13/1.99  Index Deletion       : 0.00
% 5.13/1.99  Index Matching       : 0.00
% 5.13/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
