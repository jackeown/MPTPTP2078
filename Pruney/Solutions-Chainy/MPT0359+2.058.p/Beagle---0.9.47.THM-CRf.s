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
% DateTime   : Thu Dec  3 09:56:16 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 462 expanded)
%              Number of leaves         :   43 ( 172 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 724 expanded)
%              Number of equality atoms :   44 ( 194 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_84,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_199,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_190])).

tff(c_202,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_199])).

tff(c_42,plain,(
    ! [A_51] : r1_tarski(k1_tarski(A_51),k1_zfmisc_1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_176,plain,(
    ! [B_82,C_83,A_84] :
      ( r2_hidden(B_82,C_83)
      | ~ r1_tarski(k2_tarski(A_84,B_82),C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_180,plain,(
    ! [A_85,C_86] :
      ( r2_hidden(A_85,C_86)
      | ~ r1_tarski(k1_tarski(A_85),C_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_176])).

tff(c_185,plain,(
    ! [A_87] : r2_hidden(A_87,k1_zfmisc_1(A_87)) ),
    inference(resolution,[status(thm)],[c_42,c_180])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    ! [A_87] : ~ v1_xboole_0(k1_zfmisc_1(A_87)) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_184,plain,(
    ! [A_51] : r2_hidden(A_51,k1_zfmisc_1(A_51)) ),
    inference(resolution,[status(thm)],[c_42,c_180])).

tff(c_211,plain,(
    ! [B_92,A_93] :
      ( m1_subset_1(B_92,A_93)
      | ~ r2_hidden(B_92,A_93)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_214,plain,(
    ! [A_51] :
      ( m1_subset_1(A_51,k1_zfmisc_1(A_51))
      | v1_xboole_0(k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_184,c_211])).

tff(c_220,plain,(
    ! [A_51] : m1_subset_1(A_51,k1_zfmisc_1(A_51)) ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_214])).

tff(c_255,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = k3_subset_1(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_262,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k3_subset_1(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_220,c_255])).

tff(c_271,plain,(
    ! [A_51] : k3_subset_1(A_51,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_262])).

tff(c_52,plain,(
    ! [A_54] : k2_subset_1(A_54) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,
    ( k2_subset_1('#skF_2') != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_73,plain,
    ( '#skF_2' != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_66])).

tff(c_121,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_72,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | k2_subset_1('#skF_2') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_74,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_72])).

tff(c_136,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_74])).

tff(c_137,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_121])).

tff(c_330,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_137])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_330])).

tff(c_334,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k3_subset_1(A_57,B_58),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_393,plain,(
    ! [B_121,C_122,A_123] :
      ( r2_hidden(B_121,C_122)
      | ~ r1_tarski(k2_tarski(A_123,B_121),C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_397,plain,(
    ! [A_124,C_125] :
      ( r2_hidden(A_124,C_125)
      | ~ r1_tarski(k1_tarski(A_124),C_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_393])).

tff(c_402,plain,(
    ! [A_126] : r2_hidden(A_126,k1_zfmisc_1(A_126)) ),
    inference(resolution,[status(thm)],[c_42,c_397])).

tff(c_406,plain,(
    ! [A_126] : ~ v1_xboole_0(k1_zfmisc_1(A_126)) ),
    inference(resolution,[status(thm)],[c_402,c_2])).

tff(c_401,plain,(
    ! [A_51] : r2_hidden(A_51,k1_zfmisc_1(A_51)) ),
    inference(resolution,[status(thm)],[c_42,c_397])).

tff(c_432,plain,(
    ! [B_134,A_135] :
      ( m1_subset_1(B_134,A_135)
      | ~ r2_hidden(B_134,A_135)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_435,plain,(
    ! [A_51] :
      ( m1_subset_1(A_51,k1_zfmisc_1(A_51))
      | v1_xboole_0(k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_401,c_432])).

tff(c_444,plain,(
    ! [A_51] : m1_subset_1(A_51,k1_zfmisc_1(A_51)) ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_435])).

tff(c_412,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k3_xboole_0(A_131,B_132)) = k4_xboole_0(A_131,B_132) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_421,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_412])).

tff(c_424,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_421])).

tff(c_466,plain,(
    ! [A_141,B_142] :
      ( k4_xboole_0(A_141,B_142) = k3_subset_1(A_141,B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_473,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k3_subset_1(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_444,c_466])).

tff(c_485,plain,(
    ! [A_51] : k3_subset_1(A_51,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_473])).

tff(c_1100,plain,(
    ! [A_163,B_164] :
      ( m1_subset_1(k3_subset_1(A_163,B_164),k1_zfmisc_1(A_163))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(A_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1117,plain,(
    ! [A_51] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_51))
      | ~ m1_subset_1(A_51,k1_zfmisc_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_1100])).

tff(c_1124,plain,(
    ! [A_51] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_1117])).

tff(c_985,plain,(
    ! [A_158,B_159] :
      ( k3_subset_1(A_158,k3_subset_1(A_158,B_159)) = B_159
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_990,plain,(
    ! [A_51] : k3_subset_1(A_51,k3_subset_1(A_51,A_51)) = A_51 ),
    inference(resolution,[status(thm)],[c_444,c_985])).

tff(c_1000,plain,(
    ! [A_51] : k3_subset_1(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_990])).

tff(c_2079,plain,(
    ! [A_193,B_194] :
      ( k1_subset_1(A_193) = B_194
      | ~ r1_tarski(B_194,k3_subset_1(A_193,B_194))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(A_193)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2092,plain,(
    ! [A_51] :
      ( k1_subset_1(A_51) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_51)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_2079])).

tff(c_2106,plain,(
    ! [A_51] : k1_subset_1(A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_12,c_2092])).

tff(c_335,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_1002,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_985])).

tff(c_2089,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_subset_1('#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_2079])).

tff(c_2104,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_subset_1('#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_2089])).

tff(c_4162,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_2104])).

tff(c_4163,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4162])).

tff(c_4166,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_4163])).

tff(c_4173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4166])).

tff(c_4174,plain,(
    k3_subset_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4162])).

tff(c_4188,plain,(
    k3_subset_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4174,c_1002])).

tff(c_4565,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4188,c_1000])).

tff(c_4576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_4565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:37 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.90/1.99  
% 4.90/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.00  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 5.23/2.00  
% 5.23/2.00  %Foreground sorts:
% 5.23/2.00  
% 5.23/2.00  
% 5.23/2.00  %Background operators:
% 5.23/2.00  
% 5.23/2.00  
% 5.23/2.00  %Foreground operators:
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.23/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.23/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.23/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.23/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.23/2.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.23/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.23/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.23/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.23/2.00  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.23/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.23/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.23/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.23/2.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.23/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/2.00  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/2.00  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.23/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/2.00  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.23/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.23/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.23/2.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.23/2.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.23/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.23/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/2.00  
% 5.23/2.01  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.23/2.01  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.23/2.01  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.23/2.01  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.23/2.01  tff(f_69, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 5.23/2.01  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.23/2.01  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.23/2.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.23/2.01  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.23/2.01  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.23/2.01  tff(f_84, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.23/2.01  tff(f_109, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 5.23/2.01  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.23/2.01  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.23/2.01  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 5.23/2.01  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.23/2.01  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.23/2.01  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.23/2.01  tff(c_190, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.23/2.01  tff(c_199, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_190])).
% 5.23/2.01  tff(c_202, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_199])).
% 5.23/2.01  tff(c_42, plain, (![A_51]: (r1_tarski(k1_tarski(A_51), k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.23/2.01  tff(c_20, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.23/2.01  tff(c_176, plain, (![B_82, C_83, A_84]: (r2_hidden(B_82, C_83) | ~r1_tarski(k2_tarski(A_84, B_82), C_83))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.23/2.01  tff(c_180, plain, (![A_85, C_86]: (r2_hidden(A_85, C_86) | ~r1_tarski(k1_tarski(A_85), C_86))), inference(superposition, [status(thm), theory('equality')], [c_20, c_176])).
% 5.23/2.01  tff(c_185, plain, (![A_87]: (r2_hidden(A_87, k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_42, c_180])).
% 5.23/2.01  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.01  tff(c_189, plain, (![A_87]: (~v1_xboole_0(k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_185, c_2])).
% 5.23/2.01  tff(c_184, plain, (![A_51]: (r2_hidden(A_51, k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_42, c_180])).
% 5.23/2.01  tff(c_211, plain, (![B_92, A_93]: (m1_subset_1(B_92, A_93) | ~r2_hidden(B_92, A_93) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.23/2.01  tff(c_214, plain, (![A_51]: (m1_subset_1(A_51, k1_zfmisc_1(A_51)) | v1_xboole_0(k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_184, c_211])).
% 5.23/2.01  tff(c_220, plain, (![A_51]: (m1_subset_1(A_51, k1_zfmisc_1(A_51)))), inference(negUnitSimplification, [status(thm)], [c_189, c_214])).
% 5.23/2.01  tff(c_255, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=k3_subset_1(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.23/2.01  tff(c_262, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k3_subset_1(A_51, A_51))), inference(resolution, [status(thm)], [c_220, c_255])).
% 5.23/2.01  tff(c_271, plain, (![A_51]: (k3_subset_1(A_51, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_262])).
% 5.23/2.01  tff(c_52, plain, (![A_54]: (k2_subset_1(A_54)=A_54)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.23/2.01  tff(c_66, plain, (k2_subset_1('#skF_2')!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.23/2.01  tff(c_73, plain, ('#skF_2'!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_66])).
% 5.23/2.01  tff(c_121, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_73])).
% 5.23/2.01  tff(c_72, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | k2_subset_1('#skF_2')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.23/2.01  tff(c_74, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_72])).
% 5.23/2.01  tff(c_136, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_121, c_74])).
% 5.23/2.01  tff(c_137, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_121])).
% 5.23/2.01  tff(c_330, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_137])).
% 5.23/2.01  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_330])).
% 5.23/2.01  tff(c_334, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_73])).
% 5.23/2.01  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.23/2.01  tff(c_56, plain, (![A_57, B_58]: (m1_subset_1(k3_subset_1(A_57, B_58), k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.23/2.01  tff(c_393, plain, (![B_121, C_122, A_123]: (r2_hidden(B_121, C_122) | ~r1_tarski(k2_tarski(A_123, B_121), C_122))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.23/2.01  tff(c_397, plain, (![A_124, C_125]: (r2_hidden(A_124, C_125) | ~r1_tarski(k1_tarski(A_124), C_125))), inference(superposition, [status(thm), theory('equality')], [c_20, c_393])).
% 5.23/2.01  tff(c_402, plain, (![A_126]: (r2_hidden(A_126, k1_zfmisc_1(A_126)))), inference(resolution, [status(thm)], [c_42, c_397])).
% 5.23/2.01  tff(c_406, plain, (![A_126]: (~v1_xboole_0(k1_zfmisc_1(A_126)))), inference(resolution, [status(thm)], [c_402, c_2])).
% 5.23/2.01  tff(c_401, plain, (![A_51]: (r2_hidden(A_51, k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_42, c_397])).
% 5.23/2.01  tff(c_432, plain, (![B_134, A_135]: (m1_subset_1(B_134, A_135) | ~r2_hidden(B_134, A_135) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.23/2.01  tff(c_435, plain, (![A_51]: (m1_subset_1(A_51, k1_zfmisc_1(A_51)) | v1_xboole_0(k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_401, c_432])).
% 5.23/2.01  tff(c_444, plain, (![A_51]: (m1_subset_1(A_51, k1_zfmisc_1(A_51)))), inference(negUnitSimplification, [status(thm)], [c_406, c_435])).
% 5.23/2.01  tff(c_412, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k3_xboole_0(A_131, B_132))=k4_xboole_0(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.23/2.01  tff(c_421, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_412])).
% 5.23/2.01  tff(c_424, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_421])).
% 5.23/2.01  tff(c_466, plain, (![A_141, B_142]: (k4_xboole_0(A_141, B_142)=k3_subset_1(A_141, B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.23/2.01  tff(c_473, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k3_subset_1(A_51, A_51))), inference(resolution, [status(thm)], [c_444, c_466])).
% 5.23/2.01  tff(c_485, plain, (![A_51]: (k3_subset_1(A_51, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_424, c_473])).
% 5.23/2.01  tff(c_1100, plain, (![A_163, B_164]: (m1_subset_1(k3_subset_1(A_163, B_164), k1_zfmisc_1(A_163)) | ~m1_subset_1(B_164, k1_zfmisc_1(A_163)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.23/2.01  tff(c_1117, plain, (![A_51]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_51)) | ~m1_subset_1(A_51, k1_zfmisc_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_485, c_1100])).
% 5.23/2.01  tff(c_1124, plain, (![A_51]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_51)))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_1117])).
% 5.23/2.01  tff(c_985, plain, (![A_158, B_159]: (k3_subset_1(A_158, k3_subset_1(A_158, B_159))=B_159 | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.23/2.01  tff(c_990, plain, (![A_51]: (k3_subset_1(A_51, k3_subset_1(A_51, A_51))=A_51)), inference(resolution, [status(thm)], [c_444, c_985])).
% 5.23/2.01  tff(c_1000, plain, (![A_51]: (k3_subset_1(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_485, c_990])).
% 5.23/2.01  tff(c_2079, plain, (![A_193, B_194]: (k1_subset_1(A_193)=B_194 | ~r1_tarski(B_194, k3_subset_1(A_193, B_194)) | ~m1_subset_1(B_194, k1_zfmisc_1(A_193)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.23/2.01  tff(c_2092, plain, (![A_51]: (k1_subset_1(A_51)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_51) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_2079])).
% 5.23/2.01  tff(c_2106, plain, (![A_51]: (k1_subset_1(A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_12, c_2092])).
% 5.23/2.01  tff(c_335, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_73])).
% 5.23/2.01  tff(c_1002, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_64, c_985])).
% 5.23/2.01  tff(c_2089, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_subset_1('#skF_2') | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_2079])).
% 5.23/2.01  tff(c_2104, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_subset_1('#skF_2') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_2089])).
% 5.23/2.01  tff(c_4162, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_2104])).
% 5.23/2.01  tff(c_4163, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4162])).
% 5.23/2.01  tff(c_4166, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_4163])).
% 5.23/2.01  tff(c_4173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_4166])).
% 5.23/2.01  tff(c_4174, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4162])).
% 5.23/2.01  tff(c_4188, plain, (k3_subset_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4174, c_1002])).
% 5.23/2.01  tff(c_4565, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4188, c_1000])).
% 5.23/2.01  tff(c_4576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_4565])).
% 5.23/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/2.01  
% 5.23/2.01  Inference rules
% 5.23/2.01  ----------------------
% 5.23/2.01  #Ref     : 0
% 5.23/2.01  #Sup     : 1118
% 5.23/2.01  #Fact    : 0
% 5.23/2.01  #Define  : 0
% 5.23/2.01  #Split   : 6
% 5.23/2.01  #Chain   : 0
% 5.23/2.01  #Close   : 0
% 5.23/2.01  
% 5.23/2.01  Ordering : KBO
% 5.23/2.01  
% 5.23/2.01  Simplification rules
% 5.23/2.01  ----------------------
% 5.23/2.01  #Subsume      : 16
% 5.23/2.01  #Demod        : 859
% 5.23/2.01  #Tautology    : 687
% 5.23/2.01  #SimpNegUnit  : 8
% 5.23/2.01  #BackRed      : 25
% 5.23/2.01  
% 5.23/2.01  #Partial instantiations: 0
% 5.23/2.01  #Strategies tried      : 1
% 5.23/2.01  
% 5.23/2.01  Timing (in seconds)
% 5.23/2.01  ----------------------
% 5.23/2.01  Preprocessing        : 0.34
% 5.23/2.01  Parsing              : 0.18
% 5.23/2.01  CNF conversion       : 0.02
% 5.23/2.01  Main loop            : 0.89
% 5.23/2.02  Inferencing          : 0.28
% 5.23/2.02  Reduction            : 0.39
% 5.23/2.02  Demodulation         : 0.32
% 5.23/2.02  BG Simplification    : 0.04
% 5.23/2.02  Subsumption          : 0.13
% 5.23/2.02  Abstraction          : 0.05
% 5.23/2.02  MUC search           : 0.00
% 5.23/2.02  Cooper               : 0.00
% 5.23/2.02  Total                : 1.26
% 5.23/2.02  Index Insertion      : 0.00
% 5.23/2.02  Index Deletion       : 0.00
% 5.23/2.02  Index Matching       : 0.00
% 5.23/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
