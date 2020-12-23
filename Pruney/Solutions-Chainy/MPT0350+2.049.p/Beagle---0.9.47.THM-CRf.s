%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:32 EST 2020

% Result     : Theorem 11.19s
% Output     : CNFRefutation 11.19s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 141 expanded)
%              Number of leaves         :   48 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 163 expanded)
%              Number of equality atoms :   60 (  84 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_100,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_62,plain,(
    ! [A_61] : k2_subset_1(A_61) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_72,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_75,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_72])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_560,plain,(
    ! [A_121,B_122] :
      ( k4_xboole_0(A_121,B_122) = k3_subset_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_573,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_560])).

tff(c_68,plain,(
    ! [A_66] : ~ v1_xboole_0(k1_zfmisc_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_335,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,A_107)
      | ~ m1_subset_1(B_106,A_107)
      | v1_xboole_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    ! [C_56,A_52] :
      ( r1_tarski(C_56,A_52)
      | ~ r2_hidden(C_56,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_342,plain,(
    ! [B_106,A_52] :
      ( r1_tarski(B_106,A_52)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_52))
      | v1_xboole_0(k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_335,c_40])).

tff(c_352,plain,(
    ! [B_110,A_111] :
      ( r1_tarski(B_110,A_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_111)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_342])).

tff(c_365,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_352])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_369,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_365,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_374,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k3_xboole_0(A_112,B_113)) = k4_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3601,plain,(
    ! [B_210,A_211] : k5_xboole_0(B_210,k3_xboole_0(A_211,B_210)) = k4_xboole_0(B_210,A_211) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_374])).

tff(c_3715,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_3601])).

tff(c_3756,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_3715])).

tff(c_4138,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3756])).

tff(c_155,plain,(
    ! [B_79,A_80] : k5_xboole_0(B_79,A_80) = k5_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_171,plain,(
    ! [A_80] : k5_xboole_0(k1_xboole_0,A_80) = A_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_20])).

tff(c_26,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_668,plain,(
    ! [A_126,B_127,C_128] : k5_xboole_0(k5_xboole_0(A_126,B_127),C_128) = k5_xboole_0(A_126,k5_xboole_0(B_127,C_128)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_732,plain,(
    ! [A_24,C_128] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_128)) = k5_xboole_0(k1_xboole_0,C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_668])).

tff(c_745,plain,(
    ! [A_24,C_128] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_128)) = C_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_732])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_406,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_374])).

tff(c_422,plain,(
    ! [A_117] : k4_xboole_0(A_117,A_117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_406])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_253,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = k1_xboole_0
      | ~ r1_xboole_0(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_257,plain,(
    ! [A_19,B_20] : k3_xboole_0(k4_xboole_0(A_19,B_20),B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_253])).

tff(c_443,plain,(
    ! [A_119] : k3_xboole_0(k1_xboole_0,A_119) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_257])).

tff(c_502,plain,(
    ! [A_120] : k3_xboole_0(A_120,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_443])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_510,plain,(
    ! [A_120] : k5_xboole_0(A_120,k1_xboole_0) = k4_xboole_0(A_120,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_14])).

tff(c_546,plain,(
    ! [A_120] : k4_xboole_0(A_120,k1_xboole_0) = A_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_510])).

tff(c_1103,plain,(
    ! [A_139,B_140] : k4_xboole_0(k2_xboole_0(A_139,B_140),k3_xboole_0(A_139,B_140)) = k5_xboole_0(A_139,B_140) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1139,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k5_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_1103])).

tff(c_258,plain,(
    ! [A_86,B_87] : k3_xboole_0(k4_xboole_0(A_86,B_87),B_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_253])).

tff(c_263,plain,(
    ! [B_87,A_86] : k3_xboole_0(B_87,k4_xboole_0(A_86,B_87)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_2])).

tff(c_1414,plain,(
    k3_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1139,c_263])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),k3_xboole_0(A_9,B_10)) = k5_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1568,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')),k1_xboole_0) = k5_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1414,c_12])).

tff(c_1575,plain,(
    k2_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_546,c_1568])).

tff(c_4348,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4138,c_1575])).

tff(c_66,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k3_subset_1(A_64,B_65),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4072,plain,(
    ! [A_216,B_217,C_218] :
      ( k4_subset_1(A_216,B_217,C_218) = k2_xboole_0(B_217,C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(A_216))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_216)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_29587,plain,(
    ! [A_428,B_429,B_430] :
      ( k4_subset_1(A_428,B_429,k3_subset_1(A_428,B_430)) = k2_xboole_0(B_429,k3_subset_1(A_428,B_430))
      | ~ m1_subset_1(B_429,k1_zfmisc_1(A_428))
      | ~ m1_subset_1(B_430,k1_zfmisc_1(A_428)) ) ),
    inference(resolution,[status(thm)],[c_66,c_4072])).

tff(c_30154,plain,(
    ! [B_433] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_433)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_433))
      | ~ m1_subset_1(B_433,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_74,c_29587])).

tff(c_30173,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_30154])).

tff(c_30181,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4348,c_30173])).

tff(c_30183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_30181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:50:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.19/5.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/5.31  
% 11.19/5.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/5.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.19/5.31  
% 11.19/5.31  %Foreground sorts:
% 11.19/5.31  
% 11.19/5.31  
% 11.19/5.31  %Background operators:
% 11.19/5.31  
% 11.19/5.31  
% 11.19/5.31  %Foreground operators:
% 11.19/5.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.19/5.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.19/5.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.19/5.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.19/5.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.19/5.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.19/5.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.19/5.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.19/5.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.19/5.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.19/5.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.19/5.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.19/5.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.19/5.31  tff('#skF_3', type, '#skF_3': $i).
% 11.19/5.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.19/5.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.19/5.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.19/5.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.19/5.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.19/5.31  tff('#skF_4', type, '#skF_4': $i).
% 11.19/5.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.19/5.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.19/5.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.19/5.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.19/5.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.19/5.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.19/5.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.19/5.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.19/5.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.19/5.31  
% 11.19/5.33  tff(f_89, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 11.19/5.33  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 11.19/5.33  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.19/5.33  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.19/5.33  tff(f_100, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.19/5.33  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.19/5.33  tff(f_72, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.19/5.33  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.19/5.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.19/5.33  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.19/5.33  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 11.19/5.33  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.19/5.33  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.19/5.33  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.19/5.33  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.19/5.33  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.19/5.33  tff(f_37, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 11.19/5.33  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.19/5.33  tff(f_106, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.19/5.33  tff(c_62, plain, (![A_61]: (k2_subset_1(A_61)=A_61)), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.19/5.33  tff(c_72, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.19/5.33  tff(c_75, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_72])).
% 11.19/5.33  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.19/5.33  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.19/5.33  tff(c_560, plain, (![A_121, B_122]: (k4_xboole_0(A_121, B_122)=k3_subset_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.19/5.33  tff(c_573, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_560])).
% 11.19/5.33  tff(c_68, plain, (![A_66]: (~v1_xboole_0(k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.19/5.33  tff(c_335, plain, (![B_106, A_107]: (r2_hidden(B_106, A_107) | ~m1_subset_1(B_106, A_107) | v1_xboole_0(A_107))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.19/5.33  tff(c_40, plain, (![C_56, A_52]: (r1_tarski(C_56, A_52) | ~r2_hidden(C_56, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.19/5.33  tff(c_342, plain, (![B_106, A_52]: (r1_tarski(B_106, A_52) | ~m1_subset_1(B_106, k1_zfmisc_1(A_52)) | v1_xboole_0(k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_335, c_40])).
% 11.19/5.33  tff(c_352, plain, (![B_110, A_111]: (r1_tarski(B_110, A_111) | ~m1_subset_1(B_110, k1_zfmisc_1(A_111)))), inference(negUnitSimplification, [status(thm)], [c_68, c_342])).
% 11.19/5.33  tff(c_365, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_352])).
% 11.19/5.33  tff(c_18, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.19/5.33  tff(c_369, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_365, c_18])).
% 11.19/5.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.19/5.33  tff(c_374, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k3_xboole_0(A_112, B_113))=k4_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.19/5.33  tff(c_3601, plain, (![B_210, A_211]: (k5_xboole_0(B_210, k3_xboole_0(A_211, B_210))=k4_xboole_0(B_210, A_211))), inference(superposition, [status(thm), theory('equality')], [c_2, c_374])).
% 11.19/5.33  tff(c_3715, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_369, c_3601])).
% 11.19/5.33  tff(c_3756, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_3715])).
% 11.19/5.33  tff(c_4138, plain, (k5_xboole_0('#skF_4', '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_3756])).
% 11.19/5.33  tff(c_155, plain, (![B_79, A_80]: (k5_xboole_0(B_79, A_80)=k5_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.19/5.33  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.19/5.33  tff(c_171, plain, (![A_80]: (k5_xboole_0(k1_xboole_0, A_80)=A_80)), inference(superposition, [status(thm), theory('equality')], [c_155, c_20])).
% 11.19/5.33  tff(c_26, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.19/5.33  tff(c_668, plain, (![A_126, B_127, C_128]: (k5_xboole_0(k5_xboole_0(A_126, B_127), C_128)=k5_xboole_0(A_126, k5_xboole_0(B_127, C_128)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.19/5.33  tff(c_732, plain, (![A_24, C_128]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_128))=k5_xboole_0(k1_xboole_0, C_128))), inference(superposition, [status(thm), theory('equality')], [c_26, c_668])).
% 11.19/5.33  tff(c_745, plain, (![A_24, C_128]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_128))=C_128)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_732])).
% 11.19/5.33  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.19/5.33  tff(c_406, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_374])).
% 11.19/5.33  tff(c_422, plain, (![A_117]: (k4_xboole_0(A_117, A_117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_406])).
% 11.19/5.33  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.19/5.33  tff(c_253, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=k1_xboole_0 | ~r1_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.19/5.33  tff(c_257, plain, (![A_19, B_20]: (k3_xboole_0(k4_xboole_0(A_19, B_20), B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_253])).
% 11.19/5.33  tff(c_443, plain, (![A_119]: (k3_xboole_0(k1_xboole_0, A_119)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_422, c_257])).
% 11.19/5.33  tff(c_502, plain, (![A_120]: (k3_xboole_0(A_120, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_443])).
% 11.19/5.33  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.19/5.33  tff(c_510, plain, (![A_120]: (k5_xboole_0(A_120, k1_xboole_0)=k4_xboole_0(A_120, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_502, c_14])).
% 11.19/5.33  tff(c_546, plain, (![A_120]: (k4_xboole_0(A_120, k1_xboole_0)=A_120)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_510])).
% 11.19/5.33  tff(c_1103, plain, (![A_139, B_140]: (k4_xboole_0(k2_xboole_0(A_139, B_140), k3_xboole_0(A_139, B_140))=k5_xboole_0(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.19/5.33  tff(c_1139, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k5_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_369, c_1103])).
% 11.19/5.33  tff(c_258, plain, (![A_86, B_87]: (k3_xboole_0(k4_xboole_0(A_86, B_87), B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_253])).
% 11.19/5.33  tff(c_263, plain, (![B_87, A_86]: (k3_xboole_0(B_87, k4_xboole_0(A_86, B_87))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_258, c_2])).
% 11.19/5.33  tff(c_1414, plain, (k3_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1139, c_263])).
% 11.19/5.33  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), k3_xboole_0(A_9, B_10))=k5_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.19/5.33  tff(c_1568, plain, (k4_xboole_0(k2_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3')), k1_xboole_0)=k5_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1414, c_12])).
% 11.19/5.33  tff(c_1575, plain, (k2_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_745, c_546, c_1568])).
% 11.19/5.33  tff(c_4348, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4138, c_1575])).
% 11.19/5.33  tff(c_66, plain, (![A_64, B_65]: (m1_subset_1(k3_subset_1(A_64, B_65), k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.19/5.33  tff(c_4072, plain, (![A_216, B_217, C_218]: (k4_subset_1(A_216, B_217, C_218)=k2_xboole_0(B_217, C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(A_216)) | ~m1_subset_1(B_217, k1_zfmisc_1(A_216)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.19/5.33  tff(c_29587, plain, (![A_428, B_429, B_430]: (k4_subset_1(A_428, B_429, k3_subset_1(A_428, B_430))=k2_xboole_0(B_429, k3_subset_1(A_428, B_430)) | ~m1_subset_1(B_429, k1_zfmisc_1(A_428)) | ~m1_subset_1(B_430, k1_zfmisc_1(A_428)))), inference(resolution, [status(thm)], [c_66, c_4072])).
% 11.19/5.33  tff(c_30154, plain, (![B_433]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_433))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_433)) | ~m1_subset_1(B_433, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_74, c_29587])).
% 11.19/5.33  tff(c_30173, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_30154])).
% 11.19/5.33  tff(c_30181, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4348, c_30173])).
% 11.19/5.33  tff(c_30183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_30181])).
% 11.19/5.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/5.33  
% 11.19/5.33  Inference rules
% 11.19/5.33  ----------------------
% 11.19/5.33  #Ref     : 0
% 11.19/5.33  #Sup     : 7619
% 11.19/5.33  #Fact    : 0
% 11.19/5.33  #Define  : 0
% 11.19/5.33  #Split   : 0
% 11.19/5.33  #Chain   : 0
% 11.19/5.33  #Close   : 0
% 11.19/5.33  
% 11.19/5.33  Ordering : KBO
% 11.19/5.33  
% 11.19/5.33  Simplification rules
% 11.19/5.33  ----------------------
% 11.19/5.33  #Subsume      : 128
% 11.19/5.33  #Demod        : 9713
% 11.19/5.33  #Tautology    : 4875
% 11.19/5.33  #SimpNegUnit  : 14
% 11.19/5.33  #BackRed      : 8
% 11.19/5.33  
% 11.19/5.33  #Partial instantiations: 0
% 11.19/5.33  #Strategies tried      : 1
% 11.19/5.33  
% 11.19/5.33  Timing (in seconds)
% 11.19/5.33  ----------------------
% 11.19/5.33  Preprocessing        : 0.35
% 11.19/5.33  Parsing              : 0.18
% 11.19/5.33  CNF conversion       : 0.02
% 11.39/5.33  Main loop            : 4.22
% 11.39/5.33  Inferencing          : 0.69
% 11.39/5.33  Reduction            : 2.60
% 11.39/5.33  Demodulation         : 2.36
% 11.39/5.33  BG Simplification    : 0.09
% 11.39/5.33  Subsumption          : 0.65
% 11.39/5.33  Abstraction          : 0.13
% 11.39/5.33  MUC search           : 0.00
% 11.39/5.33  Cooper               : 0.00
% 11.39/5.33  Total                : 4.60
% 11.39/5.33  Index Insertion      : 0.00
% 11.39/5.33  Index Deletion       : 0.00
% 11.39/5.33  Index Matching       : 0.00
% 11.39/5.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
