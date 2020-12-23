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
% DateTime   : Thu Dec  3 09:59:18 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 276 expanded)
%              Number of leaves         :   47 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 400 expanded)
%              Number of equality atoms :   83 ( 212 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2542,plain,(
    ! [A_304,B_305] : k5_xboole_0(A_304,k3_xboole_0(A_304,B_305)) = k4_xboole_0(A_304,B_305) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2554,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2542])).

tff(c_2564,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2554])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2560,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2542])).

tff(c_2607,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2564,c_2560])).

tff(c_66,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_129,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_1'(A_55),A_55)
      | v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_148,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(k1_tarski(A_95),B_96)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,(
    ! [A_97] :
      ( k1_tarski(A_97) = k1_xboole_0
      | ~ r2_hidden(A_97,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_148,c_12])).

tff(c_159,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_154])).

tff(c_160,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_54,plain,(
    ! [A_73,B_74] :
      ( v1_relat_1(k5_relat_1(A_73,B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_224,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_233,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_224])).

tff(c_242,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_233])).

tff(c_239,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_224])).

tff(c_273,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_239])).

tff(c_415,plain,(
    ! [A_131,C_132,B_133] : k4_xboole_0(k2_zfmisc_1(A_131,C_132),k2_zfmisc_1(B_133,C_132)) = k2_zfmisc_1(k4_xboole_0(A_131,B_133),C_132) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_422,plain,(
    ! [B_133,C_132] : k2_zfmisc_1(k4_xboole_0(B_133,B_133),C_132) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_273])).

tff(c_431,plain,(
    ! [C_132] : k2_zfmisc_1(k1_xboole_0,C_132) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_422])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_62,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1090,plain,(
    ! [A_180,B_181] :
      ( k1_relat_1(k5_relat_1(A_180,B_181)) = k1_relat_1(A_180)
      | ~ r1_tarski(k2_relat_1(A_180),k1_relat_1(B_181))
      | ~ v1_relat_1(B_181)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1096,plain,(
    ! [B_181] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_181)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_181))
      | ~ v1_relat_1(B_181)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1090])).

tff(c_1101,plain,(
    ! [B_182] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_182)) = k1_xboole_0
      | ~ v1_relat_1(B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_10,c_64,c_1096])).

tff(c_56,plain,(
    ! [A_75] :
      ( k3_xboole_0(A_75,k2_zfmisc_1(k1_relat_1(A_75),k2_relat_1(A_75))) = A_75
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1113,plain,(
    ! [B_182] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_182),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_182)))) = k5_relat_1(k1_xboole_0,B_182)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_182))
      | ~ v1_relat_1(B_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_56])).

tff(c_1121,plain,(
    ! [B_183] :
      ( k5_relat_1(k1_xboole_0,B_183) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_183))
      | ~ v1_relat_1(B_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_431,c_1113])).

tff(c_1125,plain,(
    ! [B_74] :
      ( k5_relat_1(k1_xboole_0,B_74) = k1_xboole_0
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_54,c_1121])).

tff(c_1129,plain,(
    ! [B_184] :
      ( k5_relat_1(k1_xboole_0,B_184) = k1_xboole_0
      | ~ v1_relat_1(B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_1125])).

tff(c_1138,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_1129])).

tff(c_1144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_1138])).

tff(c_1145,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_42,plain,(
    ! [B_52] : k4_xboole_0(k1_tarski(B_52),k1_tarski(B_52)) != k1_tarski(B_52) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1153,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_42])).

tff(c_1160,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_1145,c_1153])).

tff(c_1283,plain,(
    ! [A_199,B_200] : k5_xboole_0(A_199,k3_xboole_0(A_199,B_200)) = k4_xboole_0(A_199,B_200) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1318,plain,(
    ! [A_202] : k5_xboole_0(A_202,k1_xboole_0) = k4_xboole_0(A_202,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1283])).

tff(c_1298,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1283])).

tff(c_1309,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1298])).

tff(c_1325,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1318,c_1309])).

tff(c_1335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1160,c_1325])).

tff(c_1336,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1443,plain,(
    ! [A_222,B_223] :
      ( r1_tarski(k1_tarski(A_222),B_223)
      | ~ r2_hidden(A_222,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1453,plain,(
    ! [A_224] :
      ( k1_tarski(A_224) = k1_xboole_0
      | ~ r2_hidden(A_224,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1443,c_12])).

tff(c_1458,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_1453])).

tff(c_1465,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1458])).

tff(c_1466,plain,(
    ! [A_227,B_228] : k5_xboole_0(A_227,k3_xboole_0(A_227,B_228)) = k4_xboole_0(A_227,B_228) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1478,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1466])).

tff(c_1488,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1478])).

tff(c_1484,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1466])).

tff(c_1544,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1484])).

tff(c_1637,plain,(
    ! [C_245,A_246,B_247] : k4_xboole_0(k2_zfmisc_1(C_245,A_246),k2_zfmisc_1(C_245,B_247)) = k2_zfmisc_1(C_245,k4_xboole_0(A_246,B_247)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1644,plain,(
    ! [C_245,B_247] : k2_zfmisc_1(C_245,k4_xboole_0(B_247,B_247)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1637,c_1544])).

tff(c_1653,plain,(
    ! [C_245] : k2_zfmisc_1(C_245,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_1644])).

tff(c_2434,plain,(
    ! [B_299,A_300] :
      ( k2_relat_1(k5_relat_1(B_299,A_300)) = k2_relat_1(A_300)
      | ~ r1_tarski(k1_relat_1(A_300),k2_relat_1(B_299))
      | ~ v1_relat_1(B_299)
      | ~ v1_relat_1(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2440,plain,(
    ! [B_299] :
      ( k2_relat_1(k5_relat_1(B_299,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_299))
      | ~ v1_relat_1(B_299)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2434])).

tff(c_2450,plain,(
    ! [B_301] :
      ( k2_relat_1(k5_relat_1(B_301,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_10,c_62,c_2440])).

tff(c_2465,plain,(
    ! [B_301] :
      ( k3_xboole_0(k5_relat_1(B_301,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_301,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_301,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_301,k1_xboole_0))
      | ~ v1_relat_1(B_301) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2450,c_56])).

tff(c_2480,plain,(
    ! [B_302] :
      ( k5_relat_1(B_302,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_302,k1_xboole_0))
      | ~ v1_relat_1(B_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1653,c_2465])).

tff(c_2487,plain,(
    ! [A_73] :
      ( k5_relat_1(A_73,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_54,c_2480])).

tff(c_2493,plain,(
    ! [A_303] :
      ( k5_relat_1(A_303,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_2487])).

tff(c_2502,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_2493])).

tff(c_2509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1336,c_2502])).

tff(c_2510,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1458])).

tff(c_2530,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2510,c_42])).

tff(c_2539,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2510,c_2510,c_2530])).

tff(c_2611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2607,c_2539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.80  
% 4.68/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.81  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.68/1.81  
% 4.68/1.81  %Foreground sorts:
% 4.68/1.81  
% 4.68/1.81  
% 4.68/1.81  %Background operators:
% 4.68/1.81  
% 4.68/1.81  
% 4.68/1.81  %Foreground operators:
% 4.68/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.68/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.68/1.81  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.68/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.68/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.68/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.68/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.68/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.68/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.68/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.68/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.68/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.68/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.68/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.68/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.68/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.68/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.68/1.81  
% 4.82/1.84  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.82/1.84  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.82/1.84  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.82/1.84  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.82/1.84  tff(f_122, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 4.82/1.84  tff(f_84, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 4.82/1.84  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.82/1.84  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.82/1.84  tff(f_90, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.82/1.84  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.82/1.84  tff(f_67, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 4.82/1.84  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.82/1.84  tff(f_115, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.82/1.84  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 4.82/1.84  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 4.82/1.84  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.82/1.84  tff(f_112, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 4.82/1.84  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.82/1.84  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.84  tff(c_2542, plain, (![A_304, B_305]: (k5_xboole_0(A_304, k3_xboole_0(A_304, B_305))=k4_xboole_0(A_304, B_305))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.82/1.84  tff(c_2554, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2542])).
% 4.82/1.84  tff(c_2564, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2554])).
% 4.82/1.84  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.82/1.84  tff(c_2560, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2542])).
% 4.82/1.84  tff(c_2607, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2564, c_2560])).
% 4.82/1.84  tff(c_66, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.82/1.84  tff(c_129, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 4.82/1.84  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.82/1.84  tff(c_52, plain, (![A_55]: (r2_hidden('#skF_1'(A_55), A_55) | v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.82/1.84  tff(c_148, plain, (![A_95, B_96]: (r1_tarski(k1_tarski(A_95), B_96) | ~r2_hidden(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.82/1.84  tff(c_12, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.82/1.84  tff(c_154, plain, (![A_97]: (k1_tarski(A_97)=k1_xboole_0 | ~r2_hidden(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_148, c_12])).
% 4.82/1.84  tff(c_159, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_154])).
% 4.82/1.84  tff(c_160, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_159])).
% 4.82/1.84  tff(c_54, plain, (![A_73, B_74]: (v1_relat_1(k5_relat_1(A_73, B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.82/1.84  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.82/1.84  tff(c_224, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.82/1.84  tff(c_233, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_224])).
% 4.82/1.84  tff(c_242, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_233])).
% 4.82/1.84  tff(c_239, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_224])).
% 4.82/1.84  tff(c_273, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_239])).
% 4.82/1.84  tff(c_415, plain, (![A_131, C_132, B_133]: (k4_xboole_0(k2_zfmisc_1(A_131, C_132), k2_zfmisc_1(B_133, C_132))=k2_zfmisc_1(k4_xboole_0(A_131, B_133), C_132))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.82/1.84  tff(c_422, plain, (![B_133, C_132]: (k2_zfmisc_1(k4_xboole_0(B_133, B_133), C_132)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_415, c_273])).
% 4.82/1.84  tff(c_431, plain, (![C_132]: (k2_zfmisc_1(k1_xboole_0, C_132)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_422])).
% 4.82/1.84  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.82/1.84  tff(c_64, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.82/1.84  tff(c_62, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.82/1.84  tff(c_1090, plain, (![A_180, B_181]: (k1_relat_1(k5_relat_1(A_180, B_181))=k1_relat_1(A_180) | ~r1_tarski(k2_relat_1(A_180), k1_relat_1(B_181)) | ~v1_relat_1(B_181) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.84  tff(c_1096, plain, (![B_181]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_181))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_181)) | ~v1_relat_1(B_181) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1090])).
% 4.82/1.84  tff(c_1101, plain, (![B_182]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_182))=k1_xboole_0 | ~v1_relat_1(B_182))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_10, c_64, c_1096])).
% 4.82/1.84  tff(c_56, plain, (![A_75]: (k3_xboole_0(A_75, k2_zfmisc_1(k1_relat_1(A_75), k2_relat_1(A_75)))=A_75 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.82/1.84  tff(c_1113, plain, (![B_182]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_182), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_182))))=k5_relat_1(k1_xboole_0, B_182) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_182)) | ~v1_relat_1(B_182))), inference(superposition, [status(thm), theory('equality')], [c_1101, c_56])).
% 4.82/1.84  tff(c_1121, plain, (![B_183]: (k5_relat_1(k1_xboole_0, B_183)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_183)) | ~v1_relat_1(B_183))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_431, c_1113])).
% 4.82/1.84  tff(c_1125, plain, (![B_74]: (k5_relat_1(k1_xboole_0, B_74)=k1_xboole_0 | ~v1_relat_1(B_74) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_54, c_1121])).
% 4.82/1.84  tff(c_1129, plain, (![B_184]: (k5_relat_1(k1_xboole_0, B_184)=k1_xboole_0 | ~v1_relat_1(B_184))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_1125])).
% 4.82/1.84  tff(c_1138, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_1129])).
% 4.82/1.84  tff(c_1144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_1138])).
% 4.82/1.84  tff(c_1145, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_159])).
% 4.82/1.84  tff(c_42, plain, (![B_52]: (k4_xboole_0(k1_tarski(B_52), k1_tarski(B_52))!=k1_tarski(B_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.82/1.84  tff(c_1153, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1145, c_42])).
% 4.82/1.84  tff(c_1160, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1145, c_1145, c_1153])).
% 4.82/1.84  tff(c_1283, plain, (![A_199, B_200]: (k5_xboole_0(A_199, k3_xboole_0(A_199, B_200))=k4_xboole_0(A_199, B_200))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.82/1.84  tff(c_1318, plain, (![A_202]: (k5_xboole_0(A_202, k1_xboole_0)=k4_xboole_0(A_202, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1283])).
% 4.82/1.84  tff(c_1298, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1283])).
% 4.82/1.84  tff(c_1309, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1298])).
% 4.82/1.84  tff(c_1325, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1318, c_1309])).
% 4.82/1.84  tff(c_1335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1160, c_1325])).
% 4.82/1.84  tff(c_1336, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 4.82/1.84  tff(c_1443, plain, (![A_222, B_223]: (r1_tarski(k1_tarski(A_222), B_223) | ~r2_hidden(A_222, B_223))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.82/1.84  tff(c_1453, plain, (![A_224]: (k1_tarski(A_224)=k1_xboole_0 | ~r2_hidden(A_224, k1_xboole_0))), inference(resolution, [status(thm)], [c_1443, c_12])).
% 4.82/1.84  tff(c_1458, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_1453])).
% 4.82/1.84  tff(c_1465, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1458])).
% 4.82/1.84  tff(c_1466, plain, (![A_227, B_228]: (k5_xboole_0(A_227, k3_xboole_0(A_227, B_228))=k4_xboole_0(A_227, B_228))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.82/1.84  tff(c_1478, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1466])).
% 4.82/1.84  tff(c_1488, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1478])).
% 4.82/1.84  tff(c_1484, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1466])).
% 4.82/1.84  tff(c_1544, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1484])).
% 4.82/1.84  tff(c_1637, plain, (![C_245, A_246, B_247]: (k4_xboole_0(k2_zfmisc_1(C_245, A_246), k2_zfmisc_1(C_245, B_247))=k2_zfmisc_1(C_245, k4_xboole_0(A_246, B_247)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.82/1.84  tff(c_1644, plain, (![C_245, B_247]: (k2_zfmisc_1(C_245, k4_xboole_0(B_247, B_247))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1637, c_1544])).
% 4.82/1.84  tff(c_1653, plain, (![C_245]: (k2_zfmisc_1(C_245, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1544, c_1644])).
% 4.82/1.84  tff(c_2434, plain, (![B_299, A_300]: (k2_relat_1(k5_relat_1(B_299, A_300))=k2_relat_1(A_300) | ~r1_tarski(k1_relat_1(A_300), k2_relat_1(B_299)) | ~v1_relat_1(B_299) | ~v1_relat_1(A_300))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.82/1.84  tff(c_2440, plain, (![B_299]: (k2_relat_1(k5_relat_1(B_299, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_299)) | ~v1_relat_1(B_299) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2434])).
% 4.82/1.84  tff(c_2450, plain, (![B_301]: (k2_relat_1(k5_relat_1(B_301, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_301))), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_10, c_62, c_2440])).
% 4.82/1.84  tff(c_2465, plain, (![B_301]: (k3_xboole_0(k5_relat_1(B_301, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_301, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_301, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_301, k1_xboole_0)) | ~v1_relat_1(B_301))), inference(superposition, [status(thm), theory('equality')], [c_2450, c_56])).
% 4.82/1.84  tff(c_2480, plain, (![B_302]: (k5_relat_1(B_302, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_302, k1_xboole_0)) | ~v1_relat_1(B_302))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1653, c_2465])).
% 4.82/1.84  tff(c_2487, plain, (![A_73]: (k5_relat_1(A_73, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_54, c_2480])).
% 4.82/1.84  tff(c_2493, plain, (![A_303]: (k5_relat_1(A_303, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_303))), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_2487])).
% 4.82/1.84  tff(c_2502, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_2493])).
% 4.82/1.84  tff(c_2509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1336, c_2502])).
% 4.82/1.84  tff(c_2510, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1458])).
% 4.82/1.84  tff(c_2530, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2510, c_42])).
% 4.82/1.84  tff(c_2539, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2510, c_2510, c_2530])).
% 4.82/1.84  tff(c_2611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2607, c_2539])).
% 4.82/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.84  
% 4.82/1.84  Inference rules
% 4.82/1.84  ----------------------
% 4.82/1.84  #Ref     : 2
% 4.82/1.84  #Sup     : 602
% 4.82/1.84  #Fact    : 0
% 4.82/1.84  #Define  : 0
% 4.82/1.84  #Split   : 3
% 4.82/1.84  #Chain   : 0
% 4.82/1.84  #Close   : 0
% 4.82/1.84  
% 4.82/1.84  Ordering : KBO
% 4.82/1.84  
% 4.82/1.84  Simplification rules
% 4.82/1.84  ----------------------
% 4.82/1.84  #Subsume      : 5
% 4.82/1.84  #Demod        : 523
% 4.82/1.84  #Tautology    : 401
% 4.82/1.84  #SimpNegUnit  : 7
% 4.82/1.84  #BackRed      : 12
% 4.82/1.84  
% 4.82/1.84  #Partial instantiations: 0
% 4.82/1.84  #Strategies tried      : 1
% 4.82/1.84  
% 4.82/1.84  Timing (in seconds)
% 4.82/1.84  ----------------------
% 4.82/1.84  Preprocessing        : 0.37
% 4.82/1.84  Parsing              : 0.19
% 4.82/1.84  CNF conversion       : 0.03
% 4.82/1.84  Main loop            : 0.68
% 4.82/1.84  Inferencing          : 0.25
% 4.82/1.84  Reduction            : 0.25
% 4.82/1.84  Demodulation         : 0.19
% 4.82/1.84  BG Simplification    : 0.03
% 4.82/1.84  Subsumption          : 0.09
% 4.82/1.84  Abstraction          : 0.04
% 4.82/1.84  MUC search           : 0.00
% 4.82/1.84  Cooper               : 0.00
% 4.82/1.84  Total                : 1.10
% 4.82/1.84  Index Insertion      : 0.00
% 4.82/1.84  Index Deletion       : 0.00
% 4.82/1.84  Index Matching       : 0.00
% 4.82/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
