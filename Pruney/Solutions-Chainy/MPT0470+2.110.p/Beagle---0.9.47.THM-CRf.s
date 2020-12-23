%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:16 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.61s
% Verified   : 
% Statistics : Number of formulae       :  148 (1431 expanded)
%              Number of leaves         :   46 ( 498 expanded)
%              Depth                    :   23
%              Number of atoms          :  240 (2685 expanded)
%              Number of equality atoms :  100 (1107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_130,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
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

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_123,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_110,axiom,(
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

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_18,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7902,plain,(
    ! [A_397,B_398] : k5_xboole_0(A_397,k3_xboole_0(A_397,B_398)) = k4_xboole_0(A_397,B_398) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7914,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7902])).

tff(c_7917,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7914])).

tff(c_863,plain,(
    ! [A_180,B_181] : k5_xboole_0(A_180,k3_xboole_0(A_180,B_181)) = k4_xboole_0(A_180,B_181) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_875,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_863])).

tff(c_878,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_875])).

tff(c_68,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_124,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_1'(A_48),A_48)
      | v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_161,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k1_tarski(A_93),B_94)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_167,plain,(
    ! [A_95] :
      ( k1_tarski(A_95) = k1_xboole_0
      | ~ r2_hidden(A_95,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_161,c_16])).

tff(c_172,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_167])).

tff(c_173,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_54,plain,(
    ! [A_66,B_67] :
      ( v1_relat_1(k5_relat_1(A_66,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = k4_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_208,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_196])).

tff(c_211,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_208])).

tff(c_442,plain,(
    ! [A_135,C_136,B_137] : k4_xboole_0(k2_zfmisc_1(A_135,C_136),k2_zfmisc_1(B_137,C_136)) = k2_zfmisc_1(k4_xboole_0(A_135,B_137),C_136) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_464,plain,(
    ! [A_135,C_136] : k2_zfmisc_1(k4_xboole_0(A_135,A_135),C_136) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_442])).

tff(c_470,plain,(
    ! [C_136] : k2_zfmisc_1(k1_xboole_0,C_136) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_464])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_64,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_610,plain,(
    ! [A_157,B_158] :
      ( k1_relat_1(k5_relat_1(A_157,B_158)) = k1_relat_1(A_157)
      | ~ r1_tarski(k2_relat_1(A_157),k1_relat_1(B_158))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_619,plain,(
    ! [B_158] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_158)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_158))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_610])).

tff(c_626,plain,(
    ! [B_159] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_159)) = k1_xboole_0
      | ~ v1_relat_1(B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_14,c_66,c_619])).

tff(c_56,plain,(
    ! [A_68] :
      ( k3_xboole_0(A_68,k2_zfmisc_1(k1_relat_1(A_68),k2_relat_1(A_68))) = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_638,plain,(
    ! [B_159] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_159),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_159)))) = k5_relat_1(k1_xboole_0,B_159)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_159))
      | ~ v1_relat_1(B_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_56])).

tff(c_762,plain,(
    ! [B_164] :
      ( k5_relat_1(k1_xboole_0,B_164) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_164))
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_470,c_638])).

tff(c_766,plain,(
    ! [B_67] :
      ( k5_relat_1(k1_xboole_0,B_67) = k1_xboole_0
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_54,c_762])).

tff(c_770,plain,(
    ! [B_165] :
      ( k5_relat_1(k1_xboole_0,B_165) = k1_xboole_0
      | ~ v1_relat_1(B_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_766])).

tff(c_779,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_770])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_779])).

tff(c_786,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_42,plain,(
    ! [B_45] : k4_xboole_0(k1_tarski(B_45),k1_tarski(B_45)) != k1_tarski(B_45) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_792,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_42])).

tff(c_804,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_786,c_792])).

tff(c_882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_804])).

tff(c_883,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_925,plain,(
    ! [A_187,B_188] :
      ( r1_tarski(k1_tarski(A_187),B_188)
      | ~ r2_hidden(A_187,B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_931,plain,(
    ! [A_189] :
      ( k1_tarski(A_189) = k1_xboole_0
      | ~ r2_hidden(A_189,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_925,c_16])).

tff(c_936,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_931])).

tff(c_938,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_936])).

tff(c_979,plain,(
    ! [A_203,B_204] : k5_xboole_0(A_203,k3_xboole_0(A_203,B_204)) = k4_xboole_0(A_203,B_204) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_991,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_979])).

tff(c_994,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_991])).

tff(c_1201,plain,(
    ! [A_226,C_227,B_228] : k4_xboole_0(k2_zfmisc_1(A_226,C_227),k2_zfmisc_1(B_228,C_227)) = k2_zfmisc_1(k4_xboole_0(A_226,B_228),C_227) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1208,plain,(
    ! [B_228,C_227] : k2_zfmisc_1(k4_xboole_0(B_228,B_228),C_227) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1201,c_994])).

tff(c_1217,plain,(
    ! [C_227] : k2_zfmisc_1(k1_xboole_0,C_227) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_994,c_1208])).

tff(c_1532,plain,(
    ! [A_259,B_260] :
      ( k1_relat_1(k5_relat_1(A_259,B_260)) = k1_relat_1(A_259)
      | ~ r1_tarski(k2_relat_1(A_259),k1_relat_1(B_260))
      | ~ v1_relat_1(B_260)
      | ~ v1_relat_1(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1541,plain,(
    ! [B_260] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_260)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_260))
      | ~ v1_relat_1(B_260)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1532])).

tff(c_1548,plain,(
    ! [B_261] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_261)) = k1_xboole_0
      | ~ v1_relat_1(B_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_14,c_66,c_1541])).

tff(c_1560,plain,(
    ! [B_261] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_261),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_261)))) = k5_relat_1(k1_xboole_0,B_261)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_261))
      | ~ v1_relat_1(B_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1548,c_56])).

tff(c_1573,plain,(
    ! [B_262] :
      ( k5_relat_1(k1_xboole_0,B_262) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_262))
      | ~ v1_relat_1(B_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1217,c_1560])).

tff(c_1577,plain,(
    ! [B_67] :
      ( k5_relat_1(k1_xboole_0,B_67) = k1_xboole_0
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_54,c_1573])).

tff(c_1586,plain,(
    ! [B_263] :
      ( k5_relat_1(k1_xboole_0,B_263) = k1_xboole_0
      | ~ v1_relat_1(B_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_1577])).

tff(c_1597,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_938,c_1586])).

tff(c_1150,plain,(
    ! [A_222,B_223] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_222,B_223)),k2_relat_1(B_223))
      | ~ v1_relat_1(B_223)
      | ~ v1_relat_1(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1158,plain,(
    ! [A_222] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_222,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1150])).

tff(c_1164,plain,(
    ! [A_224] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_224,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_1158])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1166,plain,(
    ! [A_224] :
      ( k2_relat_1(k5_relat_1(A_224,k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(A_224,k1_xboole_0)))
      | ~ v1_relat_1(A_224) ) ),
    inference(resolution,[status(thm)],[c_1164,c_4])).

tff(c_1172,plain,(
    ! [A_224] :
      ( k2_relat_1(k5_relat_1(A_224,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1166])).

tff(c_884,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1746,plain,(
    ! [A_275,B_276,C_277] :
      ( k5_relat_1(k5_relat_1(A_275,B_276),C_277) = k5_relat_1(A_275,k5_relat_1(B_276,C_277))
      | ~ v1_relat_1(C_277)
      | ~ v1_relat_1(B_276)
      | ~ v1_relat_1(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1784,plain,(
    ! [C_277] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_4',C_277)) = k5_relat_1(k1_xboole_0,C_277)
      | ~ v1_relat_1(C_277)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_1746])).

tff(c_1796,plain,(
    ! [C_277] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_4',C_277)) = k5_relat_1(k1_xboole_0,C_277)
      | ~ v1_relat_1(C_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_70,c_1784])).

tff(c_1797,plain,(
    ! [C_278] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_4',C_278)) = k5_relat_1(k1_xboole_0,C_278)
      | ~ v1_relat_1(C_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_70,c_1784])).

tff(c_1596,plain,(
    ! [A_66,B_67] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(A_66,B_67)) = k1_xboole_0
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_54,c_1586])).

tff(c_1809,plain,(
    ! [C_278] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_278)) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1('#skF_4',C_278))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(C_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1797,c_1596])).

tff(c_1924,plain,(
    ! [C_282] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_282)) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1('#skF_4',C_282))
      | ~ v1_relat_1(C_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_1809])).

tff(c_1928,plain,(
    ! [B_67] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,B_67)) = k1_xboole_0
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_1924])).

tff(c_1931,plain,(
    ! [B_67] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,B_67)) = k1_xboole_0
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1928])).

tff(c_58,plain,(
    ! [A_69,B_71] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_69,B_71)),k2_relat_1(B_71))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4201,plain,(
    ! [A_334,B_335,C_336] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_334,k5_relat_1(B_335,C_336))),k2_relat_1(C_336))
      | ~ v1_relat_1(C_336)
      | ~ v1_relat_1(k5_relat_1(A_334,B_335))
      | ~ v1_relat_1(C_336)
      | ~ v1_relat_1(B_335)
      | ~ v1_relat_1(A_334) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1746,c_58])).

tff(c_7285,plain,(
    ! [A_384,B_385,C_386] :
      ( k2_relat_1(k5_relat_1(A_384,k5_relat_1(B_385,C_386))) = k2_relat_1(C_386)
      | ~ r1_tarski(k2_relat_1(C_386),k2_relat_1(k5_relat_1(A_384,k5_relat_1(B_385,C_386))))
      | ~ v1_relat_1(k5_relat_1(A_384,B_385))
      | ~ v1_relat_1(C_386)
      | ~ v1_relat_1(B_385)
      | ~ v1_relat_1(A_384) ) ),
    inference(resolution,[status(thm)],[c_4201,c_4])).

tff(c_7377,plain,(
    ! [B_67] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,B_67))) = k2_relat_1(B_67)
      | ~ r1_tarski(k2_relat_1(B_67),k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1931,c_7285])).

tff(c_7475,plain,(
    ! [B_387] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,B_387))) = k2_relat_1(B_387)
      | ~ r1_tarski(k2_relat_1(B_387),k1_xboole_0)
      | ~ v1_relat_1(B_387) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_938,c_938,c_1597,c_64,c_7377])).

tff(c_7700,plain,(
    ! [C_389] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_389))) = k2_relat_1(k5_relat_1('#skF_4',C_389))
      | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_4',C_389)),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1('#skF_4',C_389))
      | ~ v1_relat_1(C_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1796,c_7475])).

tff(c_7708,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k2_relat_1(k5_relat_1('#skF_4',k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1('#skF_4',k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1172,c_7700])).

tff(c_7717,plain,
    ( k2_relat_1(k5_relat_1('#skF_4',k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_938,c_14,c_64,c_1597,c_1597,c_7708])).

tff(c_7721,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_7717])).

tff(c_7724,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_7721])).

tff(c_7728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_938,c_7724])).

tff(c_7730,plain,(
    v1_relat_1(k5_relat_1('#skF_4',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_7717])).

tff(c_1238,plain,(
    ! [C_230,A_231,B_232] : k4_xboole_0(k2_zfmisc_1(C_230,A_231),k2_zfmisc_1(C_230,B_232)) = k2_zfmisc_1(C_230,k4_xboole_0(A_231,B_232)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_41,C_43,B_42] : k4_xboole_0(k2_zfmisc_1(A_41,C_43),k2_zfmisc_1(B_42,C_43)) = k2_zfmisc_1(k4_xboole_0(A_41,B_42),C_43) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1245,plain,(
    ! [C_230,B_232] : k2_zfmisc_1(k4_xboole_0(C_230,C_230),B_232) = k2_zfmisc_1(C_230,k4_xboole_0(B_232,B_232)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_38])).

tff(c_1268,plain,(
    ! [C_230] : k2_zfmisc_1(C_230,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1217,c_994,c_994,c_1245])).

tff(c_7729,plain,(
    k2_relat_1(k5_relat_1('#skF_4',k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7717])).

tff(c_7793,plain,
    ( k3_xboole_0(k5_relat_1('#skF_4',k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1('#skF_4',k1_xboole_0)),k1_xboole_0)) = k5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1('#skF_4',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7729,c_56])).

tff(c_7837,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7730,c_12,c_1268,c_7793])).

tff(c_7839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_883,c_7837])).

tff(c_7840,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_936])).

tff(c_7846,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7840,c_42])).

tff(c_7858,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7840,c_7840,c_7846])).

tff(c_7921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7917,c_7858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:23:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.40  
% 6.53/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.41  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 6.53/2.41  
% 6.53/2.41  %Foreground sorts:
% 6.53/2.41  
% 6.53/2.41  
% 6.53/2.41  %Background operators:
% 6.53/2.41  
% 6.53/2.41  
% 6.53/2.41  %Foreground operators:
% 6.53/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.53/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.53/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.53/2.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.53/2.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.53/2.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.53/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.53/2.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.53/2.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.53/2.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.53/2.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.53/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.53/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.53/2.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.53/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.53/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.53/2.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.53/2.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.53/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.53/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.53/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.53/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.53/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.53/2.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.53/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.53/2.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.53/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.53/2.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.53/2.41  
% 6.61/2.43  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.61/2.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.61/2.43  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.61/2.43  tff(f_130, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 6.61/2.43  tff(f_84, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 6.61/2.43  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.61/2.43  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.61/2.43  tff(f_90, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.61/2.43  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.61/2.43  tff(f_67, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 6.61/2.43  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.61/2.43  tff(f_123, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.61/2.43  tff(f_110, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 6.61/2.43  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 6.61/2.43  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.61/2.43  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 6.61/2.43  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.61/2.43  tff(f_120, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 6.61/2.43  tff(c_18, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.61/2.43  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.61/2.43  tff(c_7902, plain, (![A_397, B_398]: (k5_xboole_0(A_397, k3_xboole_0(A_397, B_398))=k4_xboole_0(A_397, B_398))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.61/2.43  tff(c_7914, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7902])).
% 6.61/2.43  tff(c_7917, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7914])).
% 6.61/2.43  tff(c_863, plain, (![A_180, B_181]: (k5_xboole_0(A_180, k3_xboole_0(A_180, B_181))=k4_xboole_0(A_180, B_181))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.61/2.43  tff(c_875, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_863])).
% 6.61/2.43  tff(c_878, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_875])).
% 6.61/2.43  tff(c_68, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.61/2.43  tff(c_124, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 6.61/2.43  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.61/2.43  tff(c_52, plain, (![A_48]: (r2_hidden('#skF_1'(A_48), A_48) | v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.61/2.43  tff(c_161, plain, (![A_93, B_94]: (r1_tarski(k1_tarski(A_93), B_94) | ~r2_hidden(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.61/2.43  tff(c_16, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.61/2.43  tff(c_167, plain, (![A_95]: (k1_tarski(A_95)=k1_xboole_0 | ~r2_hidden(A_95, k1_xboole_0))), inference(resolution, [status(thm)], [c_161, c_16])).
% 6.61/2.43  tff(c_172, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_167])).
% 6.61/2.43  tff(c_173, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_172])).
% 6.61/2.43  tff(c_54, plain, (![A_66, B_67]: (v1_relat_1(k5_relat_1(A_66, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.61/2.43  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.61/2.43  tff(c_196, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(A_105, B_106))=k4_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.61/2.43  tff(c_208, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_196])).
% 6.61/2.43  tff(c_211, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_208])).
% 6.61/2.43  tff(c_442, plain, (![A_135, C_136, B_137]: (k4_xboole_0(k2_zfmisc_1(A_135, C_136), k2_zfmisc_1(B_137, C_136))=k2_zfmisc_1(k4_xboole_0(A_135, B_137), C_136))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.61/2.43  tff(c_464, plain, (![A_135, C_136]: (k2_zfmisc_1(k4_xboole_0(A_135, A_135), C_136)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_211, c_442])).
% 6.61/2.43  tff(c_470, plain, (![C_136]: (k2_zfmisc_1(k1_xboole_0, C_136)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_464])).
% 6.61/2.43  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.61/2.43  tff(c_66, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.61/2.43  tff(c_64, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.61/2.43  tff(c_610, plain, (![A_157, B_158]: (k1_relat_1(k5_relat_1(A_157, B_158))=k1_relat_1(A_157) | ~r1_tarski(k2_relat_1(A_157), k1_relat_1(B_158)) | ~v1_relat_1(B_158) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.61/2.43  tff(c_619, plain, (![B_158]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_158))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_158)) | ~v1_relat_1(B_158) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_610])).
% 6.61/2.43  tff(c_626, plain, (![B_159]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_159))=k1_xboole_0 | ~v1_relat_1(B_159))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_14, c_66, c_619])).
% 6.61/2.43  tff(c_56, plain, (![A_68]: (k3_xboole_0(A_68, k2_zfmisc_1(k1_relat_1(A_68), k2_relat_1(A_68)))=A_68 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.61/2.43  tff(c_638, plain, (![B_159]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_159), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_159))))=k5_relat_1(k1_xboole_0, B_159) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_159)) | ~v1_relat_1(B_159))), inference(superposition, [status(thm), theory('equality')], [c_626, c_56])).
% 6.61/2.43  tff(c_762, plain, (![B_164]: (k5_relat_1(k1_xboole_0, B_164)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_164)) | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_470, c_638])).
% 6.61/2.43  tff(c_766, plain, (![B_67]: (k5_relat_1(k1_xboole_0, B_67)=k1_xboole_0 | ~v1_relat_1(B_67) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_54, c_762])).
% 6.61/2.43  tff(c_770, plain, (![B_165]: (k5_relat_1(k1_xboole_0, B_165)=k1_xboole_0 | ~v1_relat_1(B_165))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_766])).
% 6.61/2.43  tff(c_779, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_770])).
% 6.61/2.43  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_779])).
% 6.61/2.43  tff(c_786, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_172])).
% 6.61/2.43  tff(c_42, plain, (![B_45]: (k4_xboole_0(k1_tarski(B_45), k1_tarski(B_45))!=k1_tarski(B_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.61/2.43  tff(c_792, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_786, c_42])).
% 6.61/2.43  tff(c_804, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_786, c_786, c_792])).
% 6.61/2.43  tff(c_882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_878, c_804])).
% 6.61/2.43  tff(c_883, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 6.61/2.43  tff(c_925, plain, (![A_187, B_188]: (r1_tarski(k1_tarski(A_187), B_188) | ~r2_hidden(A_187, B_188))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.61/2.43  tff(c_931, plain, (![A_189]: (k1_tarski(A_189)=k1_xboole_0 | ~r2_hidden(A_189, k1_xboole_0))), inference(resolution, [status(thm)], [c_925, c_16])).
% 6.61/2.43  tff(c_936, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_931])).
% 6.61/2.43  tff(c_938, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_936])).
% 6.61/2.43  tff(c_979, plain, (![A_203, B_204]: (k5_xboole_0(A_203, k3_xboole_0(A_203, B_204))=k4_xboole_0(A_203, B_204))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.61/2.43  tff(c_991, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_979])).
% 6.61/2.43  tff(c_994, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_991])).
% 6.61/2.43  tff(c_1201, plain, (![A_226, C_227, B_228]: (k4_xboole_0(k2_zfmisc_1(A_226, C_227), k2_zfmisc_1(B_228, C_227))=k2_zfmisc_1(k4_xboole_0(A_226, B_228), C_227))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.61/2.43  tff(c_1208, plain, (![B_228, C_227]: (k2_zfmisc_1(k4_xboole_0(B_228, B_228), C_227)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1201, c_994])).
% 6.61/2.43  tff(c_1217, plain, (![C_227]: (k2_zfmisc_1(k1_xboole_0, C_227)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_994, c_1208])).
% 6.61/2.43  tff(c_1532, plain, (![A_259, B_260]: (k1_relat_1(k5_relat_1(A_259, B_260))=k1_relat_1(A_259) | ~r1_tarski(k2_relat_1(A_259), k1_relat_1(B_260)) | ~v1_relat_1(B_260) | ~v1_relat_1(A_259))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.61/2.43  tff(c_1541, plain, (![B_260]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_260))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_260)) | ~v1_relat_1(B_260) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1532])).
% 6.61/2.43  tff(c_1548, plain, (![B_261]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_261))=k1_xboole_0 | ~v1_relat_1(B_261))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_14, c_66, c_1541])).
% 6.61/2.43  tff(c_1560, plain, (![B_261]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_261), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_261))))=k5_relat_1(k1_xboole_0, B_261) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_261)) | ~v1_relat_1(B_261))), inference(superposition, [status(thm), theory('equality')], [c_1548, c_56])).
% 6.61/2.43  tff(c_1573, plain, (![B_262]: (k5_relat_1(k1_xboole_0, B_262)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_262)) | ~v1_relat_1(B_262))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1217, c_1560])).
% 6.61/2.43  tff(c_1577, plain, (![B_67]: (k5_relat_1(k1_xboole_0, B_67)=k1_xboole_0 | ~v1_relat_1(B_67) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_54, c_1573])).
% 6.61/2.43  tff(c_1586, plain, (![B_263]: (k5_relat_1(k1_xboole_0, B_263)=k1_xboole_0 | ~v1_relat_1(B_263))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_1577])).
% 6.61/2.43  tff(c_1597, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_938, c_1586])).
% 6.61/2.43  tff(c_1150, plain, (![A_222, B_223]: (r1_tarski(k2_relat_1(k5_relat_1(A_222, B_223)), k2_relat_1(B_223)) | ~v1_relat_1(B_223) | ~v1_relat_1(A_222))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.61/2.43  tff(c_1158, plain, (![A_222]: (r1_tarski(k2_relat_1(k5_relat_1(A_222, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_222))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1150])).
% 6.61/2.43  tff(c_1164, plain, (![A_224]: (r1_tarski(k2_relat_1(k5_relat_1(A_224, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_224))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_1158])).
% 6.61/2.43  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.61/2.43  tff(c_1166, plain, (![A_224]: (k2_relat_1(k5_relat_1(A_224, k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_relat_1(k5_relat_1(A_224, k1_xboole_0))) | ~v1_relat_1(A_224))), inference(resolution, [status(thm)], [c_1164, c_4])).
% 6.61/2.43  tff(c_1172, plain, (![A_224]: (k2_relat_1(k5_relat_1(A_224, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_224))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1166])).
% 6.61/2.43  tff(c_884, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 6.61/2.43  tff(c_1746, plain, (![A_275, B_276, C_277]: (k5_relat_1(k5_relat_1(A_275, B_276), C_277)=k5_relat_1(A_275, k5_relat_1(B_276, C_277)) | ~v1_relat_1(C_277) | ~v1_relat_1(B_276) | ~v1_relat_1(A_275))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.61/2.43  tff(c_1784, plain, (![C_277]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_4', C_277))=k5_relat_1(k1_xboole_0, C_277) | ~v1_relat_1(C_277) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_884, c_1746])).
% 6.61/2.43  tff(c_1796, plain, (![C_277]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_4', C_277))=k5_relat_1(k1_xboole_0, C_277) | ~v1_relat_1(C_277))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_70, c_1784])).
% 6.61/2.43  tff(c_1797, plain, (![C_278]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_4', C_278))=k5_relat_1(k1_xboole_0, C_278) | ~v1_relat_1(C_278))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_70, c_1784])).
% 6.61/2.43  tff(c_1596, plain, (![A_66, B_67]: (k5_relat_1(k1_xboole_0, k5_relat_1(A_66, B_67))=k1_xboole_0 | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_54, c_1586])).
% 6.61/2.43  tff(c_1809, plain, (![C_278]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_278))=k1_xboole_0 | ~v1_relat_1(k5_relat_1('#skF_4', C_278)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(C_278))), inference(superposition, [status(thm), theory('equality')], [c_1797, c_1596])).
% 6.61/2.43  tff(c_1924, plain, (![C_282]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_282))=k1_xboole_0 | ~v1_relat_1(k5_relat_1('#skF_4', C_282)) | ~v1_relat_1(C_282))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_1809])).
% 6.61/2.43  tff(c_1928, plain, (![B_67]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, B_67))=k1_xboole_0 | ~v1_relat_1(B_67) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_1924])).
% 6.61/2.43  tff(c_1931, plain, (![B_67]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, B_67))=k1_xboole_0 | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1928])).
% 6.61/2.43  tff(c_58, plain, (![A_69, B_71]: (r1_tarski(k2_relat_1(k5_relat_1(A_69, B_71)), k2_relat_1(B_71)) | ~v1_relat_1(B_71) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.61/2.43  tff(c_4201, plain, (![A_334, B_335, C_336]: (r1_tarski(k2_relat_1(k5_relat_1(A_334, k5_relat_1(B_335, C_336))), k2_relat_1(C_336)) | ~v1_relat_1(C_336) | ~v1_relat_1(k5_relat_1(A_334, B_335)) | ~v1_relat_1(C_336) | ~v1_relat_1(B_335) | ~v1_relat_1(A_334))), inference(superposition, [status(thm), theory('equality')], [c_1746, c_58])).
% 6.61/2.43  tff(c_7285, plain, (![A_384, B_385, C_386]: (k2_relat_1(k5_relat_1(A_384, k5_relat_1(B_385, C_386)))=k2_relat_1(C_386) | ~r1_tarski(k2_relat_1(C_386), k2_relat_1(k5_relat_1(A_384, k5_relat_1(B_385, C_386)))) | ~v1_relat_1(k5_relat_1(A_384, B_385)) | ~v1_relat_1(C_386) | ~v1_relat_1(B_385) | ~v1_relat_1(A_384))), inference(resolution, [status(thm)], [c_4201, c_4])).
% 6.61/2.43  tff(c_7377, plain, (![B_67]: (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, B_67)))=k2_relat_1(B_67) | ~r1_tarski(k2_relat_1(B_67), k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0)) | ~v1_relat_1(B_67) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_1931, c_7285])).
% 6.61/2.43  tff(c_7475, plain, (![B_387]: (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, B_387)))=k2_relat_1(B_387) | ~r1_tarski(k2_relat_1(B_387), k1_xboole_0) | ~v1_relat_1(B_387))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_938, c_938, c_1597, c_64, c_7377])).
% 6.61/2.43  tff(c_7700, plain, (![C_389]: (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_389)))=k2_relat_1(k5_relat_1('#skF_4', C_389)) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_4', C_389)), k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_4', C_389)) | ~v1_relat_1(C_389))), inference(superposition, [status(thm), theory('equality')], [c_1796, c_7475])).
% 6.61/2.43  tff(c_7708, plain, (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, k1_xboole_0)))=k2_relat_1(k5_relat_1('#skF_4', k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_4', k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1172, c_7700])).
% 6.61/2.43  tff(c_7717, plain, (k2_relat_1(k5_relat_1('#skF_4', k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_938, c_14, c_64, c_1597, c_1597, c_7708])).
% 6.61/2.43  tff(c_7721, plain, (~v1_relat_1(k5_relat_1('#skF_4', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_7717])).
% 6.61/2.43  tff(c_7724, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_7721])).
% 6.61/2.43  tff(c_7728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_938, c_7724])).
% 6.61/2.43  tff(c_7730, plain, (v1_relat_1(k5_relat_1('#skF_4', k1_xboole_0))), inference(splitRight, [status(thm)], [c_7717])).
% 6.61/2.43  tff(c_1238, plain, (![C_230, A_231, B_232]: (k4_xboole_0(k2_zfmisc_1(C_230, A_231), k2_zfmisc_1(C_230, B_232))=k2_zfmisc_1(C_230, k4_xboole_0(A_231, B_232)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.61/2.43  tff(c_38, plain, (![A_41, C_43, B_42]: (k4_xboole_0(k2_zfmisc_1(A_41, C_43), k2_zfmisc_1(B_42, C_43))=k2_zfmisc_1(k4_xboole_0(A_41, B_42), C_43))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.61/2.43  tff(c_1245, plain, (![C_230, B_232]: (k2_zfmisc_1(k4_xboole_0(C_230, C_230), B_232)=k2_zfmisc_1(C_230, k4_xboole_0(B_232, B_232)))), inference(superposition, [status(thm), theory('equality')], [c_1238, c_38])).
% 6.61/2.43  tff(c_1268, plain, (![C_230]: (k2_zfmisc_1(C_230, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1217, c_994, c_994, c_1245])).
% 6.61/2.43  tff(c_7729, plain, (k2_relat_1(k5_relat_1('#skF_4', k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_7717])).
% 6.61/2.43  tff(c_7793, plain, (k3_xboole_0(k5_relat_1('#skF_4', k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1('#skF_4', k1_xboole_0)), k1_xboole_0))=k5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7729, c_56])).
% 6.61/2.43  tff(c_7837, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7730, c_12, c_1268, c_7793])).
% 6.61/2.43  tff(c_7839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_883, c_7837])).
% 6.61/2.43  tff(c_7840, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_936])).
% 6.61/2.43  tff(c_7846, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7840, c_42])).
% 6.61/2.43  tff(c_7858, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7840, c_7840, c_7846])).
% 6.61/2.43  tff(c_7921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7917, c_7858])).
% 6.61/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.43  
% 6.61/2.43  Inference rules
% 6.61/2.43  ----------------------
% 6.61/2.43  #Ref     : 2
% 6.61/2.43  #Sup     : 1812
% 6.61/2.43  #Fact    : 0
% 6.61/2.43  #Define  : 0
% 6.61/2.43  #Split   : 4
% 6.61/2.43  #Chain   : 0
% 6.61/2.43  #Close   : 0
% 6.61/2.43  
% 6.61/2.43  Ordering : KBO
% 6.61/2.43  
% 6.61/2.43  Simplification rules
% 6.61/2.43  ----------------------
% 6.61/2.43  #Subsume      : 261
% 6.61/2.43  #Demod        : 2339
% 6.61/2.43  #Tautology    : 891
% 6.61/2.43  #SimpNegUnit  : 8
% 6.61/2.43  #BackRed      : 13
% 6.61/2.43  
% 6.61/2.43  #Partial instantiations: 0
% 6.61/2.43  #Strategies tried      : 1
% 6.61/2.43  
% 6.61/2.43  Timing (in seconds)
% 6.61/2.43  ----------------------
% 6.61/2.43  Preprocessing        : 0.35
% 6.61/2.43  Parsing              : 0.18
% 6.61/2.43  CNF conversion       : 0.02
% 6.61/2.43  Main loop            : 1.30
% 6.61/2.43  Inferencing          : 0.41
% 6.61/2.43  Reduction            : 0.50
% 6.61/2.43  Demodulation         : 0.39
% 6.61/2.43  BG Simplification    : 0.06
% 6.61/2.43  Subsumption          : 0.25
% 6.61/2.43  Abstraction          : 0.07
% 6.61/2.43  MUC search           : 0.00
% 6.61/2.43  Cooper               : 0.00
% 6.61/2.43  Total                : 1.70
% 6.61/2.43  Index Insertion      : 0.00
% 6.61/2.43  Index Deletion       : 0.00
% 6.61/2.43  Index Matching       : 0.00
% 6.61/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
