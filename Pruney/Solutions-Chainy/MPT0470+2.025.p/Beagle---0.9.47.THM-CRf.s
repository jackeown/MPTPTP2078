%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:04 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 113 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 172 expanded)
%              Number of equality atoms :   38 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_95,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_48,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_80,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_75,plain,(
    ! [A_53] :
      ( v1_relat_1(A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_75])).

tff(c_36,plain,(
    ! [A_40,B_41] :
      ( v1_relat_1(k5_relat_1(A_40,B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    ! [A_56,B_57] :
      ( v1_xboole_0(k2_zfmisc_1(A_56,B_57))
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_109,plain,(
    ! [A_62,B_63] :
      ( k2_zfmisc_1(A_62,B_63) = k1_xboole_0
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_118,plain,(
    ! [B_63] : k2_zfmisc_1(k1_xboole_0,B_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_109])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_545,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_93,B_94)),k1_relat_1(A_93))
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_550,plain,(
    ! [B_94] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_94)),k1_xboole_0)
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_545])).

tff(c_554,plain,(
    ! [B_95] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_95)),k1_xboole_0)
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_550])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_197,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_206,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_564,plain,(
    ! [B_96] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_96)) = k1_xboole_0
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_554,c_206])).

tff(c_38,plain,(
    ! [A_42] :
      ( k3_xboole_0(A_42,k2_zfmisc_1(k1_relat_1(A_42),k2_relat_1(A_42))) = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_579,plain,(
    ! [B_96] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_96),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_96)))) = k5_relat_1(k1_xboole_0,B_96)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_38])).

tff(c_598,plain,(
    ! [B_101] :
      ( k5_relat_1(k1_xboole_0,B_101) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_118,c_579])).

tff(c_602,plain,(
    ! [B_41] :
      ( k5_relat_1(k1_xboole_0,B_41) = k1_xboole_0
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_598])).

tff(c_606,plain,(
    ! [B_102] :
      ( k5_relat_1(k1_xboole_0,B_102) = k1_xboole_0
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_602])).

tff(c_621,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_606])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_621])).

tff(c_630,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_645,plain,(
    ! [A_105,B_106] :
      ( v1_xboole_0(k2_zfmisc_1(A_105,B_106))
      | ~ v1_xboole_0(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_655,plain,(
    ! [A_109,B_110] :
      ( k2_zfmisc_1(A_109,B_110) = k1_xboole_0
      | ~ v1_xboole_0(B_110) ) ),
    inference(resolution,[status(thm)],[c_645,c_4])).

tff(c_664,plain,(
    ! [A_109] : k2_zfmisc_1(A_109,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_655])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1241,plain,(
    ! [B_157,A_158] :
      ( k2_relat_1(k5_relat_1(B_157,A_158)) = k2_relat_1(A_158)
      | ~ r1_tarski(k1_relat_1(A_158),k2_relat_1(B_157))
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1247,plain,(
    ! [B_157] :
      ( k2_relat_1(k5_relat_1(B_157,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_157))
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1241])).

tff(c_1257,plain,(
    ! [B_159] :
      ( k2_relat_1(k5_relat_1(B_159,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_14,c_44,c_1247])).

tff(c_1266,plain,(
    ! [B_159] :
      ( k3_xboole_0(k5_relat_1(B_159,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_159,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_159,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_159,k1_xboole_0))
      | ~ v1_relat_1(B_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_38])).

tff(c_1390,plain,(
    ! [B_164] :
      ( k5_relat_1(B_164,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_164,k1_xboole_0))
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_664,c_1266])).

tff(c_1397,plain,(
    ! [A_40] :
      ( k5_relat_1(A_40,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_36,c_1390])).

tff(c_1403,plain,(
    ! [A_165] :
      ( k5_relat_1(A_165,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1397])).

tff(c_1418,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_1403])).

tff(c_1427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_1418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:59:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.85  
% 3.67/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.85  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.67/1.85  
% 3.67/1.85  %Foreground sorts:
% 3.67/1.85  
% 3.67/1.85  
% 3.67/1.85  %Background operators:
% 3.67/1.85  
% 3.67/1.85  
% 3.67/1.85  %Foreground operators:
% 3.67/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.67/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.67/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.67/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.67/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.85  tff('#skF_1', type, '#skF_1': $i).
% 3.67/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.67/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.67/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.67/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.67/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.67/1.85  
% 3.67/1.88  tff(f_102, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.67/1.88  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.67/1.88  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.67/1.88  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.67/1.88  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.67/1.88  tff(f_60, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.67/1.88  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.67/1.88  tff(f_95, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.67/1.88  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.67/1.88  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.67/1.88  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.67/1.88  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.67/1.88  tff(f_56, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.67/1.88  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.67/1.88  tff(c_48, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.67/1.88  tff(c_80, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 3.67/1.88  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.67/1.88  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.67/1.88  tff(c_75, plain, (![A_53]: (v1_relat_1(A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.67/1.88  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_75])).
% 3.67/1.88  tff(c_36, plain, (![A_40, B_41]: (v1_relat_1(k5_relat_1(A_40, B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.67/1.88  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.67/1.88  tff(c_90, plain, (![A_56, B_57]: (v1_xboole_0(k2_zfmisc_1(A_56, B_57)) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.67/1.88  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.67/1.88  tff(c_109, plain, (![A_62, B_63]: (k2_zfmisc_1(A_62, B_63)=k1_xboole_0 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_90, c_4])).
% 3.67/1.88  tff(c_118, plain, (![B_63]: (k2_zfmisc_1(k1_xboole_0, B_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_109])).
% 3.67/1.88  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.67/1.88  tff(c_545, plain, (![A_93, B_94]: (r1_tarski(k1_relat_1(k5_relat_1(A_93, B_94)), k1_relat_1(A_93)) | ~v1_relat_1(B_94) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.67/1.88  tff(c_550, plain, (![B_94]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_94)), k1_xboole_0) | ~v1_relat_1(B_94) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_545])).
% 3.67/1.88  tff(c_554, plain, (![B_95]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_95)), k1_xboole_0) | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_550])).
% 3.67/1.88  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.67/1.88  tff(c_197, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.67/1.88  tff(c_206, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_197])).
% 3.67/1.88  tff(c_564, plain, (![B_96]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_96))=k1_xboole_0 | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_554, c_206])).
% 3.67/1.88  tff(c_38, plain, (![A_42]: (k3_xboole_0(A_42, k2_zfmisc_1(k1_relat_1(A_42), k2_relat_1(A_42)))=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.67/1.88  tff(c_579, plain, (![B_96]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_96), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_96))))=k5_relat_1(k1_xboole_0, B_96) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_96)) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_564, c_38])).
% 3.67/1.88  tff(c_598, plain, (![B_101]: (k5_relat_1(k1_xboole_0, B_101)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_101)) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_118, c_579])).
% 3.67/1.88  tff(c_602, plain, (![B_41]: (k5_relat_1(k1_xboole_0, B_41)=k1_xboole_0 | ~v1_relat_1(B_41) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_598])).
% 3.67/1.88  tff(c_606, plain, (![B_102]: (k5_relat_1(k1_xboole_0, B_102)=k1_xboole_0 | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_602])).
% 3.67/1.88  tff(c_621, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_606])).
% 3.67/1.88  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_621])).
% 3.67/1.88  tff(c_630, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.67/1.88  tff(c_645, plain, (![A_105, B_106]: (v1_xboole_0(k2_zfmisc_1(A_105, B_106)) | ~v1_xboole_0(B_106))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.67/1.88  tff(c_655, plain, (![A_109, B_110]: (k2_zfmisc_1(A_109, B_110)=k1_xboole_0 | ~v1_xboole_0(B_110))), inference(resolution, [status(thm)], [c_645, c_4])).
% 3.67/1.88  tff(c_664, plain, (![A_109]: (k2_zfmisc_1(A_109, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_655])).
% 3.67/1.88  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.67/1.88  tff(c_1241, plain, (![B_157, A_158]: (k2_relat_1(k5_relat_1(B_157, A_158))=k2_relat_1(A_158) | ~r1_tarski(k1_relat_1(A_158), k2_relat_1(B_157)) | ~v1_relat_1(B_157) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.67/1.88  tff(c_1247, plain, (![B_157]: (k2_relat_1(k5_relat_1(B_157, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_157)) | ~v1_relat_1(B_157) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1241])).
% 3.67/1.88  tff(c_1257, plain, (![B_159]: (k2_relat_1(k5_relat_1(B_159, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_159))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_14, c_44, c_1247])).
% 3.67/1.88  tff(c_1266, plain, (![B_159]: (k3_xboole_0(k5_relat_1(B_159, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_159, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_159, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_159, k1_xboole_0)) | ~v1_relat_1(B_159))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_38])).
% 3.67/1.88  tff(c_1390, plain, (![B_164]: (k5_relat_1(B_164, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_164, k1_xboole_0)) | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_664, c_1266])).
% 3.67/1.88  tff(c_1397, plain, (![A_40]: (k5_relat_1(A_40, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_36, c_1390])).
% 3.67/1.88  tff(c_1403, plain, (![A_165]: (k5_relat_1(A_165, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1397])).
% 3.67/1.88  tff(c_1418, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_1403])).
% 3.67/1.88  tff(c_1427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_630, c_1418])).
% 3.67/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.88  
% 3.67/1.88  Inference rules
% 3.67/1.88  ----------------------
% 3.67/1.88  #Ref     : 0
% 3.67/1.88  #Sup     : 320
% 3.67/1.88  #Fact    : 0
% 3.67/1.88  #Define  : 0
% 3.67/1.88  #Split   : 1
% 3.67/1.88  #Chain   : 0
% 3.67/1.88  #Close   : 0
% 3.67/1.88  
% 3.67/1.88  Ordering : KBO
% 3.67/1.88  
% 3.67/1.88  Simplification rules
% 3.67/1.88  ----------------------
% 3.67/1.88  #Subsume      : 5
% 3.67/1.88  #Demod        : 232
% 3.67/1.88  #Tautology    : 265
% 3.67/1.88  #SimpNegUnit  : 2
% 3.67/1.88  #BackRed      : 0
% 3.67/1.88  
% 3.67/1.88  #Partial instantiations: 0
% 3.67/1.88  #Strategies tried      : 1
% 3.67/1.88  
% 3.67/1.88  Timing (in seconds)
% 3.67/1.88  ----------------------
% 3.67/1.88  Preprocessing        : 0.47
% 3.67/1.88  Parsing              : 0.23
% 3.67/1.88  CNF conversion       : 0.03
% 3.67/1.88  Main loop            : 0.60
% 3.67/1.88  Inferencing          : 0.22
% 3.67/1.88  Reduction            : 0.19
% 3.67/1.88  Demodulation         : 0.14
% 3.67/1.88  BG Simplification    : 0.03
% 3.67/1.88  Subsumption          : 0.12
% 3.67/1.88  Abstraction          : 0.03
% 3.67/1.88  MUC search           : 0.00
% 3.67/1.88  Cooper               : 0.00
% 3.67/1.88  Total                : 1.13
% 3.67/1.88  Index Insertion      : 0.00
% 3.67/1.88  Index Deletion       : 0.00
% 3.67/1.88  Index Matching       : 0.00
% 3.67/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
