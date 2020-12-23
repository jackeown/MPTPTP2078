%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:40 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 268 expanded)
%              Number of leaves         :   38 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  134 ( 487 expanded)
%              Number of equality atoms :   34 ( 131 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_76,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_54,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_81,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_113,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_48])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,(
    r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_32,plain,(
    ! [A_43] : v1_relat_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [A_48] : k2_relat_1(k6_relat_1(A_48)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_277,plain,(
    ! [A_106,B_107] :
      ( k5_relat_1(A_106,B_107) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_106),k1_relat_1(B_107))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_292,plain,(
    ! [A_48,B_107] :
      ( k5_relat_1(k6_relat_1(A_48),B_107) = k1_xboole_0
      | ~ r1_xboole_0(A_48,k1_relat_1(B_107))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_277])).

tff(c_665,plain,(
    ! [A_153,B_154] :
      ( k5_relat_1(k6_relat_1(A_153),B_154) = k1_xboole_0
      | ~ r1_xboole_0(A_153,k1_relat_1(B_154))
      | ~ v1_relat_1(B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_292])).

tff(c_697,plain,
    ( k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_665])).

tff(c_710,plain,(
    k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_697])).

tff(c_44,plain,(
    ! [A_51,B_52] :
      ( k5_relat_1(k6_relat_1(A_51),B_52) = k7_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_716,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_44])).

tff(c_723,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_716])).

tff(c_725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_723])).

tff(c_727,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_757,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_2'(A_160,B_161),B_161)
      | r1_xboole_0(A_160,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_761,plain,(
    ! [B_161,A_160] :
      ( ~ v1_xboole_0(B_161)
      | r1_xboole_0(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_757,c_2])).

tff(c_38,plain,(
    ! [A_48] : k1_relat_1(k6_relat_1(A_48)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_869,plain,(
    ! [A_190,B_191] :
      ( k5_relat_1(A_190,B_191) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_190),k1_relat_1(B_191))
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_881,plain,(
    ! [A_190,A_48] :
      ( k5_relat_1(A_190,k6_relat_1(A_48)) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_190),A_48)
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ v1_relat_1(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_869])).

tff(c_891,plain,(
    ! [A_192,A_193] :
      ( k5_relat_1(A_192,k6_relat_1(A_193)) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_192),A_193)
      | ~ v1_relat_1(A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_881])).

tff(c_907,plain,(
    ! [A_194,B_195] :
      ( k5_relat_1(A_194,k6_relat_1(B_195)) = k1_xboole_0
      | ~ v1_relat_1(A_194)
      | ~ v1_xboole_0(B_195) ) ),
    inference(resolution,[status(thm)],[c_761,c_891])).

tff(c_914,plain,(
    ! [B_195,A_51] :
      ( k7_relat_1(k6_relat_1(B_195),A_51) = k1_xboole_0
      | ~ v1_relat_1(k6_relat_1(B_195))
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_xboole_0(B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_44])).

tff(c_928,plain,(
    ! [B_196,A_197] :
      ( k7_relat_1(k6_relat_1(B_196),A_197) = k1_xboole_0
      | ~ v1_xboole_0(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_914])).

tff(c_824,plain,(
    ! [B_180,A_181] :
      ( k3_xboole_0(k1_relat_1(B_180),A_181) = k1_relat_1(k7_relat_1(B_180,A_181))
      | ~ v1_relat_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_839,plain,(
    ! [A_48,A_181] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_48),A_181)) = k3_xboole_0(A_48,A_181)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_824])).

tff(c_843,plain,(
    ! [A_48,A_181] : k1_relat_1(k7_relat_1(k6_relat_1(A_48),A_181)) = k3_xboole_0(A_48,A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_839])).

tff(c_962,plain,(
    ! [B_205,A_206] :
      ( k3_xboole_0(B_205,A_206) = k1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(B_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_843])).

tff(c_972,plain,(
    ! [A_207] : k3_xboole_0(k1_xboole_0,A_207) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_962])).

tff(c_844,plain,(
    ! [A_182,A_183] : k1_relat_1(k7_relat_1(k6_relat_1(A_182),A_183)) = k3_xboole_0(A_182,A_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_839])).

tff(c_34,plain,(
    ! [A_44] :
      ( v1_xboole_0(k1_relat_1(A_44))
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_853,plain,(
    ! [A_182,A_183] :
      ( v1_xboole_0(k3_xboole_0(A_182,A_183))
      | ~ v1_xboole_0(k7_relat_1(k6_relat_1(A_182),A_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_34])).

tff(c_934,plain,(
    ! [B_196,A_197] :
      ( v1_xboole_0(k3_xboole_0(B_196,A_197))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(B_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_853])).

tff(c_943,plain,(
    ! [B_196,A_197] :
      ( v1_xboole_0(k3_xboole_0(B_196,A_197))
      | ~ v1_xboole_0(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_934])).

tff(c_977,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_943])).

tff(c_988,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_977])).

tff(c_937,plain,(
    ! [B_196,A_197] :
      ( k3_xboole_0(B_196,A_197) = k1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(B_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_843])).

tff(c_1030,plain,(
    ! [A_216] : k3_xboole_0(k1_relat_1(k1_xboole_0),A_216) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_988,c_937])).

tff(c_762,plain,(
    ! [B_162,A_163] :
      ( ~ v1_xboole_0(B_162)
      | r1_xboole_0(A_163,B_162) ) ),
    inference(resolution,[status(thm)],[c_757,c_2])).

tff(c_776,plain,(
    ! [B_166,A_167] :
      ( r1_xboole_0(B_166,A_167)
      | ~ v1_xboole_0(B_166) ) ),
    inference(resolution,[status(thm)],[c_762,c_8])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( ~ r1_xboole_0(k3_xboole_0(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_786,plain,(
    ! [A_12,A_167] :
      ( r1_xboole_0(A_12,A_167)
      | ~ v1_xboole_0(k3_xboole_0(A_12,A_167)) ) ),
    inference(resolution,[status(thm)],[c_776,c_16])).

tff(c_1041,plain,(
    ! [A_216] :
      ( r1_xboole_0(k1_relat_1(k1_xboole_0),A_216)
      | ~ v1_xboole_0(k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_786])).

tff(c_1055,plain,(
    ! [A_216] : r1_xboole_0(k1_relat_1(k1_xboole_0),A_216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_1041])).

tff(c_726,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1410,plain,(
    ! [B_249,A_250] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(B_249,A_250)),A_250)
      | r1_xboole_0(k1_relat_1(B_249),A_250)
      | ~ v1_relat_1(B_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_824,c_16])).

tff(c_1446,plain,
    ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),'#skF_3')
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_1410])).

tff(c_1462,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1055,c_1446])).

tff(c_1464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_727,c_1462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.49  
% 3.25/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.49  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.25/1.49  
% 3.25/1.49  %Foreground sorts:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Background operators:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Foreground operators:
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.25/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.25/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.25/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.25/1.49  
% 3.25/1.51  tff(f_108, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.25/1.51  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.25/1.51  tff(f_76, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.25/1.51  tff(f_93, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.25/1.51  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 3.25/1.51  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.25/1.51  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.25/1.51  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.25/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.25/1.51  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.25/1.51  tff(f_80, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.25/1.51  tff(f_60, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.25/1.51  tff(c_54, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.25/1.51  tff(c_81, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 3.25/1.51  tff(c_48, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.25/1.51  tff(c_113, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_81, c_48])).
% 3.25/1.51  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.25/1.51  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.25/1.51  tff(c_84, plain, (r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_81, c_8])).
% 3.25/1.51  tff(c_32, plain, (![A_43]: (v1_relat_1(k6_relat_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.25/1.51  tff(c_40, plain, (![A_48]: (k2_relat_1(k6_relat_1(A_48))=A_48)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.51  tff(c_277, plain, (![A_106, B_107]: (k5_relat_1(A_106, B_107)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_106), k1_relat_1(B_107)) | ~v1_relat_1(B_107) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.25/1.51  tff(c_292, plain, (![A_48, B_107]: (k5_relat_1(k6_relat_1(A_48), B_107)=k1_xboole_0 | ~r1_xboole_0(A_48, k1_relat_1(B_107)) | ~v1_relat_1(B_107) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_277])).
% 3.25/1.51  tff(c_665, plain, (![A_153, B_154]: (k5_relat_1(k6_relat_1(A_153), B_154)=k1_xboole_0 | ~r1_xboole_0(A_153, k1_relat_1(B_154)) | ~v1_relat_1(B_154))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_292])).
% 3.25/1.51  tff(c_697, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_665])).
% 3.25/1.51  tff(c_710, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_697])).
% 3.25/1.51  tff(c_44, plain, (![A_51, B_52]: (k5_relat_1(k6_relat_1(A_51), B_52)=k7_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.25/1.51  tff(c_716, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_710, c_44])).
% 3.25/1.51  tff(c_723, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_716])).
% 3.25/1.51  tff(c_725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_723])).
% 3.25/1.51  tff(c_727, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 3.25/1.51  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.25/1.51  tff(c_757, plain, (![A_160, B_161]: (r2_hidden('#skF_2'(A_160, B_161), B_161) | r1_xboole_0(A_160, B_161))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.25/1.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.51  tff(c_761, plain, (![B_161, A_160]: (~v1_xboole_0(B_161) | r1_xboole_0(A_160, B_161))), inference(resolution, [status(thm)], [c_757, c_2])).
% 3.25/1.51  tff(c_38, plain, (![A_48]: (k1_relat_1(k6_relat_1(A_48))=A_48)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.51  tff(c_869, plain, (![A_190, B_191]: (k5_relat_1(A_190, B_191)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_190), k1_relat_1(B_191)) | ~v1_relat_1(B_191) | ~v1_relat_1(A_190))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.25/1.51  tff(c_881, plain, (![A_190, A_48]: (k5_relat_1(A_190, k6_relat_1(A_48))=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_190), A_48) | ~v1_relat_1(k6_relat_1(A_48)) | ~v1_relat_1(A_190))), inference(superposition, [status(thm), theory('equality')], [c_38, c_869])).
% 3.25/1.51  tff(c_891, plain, (![A_192, A_193]: (k5_relat_1(A_192, k6_relat_1(A_193))=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_192), A_193) | ~v1_relat_1(A_192))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_881])).
% 3.25/1.51  tff(c_907, plain, (![A_194, B_195]: (k5_relat_1(A_194, k6_relat_1(B_195))=k1_xboole_0 | ~v1_relat_1(A_194) | ~v1_xboole_0(B_195))), inference(resolution, [status(thm)], [c_761, c_891])).
% 3.25/1.51  tff(c_914, plain, (![B_195, A_51]: (k7_relat_1(k6_relat_1(B_195), A_51)=k1_xboole_0 | ~v1_relat_1(k6_relat_1(B_195)) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_xboole_0(B_195))), inference(superposition, [status(thm), theory('equality')], [c_907, c_44])).
% 3.25/1.51  tff(c_928, plain, (![B_196, A_197]: (k7_relat_1(k6_relat_1(B_196), A_197)=k1_xboole_0 | ~v1_xboole_0(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_914])).
% 3.25/1.51  tff(c_824, plain, (![B_180, A_181]: (k3_xboole_0(k1_relat_1(B_180), A_181)=k1_relat_1(k7_relat_1(B_180, A_181)) | ~v1_relat_1(B_180))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.25/1.51  tff(c_839, plain, (![A_48, A_181]: (k1_relat_1(k7_relat_1(k6_relat_1(A_48), A_181))=k3_xboole_0(A_48, A_181) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_824])).
% 3.25/1.51  tff(c_843, plain, (![A_48, A_181]: (k1_relat_1(k7_relat_1(k6_relat_1(A_48), A_181))=k3_xboole_0(A_48, A_181))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_839])).
% 3.25/1.51  tff(c_962, plain, (![B_205, A_206]: (k3_xboole_0(B_205, A_206)=k1_relat_1(k1_xboole_0) | ~v1_xboole_0(B_205))), inference(superposition, [status(thm), theory('equality')], [c_928, c_843])).
% 3.25/1.51  tff(c_972, plain, (![A_207]: (k3_xboole_0(k1_xboole_0, A_207)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_962])).
% 3.25/1.51  tff(c_844, plain, (![A_182, A_183]: (k1_relat_1(k7_relat_1(k6_relat_1(A_182), A_183))=k3_xboole_0(A_182, A_183))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_839])).
% 3.25/1.51  tff(c_34, plain, (![A_44]: (v1_xboole_0(k1_relat_1(A_44)) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.25/1.51  tff(c_853, plain, (![A_182, A_183]: (v1_xboole_0(k3_xboole_0(A_182, A_183)) | ~v1_xboole_0(k7_relat_1(k6_relat_1(A_182), A_183)))), inference(superposition, [status(thm), theory('equality')], [c_844, c_34])).
% 3.25/1.51  tff(c_934, plain, (![B_196, A_197]: (v1_xboole_0(k3_xboole_0(B_196, A_197)) | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(B_196))), inference(superposition, [status(thm), theory('equality')], [c_928, c_853])).
% 3.25/1.51  tff(c_943, plain, (![B_196, A_197]: (v1_xboole_0(k3_xboole_0(B_196, A_197)) | ~v1_xboole_0(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_934])).
% 3.25/1.51  tff(c_977, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_972, c_943])).
% 3.25/1.51  tff(c_988, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_977])).
% 3.25/1.51  tff(c_937, plain, (![B_196, A_197]: (k3_xboole_0(B_196, A_197)=k1_relat_1(k1_xboole_0) | ~v1_xboole_0(B_196))), inference(superposition, [status(thm), theory('equality')], [c_928, c_843])).
% 3.25/1.51  tff(c_1030, plain, (![A_216]: (k3_xboole_0(k1_relat_1(k1_xboole_0), A_216)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_988, c_937])).
% 3.25/1.51  tff(c_762, plain, (![B_162, A_163]: (~v1_xboole_0(B_162) | r1_xboole_0(A_163, B_162))), inference(resolution, [status(thm)], [c_757, c_2])).
% 3.25/1.51  tff(c_776, plain, (![B_166, A_167]: (r1_xboole_0(B_166, A_167) | ~v1_xboole_0(B_166))), inference(resolution, [status(thm)], [c_762, c_8])).
% 3.25/1.51  tff(c_16, plain, (![A_12, B_13]: (~r1_xboole_0(k3_xboole_0(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.51  tff(c_786, plain, (![A_12, A_167]: (r1_xboole_0(A_12, A_167) | ~v1_xboole_0(k3_xboole_0(A_12, A_167)))), inference(resolution, [status(thm)], [c_776, c_16])).
% 3.25/1.51  tff(c_1041, plain, (![A_216]: (r1_xboole_0(k1_relat_1(k1_xboole_0), A_216) | ~v1_xboole_0(k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_786])).
% 3.25/1.51  tff(c_1055, plain, (![A_216]: (r1_xboole_0(k1_relat_1(k1_xboole_0), A_216))), inference(demodulation, [status(thm), theory('equality')], [c_988, c_1041])).
% 3.25/1.51  tff(c_726, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.25/1.51  tff(c_1410, plain, (![B_249, A_250]: (~r1_xboole_0(k1_relat_1(k7_relat_1(B_249, A_250)), A_250) | r1_xboole_0(k1_relat_1(B_249), A_250) | ~v1_relat_1(B_249))), inference(superposition, [status(thm), theory('equality')], [c_824, c_16])).
% 3.25/1.51  tff(c_1446, plain, (~r1_xboole_0(k1_relat_1(k1_xboole_0), '#skF_3') | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_726, c_1410])).
% 3.25/1.51  tff(c_1462, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1055, c_1446])).
% 3.25/1.51  tff(c_1464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_727, c_1462])).
% 3.25/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  Inference rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Ref     : 0
% 3.25/1.51  #Sup     : 309
% 3.25/1.51  #Fact    : 0
% 3.25/1.51  #Define  : 0
% 3.25/1.51  #Split   : 3
% 3.25/1.51  #Chain   : 0
% 3.25/1.51  #Close   : 0
% 3.25/1.51  
% 3.25/1.51  Ordering : KBO
% 3.25/1.51  
% 3.25/1.51  Simplification rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Subsume      : 32
% 3.25/1.51  #Demod        : 129
% 3.25/1.51  #Tautology    : 135
% 3.25/1.51  #SimpNegUnit  : 2
% 3.25/1.51  #BackRed      : 0
% 3.25/1.51  
% 3.25/1.51  #Partial instantiations: 0
% 3.25/1.51  #Strategies tried      : 1
% 3.25/1.51  
% 3.25/1.51  Timing (in seconds)
% 3.25/1.51  ----------------------
% 3.25/1.51  Preprocessing        : 0.32
% 3.25/1.51  Parsing              : 0.17
% 3.25/1.51  CNF conversion       : 0.02
% 3.25/1.51  Main loop            : 0.45
% 3.25/1.51  Inferencing          : 0.18
% 3.25/1.51  Reduction            : 0.13
% 3.25/1.51  Demodulation         : 0.09
% 3.25/1.51  BG Simplification    : 0.02
% 3.25/1.51  Subsumption          : 0.08
% 3.25/1.51  Abstraction          : 0.02
% 3.25/1.51  MUC search           : 0.00
% 3.25/1.52  Cooper               : 0.00
% 3.25/1.52  Total                : 0.81
% 3.25/1.52  Index Insertion      : 0.00
% 3.25/1.52  Index Deletion       : 0.00
% 3.25/1.52  Index Matching       : 0.00
% 3.25/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
