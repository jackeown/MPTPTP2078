%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:10 EST 2020

% Result     : Theorem 34.23s
% Output     : CNFRefutation 34.39s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 458 expanded)
%              Number of leaves         :   32 ( 175 expanded)
%              Depth                    :   21
%              Number of atoms          :  220 ( 814 expanded)
%              Number of equality atoms :   62 ( 263 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_315,plain,(
    ! [A_83] :
      ( k9_relat_1(A_83,k1_relat_1(A_83)) = k2_relat_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_324,plain,(
    ! [A_27] :
      ( k9_relat_1(k6_relat_1(A_27),A_27) = k2_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_315])).

tff(c_328,plain,(
    ! [A_27] : k9_relat_1(k6_relat_1(A_27),A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32,c_324])).

tff(c_48,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_110,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_110])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(k2_xboole_0(A_54,B_56),C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    ! [A_54,B_56] : r1_tarski(A_54,k2_xboole_0(A_54,B_56)) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_728,plain,(
    ! [B_113,A_114] :
      ( k7_relat_1(B_113,A_114) = B_113
      | ~ r1_tarski(k1_relat_1(B_113),A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1160,plain,(
    ! [B_138,B_139] :
      ( k7_relat_1(B_138,k2_xboole_0(k1_relat_1(B_138),B_139)) = B_138
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_143,c_728])).

tff(c_1221,plain,(
    ! [A_27,B_139] :
      ( k7_relat_1(k6_relat_1(A_27),k2_xboole_0(A_27,B_139)) = k6_relat_1(A_27)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1160])).

tff(c_1420,plain,(
    ! [A_147,B_148] : k7_relat_1(k6_relat_1(A_147),k2_xboole_0(A_147,B_148)) = k6_relat_1(A_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1221])).

tff(c_1489,plain,(
    k7_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k6_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_1420])).

tff(c_22,plain,(
    ! [A_16] :
      ( k9_relat_1(A_16,k1_relat_1(A_16)) = k2_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_32,B_33] :
      ( k5_relat_1(k6_relat_1(A_32),B_33) = k7_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1356,plain,(
    ! [B_143,C_144,A_145] :
      ( k9_relat_1(k5_relat_1(B_143,C_144),A_145) = k9_relat_1(C_144,k9_relat_1(B_143,A_145))
      | ~ v1_relat_1(C_144)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1375,plain,(
    ! [B_33,A_32,A_145] :
      ( k9_relat_1(B_33,k9_relat_1(k6_relat_1(A_32),A_145)) = k9_relat_1(k7_relat_1(B_33,A_32),A_145)
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1356])).

tff(c_2810,plain,(
    ! [B_203,A_204,A_205] :
      ( k9_relat_1(B_203,k9_relat_1(k6_relat_1(A_204),A_205)) = k9_relat_1(k7_relat_1(B_203,A_204),A_205)
      | ~ v1_relat_1(B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1375])).

tff(c_2876,plain,(
    ! [B_203,A_204] :
      ( k9_relat_1(k7_relat_1(B_203,A_204),k1_relat_1(k6_relat_1(A_204))) = k9_relat_1(B_203,k2_relat_1(k6_relat_1(A_204)))
      | ~ v1_relat_1(B_203)
      | ~ v1_relat_1(k6_relat_1(A_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2810])).

tff(c_2892,plain,(
    ! [B_203,A_204] :
      ( k9_relat_1(k7_relat_1(B_203,A_204),A_204) = k9_relat_1(B_203,A_204)
      | ~ v1_relat_1(B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32,c_30,c_2876])).

tff(c_605,plain,(
    ! [A_103,B_104] :
      ( k5_relat_1(k6_relat_1(A_103),B_104) = k7_relat_1(B_104,A_103)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k5_relat_1(B_29,k6_relat_1(A_28)),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_235,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_240,plain,(
    ! [A_71,B_72] :
      ( v1_relat_1(A_71)
      | ~ v1_relat_1(B_72)
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_14,c_235])).

tff(c_265,plain,(
    ! [B_29,A_28] :
      ( v1_relat_1(k5_relat_1(B_29,k6_relat_1(A_28)))
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_240])).

tff(c_612,plain,(
    ! [A_28,A_103] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_28),A_103))
      | ~ v1_relat_1(k6_relat_1(A_103))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_265])).

tff(c_628,plain,(
    ! [A_28,A_103] : v1_relat_1(k7_relat_1(k6_relat_1(A_28),A_103)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_612])).

tff(c_622,plain,(
    ! [A_28,A_103] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_28),A_103),k6_relat_1(A_103))
      | ~ v1_relat_1(k6_relat_1(A_103))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_36])).

tff(c_630,plain,(
    ! [A_28,A_103] : r1_tarski(k7_relat_1(k6_relat_1(A_28),A_103),k6_relat_1(A_103)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_622])).

tff(c_1015,plain,(
    ! [B_129,A_130,C_131] :
      ( r1_tarski(k9_relat_1(B_129,A_130),k9_relat_1(C_131,A_130))
      | ~ r1_tarski(B_129,C_131)
      | ~ v1_relat_1(C_131)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4627,plain,(
    ! [B_258,A_259,C_260] :
      ( k2_xboole_0(k9_relat_1(B_258,A_259),k9_relat_1(C_260,A_259)) = k9_relat_1(C_260,A_259)
      | ~ r1_tarski(B_258,C_260)
      | ~ v1_relat_1(C_260)
      | ~ v1_relat_1(B_258) ) ),
    inference(resolution,[status(thm)],[c_1015,c_10])).

tff(c_4742,plain,(
    ! [A_27,B_258] :
      ( k9_relat_1(k6_relat_1(A_27),A_27) = k2_xboole_0(k9_relat_1(B_258,A_27),A_27)
      | ~ r1_tarski(B_258,k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(B_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_4627])).

tff(c_13099,plain,(
    ! [B_515,A_516] :
      ( k2_xboole_0(k9_relat_1(B_515,A_516),A_516) = A_516
      | ~ r1_tarski(B_515,k6_relat_1(A_516))
      | ~ v1_relat_1(B_515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_328,c_4742])).

tff(c_13221,plain,(
    ! [A_28,A_103] :
      ( k2_xboole_0(k9_relat_1(k7_relat_1(k6_relat_1(A_28),A_103),A_103),A_103) = A_103
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_28),A_103)) ) ),
    inference(resolution,[status(thm)],[c_630,c_13099])).

tff(c_13400,plain,(
    ! [A_517,A_518] : k2_xboole_0(k9_relat_1(k7_relat_1(k6_relat_1(A_517),A_518),A_518),A_518) = A_518 ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_13221])).

tff(c_13511,plain,(
    ! [A_517,A_204] :
      ( k2_xboole_0(k9_relat_1(k6_relat_1(A_517),A_204),A_204) = A_204
      | ~ v1_relat_1(k6_relat_1(A_517)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2892,c_13400])).

tff(c_13559,plain,(
    ! [A_519,A_520] : k2_xboole_0(k9_relat_1(k6_relat_1(A_519),A_520),A_520) = A_520 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_13511])).

tff(c_1187,plain,(
    ! [A_28,B_139] :
      ( r1_tarski(k6_relat_1(A_28),k6_relat_1(k2_xboole_0(k1_relat_1(k6_relat_1(A_28)),B_139)))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1160,c_630])).

tff(c_1232,plain,(
    ! [A_28,B_139] : r1_tarski(k6_relat_1(A_28),k6_relat_1(k2_xboole_0(A_28,B_139))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30,c_1187])).

tff(c_13642,plain,(
    ! [A_519,A_520] : r1_tarski(k6_relat_1(k9_relat_1(k6_relat_1(A_519),A_520)),k6_relat_1(A_520)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13559,c_1232])).

tff(c_1241,plain,(
    ! [A_27,B_139] : k7_relat_1(k6_relat_1(A_27),k2_xboole_0(A_27,B_139)) = k6_relat_1(A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1221])).

tff(c_230,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k5_relat_1(B_67,k6_relat_1(A_68)),B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_778,plain,(
    ! [B_117,A_118] :
      ( k2_xboole_0(k5_relat_1(B_117,k6_relat_1(A_118)),B_117) = B_117
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_230,c_10])).

tff(c_806,plain,(
    ! [A_118,A_32] :
      ( k2_xboole_0(k7_relat_1(k6_relat_1(A_118),A_32),k6_relat_1(A_32)) = k6_relat_1(A_32)
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_778])).

tff(c_811,plain,(
    ! [A_118,A_32] : k2_xboole_0(k7_relat_1(k6_relat_1(A_118),A_32),k6_relat_1(A_32)) = k6_relat_1(A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_806])).

tff(c_742,plain,(
    ! [A_27,A_114] :
      ( k7_relat_1(k6_relat_1(A_27),A_114) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_114)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_728])).

tff(c_751,plain,(
    ! [A_27,A_114] :
      ( k7_relat_1(k6_relat_1(A_27),A_114) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_742])).

tff(c_216,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_65,A_66)),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_858,plain,(
    ! [B_121,A_122] :
      ( k2_xboole_0(k1_relat_1(k7_relat_1(B_121,A_122)),A_122) = A_122
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_216,c_10])).

tff(c_144,plain,(
    ! [A_57,B_58] : r1_tarski(A_57,k2_xboole_0(A_57,B_58)) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [A_3,B_4,B_58] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_58)) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_4790,plain,(
    ! [B_261,A_262,B_263] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_261,A_262)),k2_xboole_0(A_262,B_263))
      | ~ v1_relat_1(B_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_158])).

tff(c_4846,plain,(
    ! [A_27,A_114,B_263] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_27)),k2_xboole_0(A_114,B_263))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ r1_tarski(A_27,A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_4790])).

tff(c_4896,plain,(
    ! [A_264,A_265,B_266] :
      ( r1_tarski(A_264,k2_xboole_0(A_265,B_266))
      | ~ r1_tarski(A_264,A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30,c_4846])).

tff(c_239,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(A_8)
      | ~ v1_relat_1(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_235])).

tff(c_5665,plain,(
    ! [A_288,A_289,B_290] :
      ( v1_relat_1(A_288)
      | ~ v1_relat_1(k2_xboole_0(A_289,B_290))
      | ~ r1_tarski(A_288,A_289) ) ),
    inference(resolution,[status(thm)],[c_4896,c_239])).

tff(c_5681,plain,(
    ! [A_288,A_32,A_118] :
      ( v1_relat_1(A_288)
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ r1_tarski(A_288,k7_relat_1(k6_relat_1(A_118),A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_5665])).

tff(c_5800,plain,(
    ! [A_292,A_293,A_294] :
      ( v1_relat_1(A_292)
      | ~ r1_tarski(A_292,k7_relat_1(k6_relat_1(A_293),A_294)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5681])).

tff(c_5880,plain,(
    ! [A_295,A_296] :
      ( v1_relat_1(A_295)
      | ~ r1_tarski(A_295,k6_relat_1(A_296)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_5800])).

tff(c_5988,plain,(
    ! [A_296,A_28] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_296),k6_relat_1(A_28)))
      | ~ v1_relat_1(k6_relat_1(A_296)) ) ),
    inference(resolution,[status(thm)],[c_36,c_5880])).

tff(c_6070,plain,(
    ! [A_296,A_28] : v1_relat_1(k5_relat_1(k6_relat_1(A_296),k6_relat_1(A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5988])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_28),B_29),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_347,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2503,plain,(
    ! [A_186,B_187] :
      ( k5_relat_1(k6_relat_1(A_186),B_187) = B_187
      | ~ r1_tarski(B_187,k5_relat_1(k6_relat_1(A_186),B_187))
      | ~ v1_relat_1(B_187) ) ),
    inference(resolution,[status(thm)],[c_34,c_347])).

tff(c_18635,plain,(
    ! [A_621,B_622] :
      ( k5_relat_1(k6_relat_1(A_621),B_622) = B_622
      | ~ r1_tarski(B_622,k7_relat_1(B_622,A_621))
      | ~ v1_relat_1(B_622)
      | ~ v1_relat_1(B_622) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2503])).

tff(c_18686,plain,
    ( k5_relat_1(k6_relat_1('#skF_3'),k6_relat_1('#skF_2')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k6_relat_1('#skF_2'),k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1489,c_18635])).

tff(c_18728,plain,(
    k5_relat_1(k6_relat_1('#skF_3'),k6_relat_1('#skF_2')) = k6_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_6,c_18686])).

tff(c_1379,plain,(
    ! [C_144,B_143] :
      ( k9_relat_1(C_144,k9_relat_1(B_143,k1_relat_1(k5_relat_1(B_143,C_144)))) = k2_relat_1(k5_relat_1(B_143,C_144))
      | ~ v1_relat_1(C_144)
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(k5_relat_1(B_143,C_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1356])).

tff(c_18779,plain,
    ( k9_relat_1(k6_relat_1('#skF_2'),k9_relat_1(k6_relat_1('#skF_3'),k1_relat_1(k6_relat_1('#skF_2')))) = k2_relat_1(k5_relat_1(k6_relat_1('#skF_3'),k6_relat_1('#skF_2')))
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_3'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_3'),k6_relat_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18728,c_1379])).

tff(c_18837,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6070,c_18,c_18,c_32,c_18728,c_30,c_18779])).

tff(c_19052,plain,(
    r1_tarski(k6_relat_1('#skF_2'),k6_relat_1(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18837,c_13642])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19284,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k6_relat_1(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')),k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_19052,c_2])).

tff(c_19308,plain,(
    k6_relat_1(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) = k6_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13642,c_19284])).

tff(c_2872,plain,(
    ! [A_204,A_205] :
      ( k9_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_204),A_205)),A_204),A_205) = k9_relat_1(k6_relat_1(A_204),A_205)
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_204),A_205))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_2810])).

tff(c_2890,plain,(
    ! [A_204,A_205] : k9_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_204),A_205)),A_204),A_205) = k9_relat_1(k6_relat_1(A_204),A_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2872])).

tff(c_19389,plain,(
    k9_relat_1(k7_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_2') = k9_relat_1(k6_relat_1('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19308,c_2890])).

tff(c_19793,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_1489,c_19389])).

tff(c_1383,plain,(
    ! [B_33,A_32,A_145] :
      ( k9_relat_1(B_33,k9_relat_1(k6_relat_1(A_32),A_145)) = k9_relat_1(k7_relat_1(B_33,A_32),A_145)
      | ~ v1_relat_1(B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1375])).

tff(c_100804,plain,(
    ! [B_1668] :
      ( k9_relat_1(k7_relat_1(B_1668,'#skF_3'),'#skF_2') = k9_relat_1(B_1668,'#skF_2')
      | ~ v1_relat_1(B_1668) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19793,c_1383])).

tff(c_46,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_101055,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100804,c_46])).

tff(c_101129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_101055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:38:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.23/25.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.23/25.91  
% 34.23/25.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.23/25.91  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 34.23/25.91  
% 34.23/25.91  %Foreground sorts:
% 34.23/25.91  
% 34.23/25.91  
% 34.23/25.91  %Background operators:
% 34.23/25.91  
% 34.23/25.91  
% 34.23/25.91  %Foreground operators:
% 34.23/25.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.23/25.91  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 34.23/25.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 34.23/25.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.23/25.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 34.23/25.91  tff('#skF_2', type, '#skF_2': $i).
% 34.23/25.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 34.23/25.91  tff('#skF_3', type, '#skF_3': $i).
% 34.23/25.91  tff('#skF_1', type, '#skF_1': $i).
% 34.23/25.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.23/25.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.23/25.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.23/25.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 34.23/25.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.23/25.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 34.23/25.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 34.23/25.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.23/25.91  
% 34.39/25.93  tff(f_116, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 34.39/25.93  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 34.39/25.93  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 34.39/25.93  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 34.39/25.93  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 34.39/25.93  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 34.39/25.93  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 34.39/25.93  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 34.39/25.93  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 34.39/25.93  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 34.39/25.93  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 34.39/25.93  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 34.39/25.93  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 34.39/25.93  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 34.39/25.93  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 34.39/25.93  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 34.39/25.93  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 34.39/25.93  tff(c_32, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_84])).
% 34.39/25.93  tff(c_30, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_84])).
% 34.39/25.93  tff(c_315, plain, (![A_83]: (k9_relat_1(A_83, k1_relat_1(A_83))=k2_relat_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_60])).
% 34.39/25.93  tff(c_324, plain, (![A_27]: (k9_relat_1(k6_relat_1(A_27), A_27)=k2_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_315])).
% 34.39/25.93  tff(c_328, plain, (![A_27]: (k9_relat_1(k6_relat_1(A_27), A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32, c_324])).
% 34.39/25.93  tff(c_48, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 34.39/25.93  tff(c_110, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 34.39/25.93  tff(c_118, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_48, c_110])).
% 34.39/25.93  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 34.39/25.93  tff(c_132, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(k2_xboole_0(A_54, B_56), C_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.39/25.93  tff(c_143, plain, (![A_54, B_56]: (r1_tarski(A_54, k2_xboole_0(A_54, B_56)))), inference(resolution, [status(thm)], [c_6, c_132])).
% 34.39/25.93  tff(c_728, plain, (![B_113, A_114]: (k7_relat_1(B_113, A_114)=B_113 | ~r1_tarski(k1_relat_1(B_113), A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_104])).
% 34.39/25.93  tff(c_1160, plain, (![B_138, B_139]: (k7_relat_1(B_138, k2_xboole_0(k1_relat_1(B_138), B_139))=B_138 | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_143, c_728])).
% 34.39/25.93  tff(c_1221, plain, (![A_27, B_139]: (k7_relat_1(k6_relat_1(A_27), k2_xboole_0(A_27, B_139))=k6_relat_1(A_27) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1160])).
% 34.39/25.93  tff(c_1420, plain, (![A_147, B_148]: (k7_relat_1(k6_relat_1(A_147), k2_xboole_0(A_147, B_148))=k6_relat_1(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1221])).
% 34.39/25.93  tff(c_1489, plain, (k7_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k6_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_1420])).
% 34.39/25.93  tff(c_22, plain, (![A_16]: (k9_relat_1(A_16, k1_relat_1(A_16))=k2_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 34.39/25.93  tff(c_40, plain, (![A_32, B_33]: (k5_relat_1(k6_relat_1(A_32), B_33)=k7_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_98])).
% 34.39/25.93  tff(c_1356, plain, (![B_143, C_144, A_145]: (k9_relat_1(k5_relat_1(B_143, C_144), A_145)=k9_relat_1(C_144, k9_relat_1(B_143, A_145)) | ~v1_relat_1(C_144) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_80])).
% 34.39/25.93  tff(c_1375, plain, (![B_33, A_32, A_145]: (k9_relat_1(B_33, k9_relat_1(k6_relat_1(A_32), A_145))=k9_relat_1(k7_relat_1(B_33, A_32), A_145) | ~v1_relat_1(B_33) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1356])).
% 34.39/25.93  tff(c_2810, plain, (![B_203, A_204, A_205]: (k9_relat_1(B_203, k9_relat_1(k6_relat_1(A_204), A_205))=k9_relat_1(k7_relat_1(B_203, A_204), A_205) | ~v1_relat_1(B_203))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1375])).
% 34.39/25.93  tff(c_2876, plain, (![B_203, A_204]: (k9_relat_1(k7_relat_1(B_203, A_204), k1_relat_1(k6_relat_1(A_204)))=k9_relat_1(B_203, k2_relat_1(k6_relat_1(A_204))) | ~v1_relat_1(B_203) | ~v1_relat_1(k6_relat_1(A_204)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2810])).
% 34.39/25.93  tff(c_2892, plain, (![B_203, A_204]: (k9_relat_1(k7_relat_1(B_203, A_204), A_204)=k9_relat_1(B_203, A_204) | ~v1_relat_1(B_203))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32, c_30, c_2876])).
% 34.39/25.93  tff(c_605, plain, (![A_103, B_104]: (k5_relat_1(k6_relat_1(A_103), B_104)=k7_relat_1(B_104, A_103) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_98])).
% 34.39/25.93  tff(c_36, plain, (![B_29, A_28]: (r1_tarski(k5_relat_1(B_29, k6_relat_1(A_28)), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 34.39/25.93  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 34.39/25.93  tff(c_235, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 34.39/25.93  tff(c_240, plain, (![A_71, B_72]: (v1_relat_1(A_71) | ~v1_relat_1(B_72) | ~r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_14, c_235])).
% 34.39/25.93  tff(c_265, plain, (![B_29, A_28]: (v1_relat_1(k5_relat_1(B_29, k6_relat_1(A_28))) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_36, c_240])).
% 34.39/25.93  tff(c_612, plain, (![A_28, A_103]: (v1_relat_1(k7_relat_1(k6_relat_1(A_28), A_103)) | ~v1_relat_1(k6_relat_1(A_103)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_605, c_265])).
% 34.39/25.93  tff(c_628, plain, (![A_28, A_103]: (v1_relat_1(k7_relat_1(k6_relat_1(A_28), A_103)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_612])).
% 34.39/25.93  tff(c_622, plain, (![A_28, A_103]: (r1_tarski(k7_relat_1(k6_relat_1(A_28), A_103), k6_relat_1(A_103)) | ~v1_relat_1(k6_relat_1(A_103)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_605, c_36])).
% 34.39/25.93  tff(c_630, plain, (![A_28, A_103]: (r1_tarski(k7_relat_1(k6_relat_1(A_28), A_103), k6_relat_1(A_103)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_622])).
% 34.39/25.93  tff(c_1015, plain, (![B_129, A_130, C_131]: (r1_tarski(k9_relat_1(B_129, A_130), k9_relat_1(C_131, A_130)) | ~r1_tarski(B_129, C_131) | ~v1_relat_1(C_131) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_73])).
% 34.39/25.93  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 34.39/25.93  tff(c_4627, plain, (![B_258, A_259, C_260]: (k2_xboole_0(k9_relat_1(B_258, A_259), k9_relat_1(C_260, A_259))=k9_relat_1(C_260, A_259) | ~r1_tarski(B_258, C_260) | ~v1_relat_1(C_260) | ~v1_relat_1(B_258))), inference(resolution, [status(thm)], [c_1015, c_10])).
% 34.39/25.93  tff(c_4742, plain, (![A_27, B_258]: (k9_relat_1(k6_relat_1(A_27), A_27)=k2_xboole_0(k9_relat_1(B_258, A_27), A_27) | ~r1_tarski(B_258, k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(B_258))), inference(superposition, [status(thm), theory('equality')], [c_328, c_4627])).
% 34.39/25.93  tff(c_13099, plain, (![B_515, A_516]: (k2_xboole_0(k9_relat_1(B_515, A_516), A_516)=A_516 | ~r1_tarski(B_515, k6_relat_1(A_516)) | ~v1_relat_1(B_515))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_328, c_4742])).
% 34.39/25.93  tff(c_13221, plain, (![A_28, A_103]: (k2_xboole_0(k9_relat_1(k7_relat_1(k6_relat_1(A_28), A_103), A_103), A_103)=A_103 | ~v1_relat_1(k7_relat_1(k6_relat_1(A_28), A_103)))), inference(resolution, [status(thm)], [c_630, c_13099])).
% 34.39/25.93  tff(c_13400, plain, (![A_517, A_518]: (k2_xboole_0(k9_relat_1(k7_relat_1(k6_relat_1(A_517), A_518), A_518), A_518)=A_518)), inference(demodulation, [status(thm), theory('equality')], [c_628, c_13221])).
% 34.39/25.93  tff(c_13511, plain, (![A_517, A_204]: (k2_xboole_0(k9_relat_1(k6_relat_1(A_517), A_204), A_204)=A_204 | ~v1_relat_1(k6_relat_1(A_517)))), inference(superposition, [status(thm), theory('equality')], [c_2892, c_13400])).
% 34.39/25.93  tff(c_13559, plain, (![A_519, A_520]: (k2_xboole_0(k9_relat_1(k6_relat_1(A_519), A_520), A_520)=A_520)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_13511])).
% 34.39/25.93  tff(c_1187, plain, (![A_28, B_139]: (r1_tarski(k6_relat_1(A_28), k6_relat_1(k2_xboole_0(k1_relat_1(k6_relat_1(A_28)), B_139))) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_1160, c_630])).
% 34.39/25.93  tff(c_1232, plain, (![A_28, B_139]: (r1_tarski(k6_relat_1(A_28), k6_relat_1(k2_xboole_0(A_28, B_139))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30, c_1187])).
% 34.39/25.93  tff(c_13642, plain, (![A_519, A_520]: (r1_tarski(k6_relat_1(k9_relat_1(k6_relat_1(A_519), A_520)), k6_relat_1(A_520)))), inference(superposition, [status(thm), theory('equality')], [c_13559, c_1232])).
% 34.39/25.93  tff(c_1241, plain, (![A_27, B_139]: (k7_relat_1(k6_relat_1(A_27), k2_xboole_0(A_27, B_139))=k6_relat_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1221])).
% 34.39/25.93  tff(c_230, plain, (![B_67, A_68]: (r1_tarski(k5_relat_1(B_67, k6_relat_1(A_68)), B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_90])).
% 34.39/25.93  tff(c_778, plain, (![B_117, A_118]: (k2_xboole_0(k5_relat_1(B_117, k6_relat_1(A_118)), B_117)=B_117 | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_230, c_10])).
% 34.39/25.93  tff(c_806, plain, (![A_118, A_32]: (k2_xboole_0(k7_relat_1(k6_relat_1(A_118), A_32), k6_relat_1(A_32))=k6_relat_1(A_32) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_118)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_778])).
% 34.39/25.93  tff(c_811, plain, (![A_118, A_32]: (k2_xboole_0(k7_relat_1(k6_relat_1(A_118), A_32), k6_relat_1(A_32))=k6_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_806])).
% 34.39/25.93  tff(c_742, plain, (![A_27, A_114]: (k7_relat_1(k6_relat_1(A_27), A_114)=k6_relat_1(A_27) | ~r1_tarski(A_27, A_114) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_728])).
% 34.39/25.93  tff(c_751, plain, (![A_27, A_114]: (k7_relat_1(k6_relat_1(A_27), A_114)=k6_relat_1(A_27) | ~r1_tarski(A_27, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_742])).
% 34.39/25.93  tff(c_216, plain, (![B_65, A_66]: (r1_tarski(k1_relat_1(k7_relat_1(B_65, A_66)), A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_94])).
% 34.39/25.93  tff(c_858, plain, (![B_121, A_122]: (k2_xboole_0(k1_relat_1(k7_relat_1(B_121, A_122)), A_122)=A_122 | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_216, c_10])).
% 34.39/25.93  tff(c_144, plain, (![A_57, B_58]: (r1_tarski(A_57, k2_xboole_0(A_57, B_58)))), inference(resolution, [status(thm)], [c_6, c_132])).
% 34.39/25.93  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.39/25.93  tff(c_158, plain, (![A_3, B_4, B_58]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_58)))), inference(resolution, [status(thm)], [c_144, c_8])).
% 34.39/25.93  tff(c_4790, plain, (![B_261, A_262, B_263]: (r1_tarski(k1_relat_1(k7_relat_1(B_261, A_262)), k2_xboole_0(A_262, B_263)) | ~v1_relat_1(B_261))), inference(superposition, [status(thm), theory('equality')], [c_858, c_158])).
% 34.39/25.93  tff(c_4846, plain, (![A_27, A_114, B_263]: (r1_tarski(k1_relat_1(k6_relat_1(A_27)), k2_xboole_0(A_114, B_263)) | ~v1_relat_1(k6_relat_1(A_27)) | ~r1_tarski(A_27, A_114))), inference(superposition, [status(thm), theory('equality')], [c_751, c_4790])).
% 34.39/25.93  tff(c_4896, plain, (![A_264, A_265, B_266]: (r1_tarski(A_264, k2_xboole_0(A_265, B_266)) | ~r1_tarski(A_264, A_265))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30, c_4846])).
% 34.39/25.93  tff(c_239, plain, (![A_8, B_9]: (v1_relat_1(A_8) | ~v1_relat_1(B_9) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_14, c_235])).
% 34.39/25.93  tff(c_5665, plain, (![A_288, A_289, B_290]: (v1_relat_1(A_288) | ~v1_relat_1(k2_xboole_0(A_289, B_290)) | ~r1_tarski(A_288, A_289))), inference(resolution, [status(thm)], [c_4896, c_239])).
% 34.39/25.93  tff(c_5681, plain, (![A_288, A_32, A_118]: (v1_relat_1(A_288) | ~v1_relat_1(k6_relat_1(A_32)) | ~r1_tarski(A_288, k7_relat_1(k6_relat_1(A_118), A_32)))), inference(superposition, [status(thm), theory('equality')], [c_811, c_5665])).
% 34.39/25.93  tff(c_5800, plain, (![A_292, A_293, A_294]: (v1_relat_1(A_292) | ~r1_tarski(A_292, k7_relat_1(k6_relat_1(A_293), A_294)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5681])).
% 34.39/25.93  tff(c_5880, plain, (![A_295, A_296]: (v1_relat_1(A_295) | ~r1_tarski(A_295, k6_relat_1(A_296)))), inference(superposition, [status(thm), theory('equality')], [c_1241, c_5800])).
% 34.39/25.93  tff(c_5988, plain, (![A_296, A_28]: (v1_relat_1(k5_relat_1(k6_relat_1(A_296), k6_relat_1(A_28))) | ~v1_relat_1(k6_relat_1(A_296)))), inference(resolution, [status(thm)], [c_36, c_5880])).
% 34.39/25.93  tff(c_6070, plain, (![A_296, A_28]: (v1_relat_1(k5_relat_1(k6_relat_1(A_296), k6_relat_1(A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5988])).
% 34.39/25.93  tff(c_34, plain, (![A_28, B_29]: (r1_tarski(k5_relat_1(k6_relat_1(A_28), B_29), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 34.39/25.93  tff(c_347, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 34.39/25.93  tff(c_2503, plain, (![A_186, B_187]: (k5_relat_1(k6_relat_1(A_186), B_187)=B_187 | ~r1_tarski(B_187, k5_relat_1(k6_relat_1(A_186), B_187)) | ~v1_relat_1(B_187))), inference(resolution, [status(thm)], [c_34, c_347])).
% 34.39/25.93  tff(c_18635, plain, (![A_621, B_622]: (k5_relat_1(k6_relat_1(A_621), B_622)=B_622 | ~r1_tarski(B_622, k7_relat_1(B_622, A_621)) | ~v1_relat_1(B_622) | ~v1_relat_1(B_622))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2503])).
% 34.39/25.93  tff(c_18686, plain, (k5_relat_1(k6_relat_1('#skF_3'), k6_relat_1('#skF_2'))=k6_relat_1('#skF_2') | ~r1_tarski(k6_relat_1('#skF_2'), k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1489, c_18635])).
% 34.39/25.93  tff(c_18728, plain, (k5_relat_1(k6_relat_1('#skF_3'), k6_relat_1('#skF_2'))=k6_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_6, c_18686])).
% 34.39/25.93  tff(c_1379, plain, (![C_144, B_143]: (k9_relat_1(C_144, k9_relat_1(B_143, k1_relat_1(k5_relat_1(B_143, C_144))))=k2_relat_1(k5_relat_1(B_143, C_144)) | ~v1_relat_1(C_144) | ~v1_relat_1(B_143) | ~v1_relat_1(k5_relat_1(B_143, C_144)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1356])).
% 34.39/25.93  tff(c_18779, plain, (k9_relat_1(k6_relat_1('#skF_2'), k9_relat_1(k6_relat_1('#skF_3'), k1_relat_1(k6_relat_1('#skF_2'))))=k2_relat_1(k5_relat_1(k6_relat_1('#skF_3'), k6_relat_1('#skF_2'))) | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_3')) | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_3'), k6_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_18728, c_1379])).
% 34.39/25.93  tff(c_18837, plain, (k9_relat_1(k6_relat_1('#skF_2'), k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6070, c_18, c_18, c_32, c_18728, c_30, c_18779])).
% 34.39/25.93  tff(c_19052, plain, (r1_tarski(k6_relat_1('#skF_2'), k6_relat_1(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_18837, c_13642])).
% 34.39/25.93  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 34.39/25.93  tff(c_19284, plain, (k6_relat_1(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))=k6_relat_1('#skF_2') | ~r1_tarski(k6_relat_1(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')), k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_19052, c_2])).
% 34.39/25.93  tff(c_19308, plain, (k6_relat_1(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))=k6_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13642, c_19284])).
% 34.39/25.93  tff(c_2872, plain, (![A_204, A_205]: (k9_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_204), A_205)), A_204), A_205)=k9_relat_1(k6_relat_1(A_204), A_205) | ~v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_204), A_205))))), inference(superposition, [status(thm), theory('equality')], [c_328, c_2810])).
% 34.39/25.93  tff(c_2890, plain, (![A_204, A_205]: (k9_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_204), A_205)), A_204), A_205)=k9_relat_1(k6_relat_1(A_204), A_205))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2872])).
% 34.39/25.93  tff(c_19389, plain, (k9_relat_1(k7_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_2')=k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19308, c_2890])).
% 34.39/25.93  tff(c_19793, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_328, c_1489, c_19389])).
% 34.39/25.93  tff(c_1383, plain, (![B_33, A_32, A_145]: (k9_relat_1(B_33, k9_relat_1(k6_relat_1(A_32), A_145))=k9_relat_1(k7_relat_1(B_33, A_32), A_145) | ~v1_relat_1(B_33))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1375])).
% 34.39/25.93  tff(c_100804, plain, (![B_1668]: (k9_relat_1(k7_relat_1(B_1668, '#skF_3'), '#skF_2')=k9_relat_1(B_1668, '#skF_2') | ~v1_relat_1(B_1668))), inference(superposition, [status(thm), theory('equality')], [c_19793, c_1383])).
% 34.39/25.93  tff(c_46, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 34.39/25.93  tff(c_101055, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100804, c_46])).
% 34.39/25.93  tff(c_101129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_101055])).
% 34.39/25.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.39/25.93  
% 34.39/25.93  Inference rules
% 34.39/25.93  ----------------------
% 34.39/25.93  #Ref     : 0
% 34.39/25.93  #Sup     : 24127
% 34.39/25.93  #Fact    : 0
% 34.39/25.93  #Define  : 0
% 34.39/25.93  #Split   : 10
% 34.39/25.93  #Chain   : 0
% 34.39/25.93  #Close   : 0
% 34.39/25.93  
% 34.39/25.93  Ordering : KBO
% 34.39/25.93  
% 34.39/25.93  Simplification rules
% 34.39/25.93  ----------------------
% 34.39/25.93  #Subsume      : 6012
% 34.39/25.93  #Demod        : 15870
% 34.39/25.93  #Tautology    : 5861
% 34.39/25.93  #SimpNegUnit  : 195
% 34.39/25.93  #BackRed      : 14
% 34.39/25.93  
% 34.39/25.93  #Partial instantiations: 0
% 34.39/25.93  #Strategies tried      : 1
% 34.39/25.93  
% 34.39/25.93  Timing (in seconds)
% 34.39/25.93  ----------------------
% 34.39/25.93  Preprocessing        : 0.31
% 34.39/25.93  Parsing              : 0.18
% 34.39/25.93  CNF conversion       : 0.02
% 34.39/25.93  Main loop            : 24.85
% 34.39/25.93  Inferencing          : 2.41
% 34.39/25.93  Reduction            : 12.62
% 34.39/25.93  Demodulation         : 11.06
% 34.39/25.93  BG Simplification    : 0.29
% 34.39/25.93  Subsumption          : 8.64
% 34.39/25.93  Abstraction          : 0.42
% 34.39/25.93  MUC search           : 0.00
% 34.39/25.93  Cooper               : 0.00
% 34.39/25.94  Total                : 25.20
% 34.39/25.94  Index Insertion      : 0.00
% 34.39/25.94  Index Deletion       : 0.00
% 34.39/25.94  Index Matching       : 0.00
% 34.39/25.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
