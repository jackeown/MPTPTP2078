%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:24 EST 2020

% Result     : Theorem 5.99s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  124 (2373 expanded)
%              Number of leaves         :   39 ( 880 expanded)
%              Depth                    :   24
%              Number of atoms          :  187 (4897 expanded)
%              Number of equality atoms :   73 (1259 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_50,plain,(
    ! [A_51] : v1_relat_1(k6_relat_1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_509,plain,(
    ! [B_127,A_128] :
      ( k7_relat_1(B_127,k3_xboole_0(k1_relat_1(B_127),A_128)) = k7_relat_1(B_127,A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_552,plain,(
    ! [A_45,A_128] :
      ( k7_relat_1(k6_relat_1(A_45),k3_xboole_0(A_45,A_128)) = k7_relat_1(k6_relat_1(A_45),A_128)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_509])).

tff(c_569,plain,(
    ! [A_45,A_128] : k7_relat_1(k6_relat_1(A_45),k3_xboole_0(A_45,A_128)) = k7_relat_1(k6_relat_1(A_45),A_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_552])).

tff(c_52,plain,(
    ! [A_51] : v4_relat_1(k6_relat_1(A_51),A_51) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_224,plain,(
    ! [B_93,A_94] :
      ( k7_relat_1(B_93,A_94) = B_93
      | ~ v4_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_227,plain,(
    ! [A_51] :
      ( k7_relat_1(k6_relat_1(A_51),A_51) = k6_relat_1(A_51)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_52,c_224])).

tff(c_230,plain,(
    ! [A_51] : k7_relat_1(k6_relat_1(A_51),A_51) = k6_relat_1(A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_227])).

tff(c_179,plain,(
    ! [A_89,B_90] :
      ( k5_relat_1(k6_relat_1(A_89),B_90) = k7_relat_1(B_90,A_89)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_22,plain,(
    ! [B_29,A_28] :
      ( k5_relat_1(B_29,k6_relat_1(A_28)) = k8_relat_1(A_28,B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_186,plain,(
    ! [A_28,A_89] :
      ( k8_relat_1(A_28,k6_relat_1(A_89)) = k7_relat_1(k6_relat_1(A_28),A_89)
      | ~ v1_relat_1(k6_relat_1(A_89))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_22])).

tff(c_213,plain,(
    ! [A_28,A_89] : k8_relat_1(A_28,k6_relat_1(A_89)) = k7_relat_1(k6_relat_1(A_28),A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_186])).

tff(c_40,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_371,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(k2_relat_1(B_115),A_116) = k2_relat_1(k8_relat_1(A_116,B_115))
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_380,plain,(
    ! [A_116,A_45] :
      ( k2_relat_1(k8_relat_1(A_116,k6_relat_1(A_45))) = k3_xboole_0(A_45,A_116)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_371])).

tff(c_384,plain,(
    ! [A_116,A_45] : k2_relat_1(k7_relat_1(k6_relat_1(A_116),A_45)) = k3_xboole_0(A_45,A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_213,c_380])).

tff(c_123,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(k5_relat_1(B_74,k6_relat_1(A_75)),B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_14,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_116,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(A_17)
      | ~ v1_relat_1(B_18)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_14,c_112])).

tff(c_127,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(k5_relat_1(B_74,k6_relat_1(A_75)))
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_123,c_116])).

tff(c_190,plain,(
    ! [A_75,A_89] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_75),A_89))
      | ~ v1_relat_1(k6_relat_1(A_89))
      | ~ v1_relat_1(k6_relat_1(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_127])).

tff(c_215,plain,(
    ! [A_75,A_89] : v1_relat_1(k7_relat_1(k6_relat_1(A_75),A_89)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_190])).

tff(c_46,plain,(
    ! [B_48,A_47] :
      ( r1_tarski(k5_relat_1(B_48,k6_relat_1(A_47)),B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_194,plain,(
    ! [A_47,A_89] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_47),A_89),k6_relat_1(A_89))
      | ~ v1_relat_1(k6_relat_1(A_89))
      | ~ v1_relat_1(k6_relat_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_46])).

tff(c_217,plain,(
    ! [A_47,A_89] : r1_tarski(k7_relat_1(k6_relat_1(A_47),A_89),k6_relat_1(A_89)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_194])).

tff(c_750,plain,(
    ! [A_139,B_140] :
      ( r1_tarski(k2_relat_1(A_139),k2_relat_1(B_140))
      | ~ r1_tarski(A_139,B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_777,plain,(
    ! [A_139,A_45] :
      ( r1_tarski(k2_relat_1(A_139),A_45)
      | ~ r1_tarski(A_139,k6_relat_1(A_45))
      | ~ v1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_750])).

tff(c_915,plain,(
    ! [A_148,A_149] :
      ( r1_tarski(k2_relat_1(A_148),A_149)
      | ~ r1_tarski(A_148,k6_relat_1(A_149))
      | ~ v1_relat_1(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_777])).

tff(c_24,plain,(
    ! [A_30,B_31] :
      ( k8_relat_1(A_30,B_31) = B_31
      | ~ r1_tarski(k2_relat_1(B_31),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_999,plain,(
    ! [A_154,A_155] :
      ( k8_relat_1(A_154,A_155) = A_155
      | ~ r1_tarski(A_155,k6_relat_1(A_154))
      | ~ v1_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_915,c_24])).

tff(c_1027,plain,(
    ! [A_89,A_47] :
      ( k8_relat_1(A_89,k7_relat_1(k6_relat_1(A_47),A_89)) = k7_relat_1(k6_relat_1(A_47),A_89)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_47),A_89)) ) ),
    inference(resolution,[status(thm)],[c_217,c_999])).

tff(c_1472,plain,(
    ! [A_182,A_183] : k8_relat_1(A_182,k7_relat_1(k6_relat_1(A_183),A_182)) = k7_relat_1(k6_relat_1(A_183),A_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_1027])).

tff(c_26,plain,(
    ! [A_32,C_34,B_33] :
      ( k8_relat_1(A_32,k7_relat_1(C_34,B_33)) = k7_relat_1(k8_relat_1(A_32,C_34),B_33)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1482,plain,(
    ! [A_182,A_183] :
      ( k7_relat_1(k8_relat_1(A_182,k6_relat_1(A_183)),A_182) = k7_relat_1(k6_relat_1(A_183),A_182)
      | ~ v1_relat_1(k6_relat_1(A_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1472,c_26])).

tff(c_1516,plain,(
    ! [A_182,A_183] : k7_relat_1(k7_relat_1(k6_relat_1(A_182),A_183),A_182) = k7_relat_1(k6_relat_1(A_183),A_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_213,c_1482])).

tff(c_28,plain,(
    ! [B_36,A_35] :
      ( k7_relat_1(B_36,k3_xboole_0(k1_relat_1(B_36),A_35)) = k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1717,plain,(
    ! [A_191,A_192] : k7_relat_1(k7_relat_1(k6_relat_1(A_191),A_192),A_191) = k7_relat_1(k6_relat_1(A_192),A_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_213,c_1482])).

tff(c_1750,plain,(
    ! [A_191,A_35] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_191)),A_35)),A_191) = k7_relat_1(k7_relat_1(k6_relat_1(A_191),A_35),A_191)
      | ~ v1_relat_1(k6_relat_1(A_191)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1717])).

tff(c_2116,plain,(
    ! [A_203,A_204] : k7_relat_1(k6_relat_1(k3_xboole_0(A_203,A_204)),A_203) = k7_relat_1(k6_relat_1(A_204),A_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1516,c_38,c_1750])).

tff(c_2152,plain,(
    ! [A_203,A_204] : k3_xboole_0(A_203,k3_xboole_0(A_203,A_204)) = k2_relat_1(k7_relat_1(k6_relat_1(A_204),A_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_384])).

tff(c_2224,plain,(
    ! [A_203,A_204] : k3_xboole_0(A_203,k3_xboole_0(A_203,A_204)) = k3_xboole_0(A_203,A_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_2152])).

tff(c_44,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_47),B_48),B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_200,plain,(
    ! [B_90,A_89] :
      ( r1_tarski(k7_relat_1(B_90,A_89),B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_44])).

tff(c_1733,plain,(
    ! [A_192,A_191] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_192),A_191),k7_relat_1(k6_relat_1(A_191),A_192))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_191),A_192))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_191),A_192)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1717,c_200])).

tff(c_1764,plain,(
    ! [A_192,A_191] : r1_tarski(k7_relat_1(k6_relat_1(A_192),A_191),k7_relat_1(k6_relat_1(A_191),A_192)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_215,c_1733])).

tff(c_385,plain,(
    ! [A_117,A_118] : k2_relat_1(k7_relat_1(k6_relat_1(A_117),A_118)) = k3_xboole_0(A_118,A_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_213,c_380])).

tff(c_403,plain,(
    ! [A_51] : k3_xboole_0(A_51,A_51) = k2_relat_1(k6_relat_1(A_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_385])).

tff(c_411,plain,(
    ! [A_51] : k3_xboole_0(A_51,A_51) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_403])).

tff(c_306,plain,(
    ! [A_107,B_108] :
      ( k8_relat_1(A_107,B_108) = B_108
      | ~ r1_tarski(k2_relat_1(B_108),A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_309,plain,(
    ! [A_107,A_45] :
      ( k8_relat_1(A_107,k6_relat_1(A_45)) = k6_relat_1(A_45)
      | ~ r1_tarski(A_45,A_107)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_306])).

tff(c_322,plain,(
    ! [A_111,A_112] :
      ( k7_relat_1(k6_relat_1(A_111),A_112) = k6_relat_1(A_112)
      | ~ r1_tarski(A_112,A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_213,c_309])).

tff(c_328,plain,(
    ! [A_112,A_111] :
      ( r1_tarski(k6_relat_1(A_112),k6_relat_1(A_111))
      | ~ v1_relat_1(k6_relat_1(A_111))
      | ~ v1_relat_1(k6_relat_1(A_111))
      | ~ r1_tarski(A_112,A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_200])).

tff(c_355,plain,(
    ! [A_112,A_111] :
      ( r1_tarski(k6_relat_1(A_112),k6_relat_1(A_111))
      | ~ r1_tarski(A_112,A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_328])).

tff(c_311,plain,(
    ! [A_107,A_45] :
      ( k7_relat_1(k6_relat_1(A_107),A_45) = k6_relat_1(A_45)
      | ~ r1_tarski(A_45,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_213,c_309])).

tff(c_400,plain,(
    ! [A_45,A_107] :
      ( k3_xboole_0(A_45,A_107) = k2_relat_1(k6_relat_1(A_45))
      | ~ r1_tarski(A_45,A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_385])).

tff(c_438,plain,(
    ! [A_124,A_125] :
      ( k3_xboole_0(A_124,A_125) = A_124
      | ~ r1_tarski(A_124,A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_400])).

tff(c_719,plain,(
    ! [A_137,A_138] :
      ( k3_xboole_0(k6_relat_1(A_137),k6_relat_1(A_138)) = k6_relat_1(A_137)
      | ~ r1_tarski(A_137,A_138) ) ),
    inference(resolution,[status(thm)],[c_355,c_438])).

tff(c_516,plain,(
    ! [A_116,A_128] :
      ( k3_xboole_0(k3_xboole_0(k1_relat_1(k6_relat_1(A_116)),A_128),A_116) = k2_relat_1(k7_relat_1(k6_relat_1(A_116),A_128))
      | ~ v1_relat_1(k6_relat_1(A_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_384])).

tff(c_555,plain,(
    ! [A_116,A_128] : k3_xboole_0(k3_xboole_0(A_116,A_128),A_116) = k3_xboole_0(A_128,A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_384,c_38,c_516])).

tff(c_731,plain,(
    ! [A_138,A_137] :
      ( k3_xboole_0(k6_relat_1(A_138),k6_relat_1(A_137)) = k3_xboole_0(k6_relat_1(A_137),k6_relat_1(A_137))
      | ~ r1_tarski(A_137,A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_555])).

tff(c_1851,plain,(
    ! [A_197,A_198] :
      ( k3_xboole_0(k6_relat_1(A_197),k6_relat_1(A_198)) = k6_relat_1(A_198)
      | ~ r1_tarski(A_198,A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_731])).

tff(c_463,plain,(
    ! [A_112,A_111] :
      ( k3_xboole_0(k6_relat_1(A_112),k6_relat_1(A_111)) = k6_relat_1(A_112)
      | ~ r1_tarski(A_112,A_111) ) ),
    inference(resolution,[status(thm)],[c_355,c_438])).

tff(c_2532,plain,(
    ! [A_214,A_213] :
      ( k6_relat_1(A_214) = k6_relat_1(A_213)
      | ~ r1_tarski(A_214,A_213)
      | ~ r1_tarski(A_213,A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1851,c_463])).

tff(c_2536,plain,(
    ! [A_192,A_191] :
      ( k6_relat_1(k7_relat_1(k6_relat_1(A_192),A_191)) = k6_relat_1(k7_relat_1(k6_relat_1(A_191),A_192))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_191),A_192),k7_relat_1(k6_relat_1(A_192),A_191)) ) ),
    inference(resolution,[status(thm)],[c_1764,c_2532])).

tff(c_2701,plain,(
    ! [A_220,A_219] : k6_relat_1(k7_relat_1(k6_relat_1(A_220),A_219)) = k6_relat_1(k7_relat_1(k6_relat_1(A_219),A_220)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_2536])).

tff(c_3644,plain,(
    ! [A_236,A_237] : k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_236),A_237))) = k7_relat_1(k6_relat_1(A_237),A_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_2701,c_38])).

tff(c_3715,plain,(
    ! [A_239,A_238] : k7_relat_1(k6_relat_1(A_239),A_238) = k7_relat_1(k6_relat_1(A_238),A_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_3644,c_38])).

tff(c_4125,plain,(
    ! [A_246,A_247] : k2_relat_1(k7_relat_1(k6_relat_1(A_246),A_247)) = k3_xboole_0(A_246,A_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_3715,c_384])).

tff(c_4180,plain,(
    ! [A_246,A_35] :
      ( k3_xboole_0(A_246,k3_xboole_0(k1_relat_1(k6_relat_1(A_246)),A_35)) = k2_relat_1(k7_relat_1(k6_relat_1(A_246),A_35))
      | ~ v1_relat_1(k6_relat_1(A_246)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4125])).

tff(c_4213,plain,(
    ! [A_35,A_246] : k3_xboole_0(A_35,A_246) = k3_xboole_0(A_246,A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2224,c_384,c_38,c_4180])).

tff(c_4320,plain,(
    ! [A_251,A_250] : k3_xboole_0(A_251,A_250) = k3_xboole_0(A_250,A_251) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2224,c_384,c_38,c_4180])).

tff(c_4908,plain,(
    ! [A_261,A_262] : k3_xboole_0(A_261,k3_xboole_0(A_262,A_261)) = k3_xboole_0(A_261,A_262) ),
    inference(superposition,[status(thm),theory(equality)],[c_4320,c_2224])).

tff(c_4486,plain,(
    ! [A_116,A_128] : k3_xboole_0(A_116,k3_xboole_0(A_116,A_128)) = k3_xboole_0(A_128,A_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_4320])).

tff(c_4920,plain,(
    ! [A_262,A_261] : k3_xboole_0(k3_xboole_0(A_262,A_261),A_261) = k3_xboole_0(A_261,k3_xboole_0(A_261,A_262)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4908,c_4486])).

tff(c_5789,plain,(
    ! [A_276,A_277] : k3_xboole_0(k3_xboole_0(A_276,A_277),A_277) = k3_xboole_0(A_277,A_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2224,c_4920])).

tff(c_6057,plain,(
    ! [A_283,A_284] : k3_xboole_0(k3_xboole_0(A_283,A_284),A_283) = k3_xboole_0(A_283,A_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_4213,c_5789])).

tff(c_1771,plain,(
    ! [A_191,A_35] : k7_relat_1(k6_relat_1(k3_xboole_0(A_191,A_35)),A_191) = k7_relat_1(k6_relat_1(A_35),A_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1516,c_38,c_1750])).

tff(c_6120,plain,(
    ! [A_283,A_284] : k7_relat_1(k6_relat_1(k3_xboole_0(A_283,A_284)),k3_xboole_0(A_283,A_284)) = k7_relat_1(k6_relat_1(A_283),k3_xboole_0(A_283,A_284)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6057,c_1771])).

tff(c_6236,plain,(
    ! [A_283,A_284] : k7_relat_1(k6_relat_1(A_283),A_284) = k6_relat_1(k3_xboole_0(A_283,A_284)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_230,c_6120])).

tff(c_56,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_203,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_56])).

tff(c_219,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_203])).

tff(c_6990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.99/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.99/2.17  
% 5.99/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.99/2.18  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.99/2.18  
% 5.99/2.18  %Foreground sorts:
% 5.99/2.18  
% 5.99/2.18  
% 5.99/2.18  %Background operators:
% 5.99/2.18  
% 5.99/2.18  
% 5.99/2.18  %Foreground operators:
% 5.99/2.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.99/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.99/2.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.99/2.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.99/2.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.99/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.99/2.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.99/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.99/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.99/2.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.99/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.99/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.99/2.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.99/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.99/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.99/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.99/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.99/2.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.99/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.99/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.99/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.99/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.99/2.18  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.99/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.99/2.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.99/2.18  
% 5.99/2.20  tff(f_121, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 5.99/2.20  tff(f_103, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.99/2.20  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 5.99/2.20  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.99/2.20  tff(f_115, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.99/2.20  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 5.99/2.20  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 5.99/2.20  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 5.99/2.20  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.99/2.20  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.99/2.20  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 5.99/2.20  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 5.99/2.20  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 5.99/2.20  tff(f_124, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 5.99/2.20  tff(c_50, plain, (![A_51]: (v1_relat_1(k6_relat_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.99/2.20  tff(c_38, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.99/2.20  tff(c_509, plain, (![B_127, A_128]: (k7_relat_1(B_127, k3_xboole_0(k1_relat_1(B_127), A_128))=k7_relat_1(B_127, A_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.20  tff(c_552, plain, (![A_45, A_128]: (k7_relat_1(k6_relat_1(A_45), k3_xboole_0(A_45, A_128))=k7_relat_1(k6_relat_1(A_45), A_128) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_509])).
% 5.99/2.20  tff(c_569, plain, (![A_45, A_128]: (k7_relat_1(k6_relat_1(A_45), k3_xboole_0(A_45, A_128))=k7_relat_1(k6_relat_1(A_45), A_128))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_552])).
% 5.99/2.20  tff(c_52, plain, (![A_51]: (v4_relat_1(k6_relat_1(A_51), A_51))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.99/2.20  tff(c_224, plain, (![B_93, A_94]: (k7_relat_1(B_93, A_94)=B_93 | ~v4_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.99/2.20  tff(c_227, plain, (![A_51]: (k7_relat_1(k6_relat_1(A_51), A_51)=k6_relat_1(A_51) | ~v1_relat_1(k6_relat_1(A_51)))), inference(resolution, [status(thm)], [c_52, c_224])).
% 5.99/2.20  tff(c_230, plain, (![A_51]: (k7_relat_1(k6_relat_1(A_51), A_51)=k6_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_227])).
% 5.99/2.20  tff(c_179, plain, (![A_89, B_90]: (k5_relat_1(k6_relat_1(A_89), B_90)=k7_relat_1(B_90, A_89) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.99/2.20  tff(c_22, plain, (![B_29, A_28]: (k5_relat_1(B_29, k6_relat_1(A_28))=k8_relat_1(A_28, B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.99/2.20  tff(c_186, plain, (![A_28, A_89]: (k8_relat_1(A_28, k6_relat_1(A_89))=k7_relat_1(k6_relat_1(A_28), A_89) | ~v1_relat_1(k6_relat_1(A_89)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_22])).
% 5.99/2.20  tff(c_213, plain, (![A_28, A_89]: (k8_relat_1(A_28, k6_relat_1(A_89))=k7_relat_1(k6_relat_1(A_28), A_89))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_186])).
% 5.99/2.20  tff(c_40, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.99/2.20  tff(c_371, plain, (![B_115, A_116]: (k3_xboole_0(k2_relat_1(B_115), A_116)=k2_relat_1(k8_relat_1(A_116, B_115)) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.99/2.20  tff(c_380, plain, (![A_116, A_45]: (k2_relat_1(k8_relat_1(A_116, k6_relat_1(A_45)))=k3_xboole_0(A_45, A_116) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_371])).
% 5.99/2.20  tff(c_384, plain, (![A_116, A_45]: (k2_relat_1(k7_relat_1(k6_relat_1(A_116), A_45))=k3_xboole_0(A_45, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_213, c_380])).
% 5.99/2.20  tff(c_123, plain, (![B_74, A_75]: (r1_tarski(k5_relat_1(B_74, k6_relat_1(A_75)), B_74) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.99/2.20  tff(c_14, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.99/2.20  tff(c_112, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.99/2.20  tff(c_116, plain, (![A_17, B_18]: (v1_relat_1(A_17) | ~v1_relat_1(B_18) | ~r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_14, c_112])).
% 5.99/2.20  tff(c_127, plain, (![B_74, A_75]: (v1_relat_1(k5_relat_1(B_74, k6_relat_1(A_75))) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_123, c_116])).
% 5.99/2.20  tff(c_190, plain, (![A_75, A_89]: (v1_relat_1(k7_relat_1(k6_relat_1(A_75), A_89)) | ~v1_relat_1(k6_relat_1(A_89)) | ~v1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_127])).
% 5.99/2.20  tff(c_215, plain, (![A_75, A_89]: (v1_relat_1(k7_relat_1(k6_relat_1(A_75), A_89)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_190])).
% 5.99/2.20  tff(c_46, plain, (![B_48, A_47]: (r1_tarski(k5_relat_1(B_48, k6_relat_1(A_47)), B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.99/2.20  tff(c_194, plain, (![A_47, A_89]: (r1_tarski(k7_relat_1(k6_relat_1(A_47), A_89), k6_relat_1(A_89)) | ~v1_relat_1(k6_relat_1(A_89)) | ~v1_relat_1(k6_relat_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_46])).
% 5.99/2.20  tff(c_217, plain, (![A_47, A_89]: (r1_tarski(k7_relat_1(k6_relat_1(A_47), A_89), k6_relat_1(A_89)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_194])).
% 5.99/2.20  tff(c_750, plain, (![A_139, B_140]: (r1_tarski(k2_relat_1(A_139), k2_relat_1(B_140)) | ~r1_tarski(A_139, B_140) | ~v1_relat_1(B_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.99/2.20  tff(c_777, plain, (![A_139, A_45]: (r1_tarski(k2_relat_1(A_139), A_45) | ~r1_tarski(A_139, k6_relat_1(A_45)) | ~v1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(A_139))), inference(superposition, [status(thm), theory('equality')], [c_40, c_750])).
% 5.99/2.20  tff(c_915, plain, (![A_148, A_149]: (r1_tarski(k2_relat_1(A_148), A_149) | ~r1_tarski(A_148, k6_relat_1(A_149)) | ~v1_relat_1(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_777])).
% 5.99/2.20  tff(c_24, plain, (![A_30, B_31]: (k8_relat_1(A_30, B_31)=B_31 | ~r1_tarski(k2_relat_1(B_31), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.99/2.20  tff(c_999, plain, (![A_154, A_155]: (k8_relat_1(A_154, A_155)=A_155 | ~r1_tarski(A_155, k6_relat_1(A_154)) | ~v1_relat_1(A_155))), inference(resolution, [status(thm)], [c_915, c_24])).
% 5.99/2.20  tff(c_1027, plain, (![A_89, A_47]: (k8_relat_1(A_89, k7_relat_1(k6_relat_1(A_47), A_89))=k7_relat_1(k6_relat_1(A_47), A_89) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_47), A_89)))), inference(resolution, [status(thm)], [c_217, c_999])).
% 5.99/2.20  tff(c_1472, plain, (![A_182, A_183]: (k8_relat_1(A_182, k7_relat_1(k6_relat_1(A_183), A_182))=k7_relat_1(k6_relat_1(A_183), A_182))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_1027])).
% 5.99/2.20  tff(c_26, plain, (![A_32, C_34, B_33]: (k8_relat_1(A_32, k7_relat_1(C_34, B_33))=k7_relat_1(k8_relat_1(A_32, C_34), B_33) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.99/2.20  tff(c_1482, plain, (![A_182, A_183]: (k7_relat_1(k8_relat_1(A_182, k6_relat_1(A_183)), A_182)=k7_relat_1(k6_relat_1(A_183), A_182) | ~v1_relat_1(k6_relat_1(A_183)))), inference(superposition, [status(thm), theory('equality')], [c_1472, c_26])).
% 5.99/2.20  tff(c_1516, plain, (![A_182, A_183]: (k7_relat_1(k7_relat_1(k6_relat_1(A_182), A_183), A_182)=k7_relat_1(k6_relat_1(A_183), A_182))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_213, c_1482])).
% 5.99/2.20  tff(c_28, plain, (![B_36, A_35]: (k7_relat_1(B_36, k3_xboole_0(k1_relat_1(B_36), A_35))=k7_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.20  tff(c_1717, plain, (![A_191, A_192]: (k7_relat_1(k7_relat_1(k6_relat_1(A_191), A_192), A_191)=k7_relat_1(k6_relat_1(A_192), A_191))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_213, c_1482])).
% 5.99/2.20  tff(c_1750, plain, (![A_191, A_35]: (k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_191)), A_35)), A_191)=k7_relat_1(k7_relat_1(k6_relat_1(A_191), A_35), A_191) | ~v1_relat_1(k6_relat_1(A_191)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1717])).
% 5.99/2.20  tff(c_2116, plain, (![A_203, A_204]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_203, A_204)), A_203)=k7_relat_1(k6_relat_1(A_204), A_203))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1516, c_38, c_1750])).
% 5.99/2.20  tff(c_2152, plain, (![A_203, A_204]: (k3_xboole_0(A_203, k3_xboole_0(A_203, A_204))=k2_relat_1(k7_relat_1(k6_relat_1(A_204), A_203)))), inference(superposition, [status(thm), theory('equality')], [c_2116, c_384])).
% 5.99/2.20  tff(c_2224, plain, (![A_203, A_204]: (k3_xboole_0(A_203, k3_xboole_0(A_203, A_204))=k3_xboole_0(A_203, A_204))), inference(demodulation, [status(thm), theory('equality')], [c_384, c_2152])).
% 5.99/2.20  tff(c_44, plain, (![A_47, B_48]: (r1_tarski(k5_relat_1(k6_relat_1(A_47), B_48), B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.99/2.20  tff(c_200, plain, (![B_90, A_89]: (r1_tarski(k7_relat_1(B_90, A_89), B_90) | ~v1_relat_1(B_90) | ~v1_relat_1(B_90))), inference(superposition, [status(thm), theory('equality')], [c_179, c_44])).
% 5.99/2.20  tff(c_1733, plain, (![A_192, A_191]: (r1_tarski(k7_relat_1(k6_relat_1(A_192), A_191), k7_relat_1(k6_relat_1(A_191), A_192)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_191), A_192)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_191), A_192)))), inference(superposition, [status(thm), theory('equality')], [c_1717, c_200])).
% 5.99/2.20  tff(c_1764, plain, (![A_192, A_191]: (r1_tarski(k7_relat_1(k6_relat_1(A_192), A_191), k7_relat_1(k6_relat_1(A_191), A_192)))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_215, c_1733])).
% 5.99/2.20  tff(c_385, plain, (![A_117, A_118]: (k2_relat_1(k7_relat_1(k6_relat_1(A_117), A_118))=k3_xboole_0(A_118, A_117))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_213, c_380])).
% 5.99/2.20  tff(c_403, plain, (![A_51]: (k3_xboole_0(A_51, A_51)=k2_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_230, c_385])).
% 5.99/2.20  tff(c_411, plain, (![A_51]: (k3_xboole_0(A_51, A_51)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_403])).
% 5.99/2.20  tff(c_306, plain, (![A_107, B_108]: (k8_relat_1(A_107, B_108)=B_108 | ~r1_tarski(k2_relat_1(B_108), A_107) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.99/2.20  tff(c_309, plain, (![A_107, A_45]: (k8_relat_1(A_107, k6_relat_1(A_45))=k6_relat_1(A_45) | ~r1_tarski(A_45, A_107) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_306])).
% 5.99/2.20  tff(c_322, plain, (![A_111, A_112]: (k7_relat_1(k6_relat_1(A_111), A_112)=k6_relat_1(A_112) | ~r1_tarski(A_112, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_213, c_309])).
% 5.99/2.20  tff(c_328, plain, (![A_112, A_111]: (r1_tarski(k6_relat_1(A_112), k6_relat_1(A_111)) | ~v1_relat_1(k6_relat_1(A_111)) | ~v1_relat_1(k6_relat_1(A_111)) | ~r1_tarski(A_112, A_111))), inference(superposition, [status(thm), theory('equality')], [c_322, c_200])).
% 5.99/2.20  tff(c_355, plain, (![A_112, A_111]: (r1_tarski(k6_relat_1(A_112), k6_relat_1(A_111)) | ~r1_tarski(A_112, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_328])).
% 5.99/2.20  tff(c_311, plain, (![A_107, A_45]: (k7_relat_1(k6_relat_1(A_107), A_45)=k6_relat_1(A_45) | ~r1_tarski(A_45, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_213, c_309])).
% 5.99/2.20  tff(c_400, plain, (![A_45, A_107]: (k3_xboole_0(A_45, A_107)=k2_relat_1(k6_relat_1(A_45)) | ~r1_tarski(A_45, A_107))), inference(superposition, [status(thm), theory('equality')], [c_311, c_385])).
% 5.99/2.20  tff(c_438, plain, (![A_124, A_125]: (k3_xboole_0(A_124, A_125)=A_124 | ~r1_tarski(A_124, A_125))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_400])).
% 5.99/2.20  tff(c_719, plain, (![A_137, A_138]: (k3_xboole_0(k6_relat_1(A_137), k6_relat_1(A_138))=k6_relat_1(A_137) | ~r1_tarski(A_137, A_138))), inference(resolution, [status(thm)], [c_355, c_438])).
% 5.99/2.20  tff(c_516, plain, (![A_116, A_128]: (k3_xboole_0(k3_xboole_0(k1_relat_1(k6_relat_1(A_116)), A_128), A_116)=k2_relat_1(k7_relat_1(k6_relat_1(A_116), A_128)) | ~v1_relat_1(k6_relat_1(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_509, c_384])).
% 5.99/2.20  tff(c_555, plain, (![A_116, A_128]: (k3_xboole_0(k3_xboole_0(A_116, A_128), A_116)=k3_xboole_0(A_128, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_384, c_38, c_516])).
% 5.99/2.20  tff(c_731, plain, (![A_138, A_137]: (k3_xboole_0(k6_relat_1(A_138), k6_relat_1(A_137))=k3_xboole_0(k6_relat_1(A_137), k6_relat_1(A_137)) | ~r1_tarski(A_137, A_138))), inference(superposition, [status(thm), theory('equality')], [c_719, c_555])).
% 5.99/2.20  tff(c_1851, plain, (![A_197, A_198]: (k3_xboole_0(k6_relat_1(A_197), k6_relat_1(A_198))=k6_relat_1(A_198) | ~r1_tarski(A_198, A_197))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_731])).
% 5.99/2.20  tff(c_463, plain, (![A_112, A_111]: (k3_xboole_0(k6_relat_1(A_112), k6_relat_1(A_111))=k6_relat_1(A_112) | ~r1_tarski(A_112, A_111))), inference(resolution, [status(thm)], [c_355, c_438])).
% 5.99/2.20  tff(c_2532, plain, (![A_214, A_213]: (k6_relat_1(A_214)=k6_relat_1(A_213) | ~r1_tarski(A_214, A_213) | ~r1_tarski(A_213, A_214))), inference(superposition, [status(thm), theory('equality')], [c_1851, c_463])).
% 5.99/2.20  tff(c_2536, plain, (![A_192, A_191]: (k6_relat_1(k7_relat_1(k6_relat_1(A_192), A_191))=k6_relat_1(k7_relat_1(k6_relat_1(A_191), A_192)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_191), A_192), k7_relat_1(k6_relat_1(A_192), A_191)))), inference(resolution, [status(thm)], [c_1764, c_2532])).
% 5.99/2.20  tff(c_2701, plain, (![A_220, A_219]: (k6_relat_1(k7_relat_1(k6_relat_1(A_220), A_219))=k6_relat_1(k7_relat_1(k6_relat_1(A_219), A_220)))), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_2536])).
% 5.99/2.20  tff(c_3644, plain, (![A_236, A_237]: (k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(A_236), A_237)))=k7_relat_1(k6_relat_1(A_237), A_236))), inference(superposition, [status(thm), theory('equality')], [c_2701, c_38])).
% 5.99/2.20  tff(c_3715, plain, (![A_239, A_238]: (k7_relat_1(k6_relat_1(A_239), A_238)=k7_relat_1(k6_relat_1(A_238), A_239))), inference(superposition, [status(thm), theory('equality')], [c_3644, c_38])).
% 5.99/2.20  tff(c_4125, plain, (![A_246, A_247]: (k2_relat_1(k7_relat_1(k6_relat_1(A_246), A_247))=k3_xboole_0(A_246, A_247))), inference(superposition, [status(thm), theory('equality')], [c_3715, c_384])).
% 5.99/2.20  tff(c_4180, plain, (![A_246, A_35]: (k3_xboole_0(A_246, k3_xboole_0(k1_relat_1(k6_relat_1(A_246)), A_35))=k2_relat_1(k7_relat_1(k6_relat_1(A_246), A_35)) | ~v1_relat_1(k6_relat_1(A_246)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4125])).
% 5.99/2.20  tff(c_4213, plain, (![A_35, A_246]: (k3_xboole_0(A_35, A_246)=k3_xboole_0(A_246, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2224, c_384, c_38, c_4180])).
% 5.99/2.20  tff(c_4320, plain, (![A_251, A_250]: (k3_xboole_0(A_251, A_250)=k3_xboole_0(A_250, A_251))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2224, c_384, c_38, c_4180])).
% 5.99/2.20  tff(c_4908, plain, (![A_261, A_262]: (k3_xboole_0(A_261, k3_xboole_0(A_262, A_261))=k3_xboole_0(A_261, A_262))), inference(superposition, [status(thm), theory('equality')], [c_4320, c_2224])).
% 5.99/2.20  tff(c_4486, plain, (![A_116, A_128]: (k3_xboole_0(A_116, k3_xboole_0(A_116, A_128))=k3_xboole_0(A_128, A_116))), inference(superposition, [status(thm), theory('equality')], [c_555, c_4320])).
% 5.99/2.20  tff(c_4920, plain, (![A_262, A_261]: (k3_xboole_0(k3_xboole_0(A_262, A_261), A_261)=k3_xboole_0(A_261, k3_xboole_0(A_261, A_262)))), inference(superposition, [status(thm), theory('equality')], [c_4908, c_4486])).
% 5.99/2.20  tff(c_5789, plain, (![A_276, A_277]: (k3_xboole_0(k3_xboole_0(A_276, A_277), A_277)=k3_xboole_0(A_277, A_276))), inference(demodulation, [status(thm), theory('equality')], [c_2224, c_4920])).
% 5.99/2.20  tff(c_6057, plain, (![A_283, A_284]: (k3_xboole_0(k3_xboole_0(A_283, A_284), A_283)=k3_xboole_0(A_283, A_284))), inference(superposition, [status(thm), theory('equality')], [c_4213, c_5789])).
% 5.99/2.20  tff(c_1771, plain, (![A_191, A_35]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_191, A_35)), A_191)=k7_relat_1(k6_relat_1(A_35), A_191))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1516, c_38, c_1750])).
% 5.99/2.20  tff(c_6120, plain, (![A_283, A_284]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_283, A_284)), k3_xboole_0(A_283, A_284))=k7_relat_1(k6_relat_1(A_283), k3_xboole_0(A_283, A_284)))), inference(superposition, [status(thm), theory('equality')], [c_6057, c_1771])).
% 5.99/2.20  tff(c_6236, plain, (![A_283, A_284]: (k7_relat_1(k6_relat_1(A_283), A_284)=k6_relat_1(k3_xboole_0(A_283, A_284)))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_230, c_6120])).
% 5.99/2.20  tff(c_56, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.99/2.20  tff(c_203, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_56])).
% 5.99/2.20  tff(c_219, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_203])).
% 5.99/2.20  tff(c_6990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6236, c_219])).
% 5.99/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.99/2.20  
% 5.99/2.20  Inference rules
% 5.99/2.20  ----------------------
% 5.99/2.20  #Ref     : 0
% 5.99/2.20  #Sup     : 1733
% 5.99/2.20  #Fact    : 0
% 5.99/2.20  #Define  : 0
% 5.99/2.20  #Split   : 1
% 5.99/2.20  #Chain   : 0
% 5.99/2.20  #Close   : 0
% 5.99/2.20  
% 5.99/2.20  Ordering : KBO
% 5.99/2.20  
% 5.99/2.20  Simplification rules
% 5.99/2.20  ----------------------
% 5.99/2.20  #Subsume      : 220
% 5.99/2.20  #Demod        : 1403
% 5.99/2.20  #Tautology    : 708
% 5.99/2.20  #SimpNegUnit  : 0
% 5.99/2.20  #BackRed      : 38
% 5.99/2.20  
% 5.99/2.20  #Partial instantiations: 0
% 5.99/2.20  #Strategies tried      : 1
% 5.99/2.20  
% 5.99/2.20  Timing (in seconds)
% 5.99/2.20  ----------------------
% 5.99/2.20  Preprocessing        : 0.33
% 5.99/2.20  Parsing              : 0.18
% 5.99/2.20  CNF conversion       : 0.02
% 5.99/2.20  Main loop            : 1.09
% 5.99/2.20  Inferencing          : 0.34
% 5.99/2.20  Reduction            : 0.45
% 5.99/2.20  Demodulation         : 0.36
% 5.99/2.20  BG Simplification    : 0.05
% 5.99/2.20  Subsumption          : 0.18
% 5.99/2.20  Abstraction          : 0.07
% 5.99/2.20  MUC search           : 0.00
% 5.99/2.20  Cooper               : 0.00
% 5.99/2.20  Total                : 1.46
% 5.99/2.20  Index Insertion      : 0.00
% 5.99/2.20  Index Deletion       : 0.00
% 5.99/2.20  Index Matching       : 0.00
% 5.99/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
