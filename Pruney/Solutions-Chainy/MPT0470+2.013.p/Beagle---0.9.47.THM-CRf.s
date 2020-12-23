%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:02 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 235 expanded)
%              Number of leaves         :   45 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  177 ( 358 expanded)
%              Number of equality atoms :   64 ( 143 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_112,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_60,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_95,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_62,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_90,plain,(
    ! [A_63] :
      ( v1_relat_1(A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_94,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(k5_relat_1(A_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_121,plain,(
    ! [A_67,B_68] :
      ( v1_xboole_0(k2_zfmisc_1(A_67,B_68))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_169,plain,(
    ! [A_76,B_77] :
      ( k2_zfmisc_1(A_76,B_77) = k1_xboole_0
      | ~ v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_121,c_6])).

tff(c_175,plain,(
    ! [B_77] : k2_zfmisc_1(k1_xboole_0,B_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_169])).

tff(c_58,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_358,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_102,B_103)),k1_relat_1(A_102))
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_363,plain,(
    ! [B_103] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_103)),k1_xboole_0)
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_358])).

tff(c_446,plain,(
    ! [B_112] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_112)),k1_xboole_0)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_363])).

tff(c_18,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_202,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_211,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_202])).

tff(c_456,plain,(
    ! [B_113] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_113)) = k1_xboole_0
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_446,c_211])).

tff(c_48,plain,(
    ! [A_49] :
      ( k3_xboole_0(A_49,k2_zfmisc_1(k1_relat_1(A_49),k2_relat_1(A_49))) = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_474,plain,(
    ! [B_113] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_113),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_113)))) = k5_relat_1(k1_xboole_0,B_113)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_113))
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_48])).

tff(c_550,plain,(
    ! [B_118] :
      ( k5_relat_1(k1_xboole_0,B_118) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_118))
      | ~ v1_relat_1(B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_175,c_474])).

tff(c_554,plain,(
    ! [B_47] :
      ( k5_relat_1(k1_xboole_0,B_47) = k1_xboole_0
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_550])).

tff(c_558,plain,(
    ! [B_119] :
      ( k5_relat_1(k1_xboole_0,B_119) = k1_xboole_0
      | ~ v1_relat_1(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_554])).

tff(c_573,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_558])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_573])).

tff(c_582,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_20,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_700,plain,(
    ! [A_139,B_140] : k5_xboole_0(A_139,k3_xboole_0(A_139,B_140)) = k4_xboole_0(A_139,B_140) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_712,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_700])).

tff(c_715,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_712])).

tff(c_36,plain,(
    ! [A_40,B_41] : k6_subset_1(A_40,B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [A_50,B_52] :
      ( k6_subset_1(k4_relat_1(A_50),k4_relat_1(B_52)) = k4_relat_1(k6_subset_1(A_50,B_52))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1124,plain,(
    ! [A_171,B_172] :
      ( k4_xboole_0(k4_relat_1(A_171),k4_relat_1(B_172)) = k4_relat_1(k4_xboole_0(A_171,B_172))
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_50])).

tff(c_1131,plain,(
    ! [B_172] :
      ( k4_relat_1(k4_xboole_0(B_172,B_172)) = k1_xboole_0
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1124,c_715])).

tff(c_1146,plain,(
    ! [B_172] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_1131])).

tff(c_1150,plain,(
    ! [B_173] :
      ( ~ v1_relat_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(splitLeft,[status(thm)],[c_1146])).

tff(c_1158,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_94,c_1150])).

tff(c_1167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1158])).

tff(c_1168,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1146])).

tff(c_54,plain,(
    ! [B_58,A_56] :
      ( k5_relat_1(k4_relat_1(B_58),k4_relat_1(A_56)) = k4_relat_1(k5_relat_1(A_56,B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1181,plain,(
    ! [A_56] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_56)) = k4_relat_1(k5_relat_1(A_56,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_54])).

tff(c_1218,plain,(
    ! [A_179] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_179)) = k4_relat_1(k5_relat_1(A_179,k1_xboole_0))
      | ~ v1_relat_1(A_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1181])).

tff(c_42,plain,(
    ! [A_45] :
      ( v1_relat_1(k4_relat_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_613,plain,(
    ! [A_123,B_124] :
      ( v1_xboole_0(k2_zfmisc_1(A_123,B_124))
      | ~ v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_661,plain,(
    ! [A_132,B_133] :
      ( k2_zfmisc_1(A_132,B_133) = k1_xboole_0
      | ~ v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_613,c_6])).

tff(c_667,plain,(
    ! [B_133] : k2_zfmisc_1(k1_xboole_0,B_133) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_661])).

tff(c_846,plain,(
    ! [A_154,B_155] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_154,B_155)),k1_relat_1(A_154))
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_854,plain,(
    ! [B_155] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_155)),k1_xboole_0)
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_846])).

tff(c_860,plain,(
    ! [B_156] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_156)),k1_xboole_0)
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_854])).

tff(c_716,plain,(
    ! [B_141,A_142] :
      ( B_141 = A_142
      | ~ r1_tarski(B_141,A_142)
      | ~ r1_tarski(A_142,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_725,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_716])).

tff(c_884,plain,(
    ! [B_161] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_161)) = k1_xboole_0
      | ~ v1_relat_1(B_161) ) ),
    inference(resolution,[status(thm)],[c_860,c_725])).

tff(c_902,plain,(
    ! [B_161] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_161),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_161)))) = k5_relat_1(k1_xboole_0,B_161)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_161))
      | ~ v1_relat_1(B_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_48])).

tff(c_918,plain,(
    ! [B_162] :
      ( k5_relat_1(k1_xboole_0,B_162) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_162))
      | ~ v1_relat_1(B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_667,c_902])).

tff(c_922,plain,(
    ! [B_47] :
      ( k5_relat_1(k1_xboole_0,B_47) = k1_xboole_0
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_918])).

tff(c_952,plain,(
    ! [B_165] :
      ( k5_relat_1(k1_xboole_0,B_165) = k1_xboole_0
      | ~ v1_relat_1(B_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_922])).

tff(c_970,plain,(
    ! [A_45] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_45)) = k1_xboole_0
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_42,c_952])).

tff(c_1262,plain,(
    ! [A_180] :
      ( k4_relat_1(k5_relat_1(A_180,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1218,c_970])).

tff(c_46,plain,(
    ! [A_48] :
      ( k4_relat_1(k4_relat_1(A_48)) = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1286,plain,(
    ! [A_180] :
      ( k5_relat_1(A_180,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_180,k1_xboole_0))
      | ~ v1_relat_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1262,c_46])).

tff(c_1913,plain,(
    ! [A_209] :
      ( k5_relat_1(A_209,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_209,k1_xboole_0))
      | ~ v1_relat_1(A_209)
      | ~ v1_relat_1(A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1168,c_1286])).

tff(c_1923,plain,(
    ! [A_46] :
      ( k5_relat_1(A_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_44,c_1913])).

tff(c_2007,plain,(
    ! [A_212] :
      ( k5_relat_1(A_212,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1923])).

tff(c_2031,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_2007])).

tff(c_2043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_2031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.58  
% 3.52/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.58  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.52/1.58  
% 3.52/1.58  %Foreground sorts:
% 3.52/1.58  
% 3.52/1.58  
% 3.52/1.58  %Background operators:
% 3.52/1.58  
% 3.52/1.58  
% 3.52/1.58  %Foreground operators:
% 3.52/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.52/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.52/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.52/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.58  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.52/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.52/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.58  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.52/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.52/1.58  
% 3.52/1.60  tff(f_119, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.52/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.52/1.60  tff(f_70, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.52/1.60  tff(f_80, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.52/1.60  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.52/1.60  tff(f_62, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.52/1.60  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.52/1.60  tff(f_112, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.52/1.60  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 3.52/1.60  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.52/1.60  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.52/1.60  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.52/1.60  tff(f_46, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.52/1.60  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.52/1.60  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.52/1.60  tff(f_64, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.52/1.60  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 3.52/1.60  tff(f_109, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.52/1.60  tff(f_74, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.52/1.60  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.52/1.60  tff(c_60, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.52/1.60  tff(c_95, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.52/1.60  tff(c_62, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.52/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.52/1.60  tff(c_90, plain, (![A_63]: (v1_relat_1(A_63) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.52/1.60  tff(c_94, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_90])).
% 3.52/1.60  tff(c_44, plain, (![A_46, B_47]: (v1_relat_1(k5_relat_1(A_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.52/1.60  tff(c_16, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.52/1.60  tff(c_121, plain, (![A_67, B_68]: (v1_xboole_0(k2_zfmisc_1(A_67, B_68)) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.60  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.52/1.60  tff(c_169, plain, (![A_76, B_77]: (k2_zfmisc_1(A_76, B_77)=k1_xboole_0 | ~v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_121, c_6])).
% 3.52/1.60  tff(c_175, plain, (![B_77]: (k2_zfmisc_1(k1_xboole_0, B_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_169])).
% 3.52/1.60  tff(c_58, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.60  tff(c_358, plain, (![A_102, B_103]: (r1_tarski(k1_relat_1(k5_relat_1(A_102, B_103)), k1_relat_1(A_102)) | ~v1_relat_1(B_103) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.52/1.60  tff(c_363, plain, (![B_103]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_103)), k1_xboole_0) | ~v1_relat_1(B_103) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_358])).
% 3.52/1.60  tff(c_446, plain, (![B_112]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_112)), k1_xboole_0) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_363])).
% 3.52/1.60  tff(c_18, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.52/1.60  tff(c_202, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.52/1.60  tff(c_211, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_202])).
% 3.52/1.60  tff(c_456, plain, (![B_113]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_113))=k1_xboole_0 | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_446, c_211])).
% 3.52/1.60  tff(c_48, plain, (![A_49]: (k3_xboole_0(A_49, k2_zfmisc_1(k1_relat_1(A_49), k2_relat_1(A_49)))=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.52/1.60  tff(c_474, plain, (![B_113]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_113), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_113))))=k5_relat_1(k1_xboole_0, B_113) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_113)) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_456, c_48])).
% 3.52/1.60  tff(c_550, plain, (![B_118]: (k5_relat_1(k1_xboole_0, B_118)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_118)) | ~v1_relat_1(B_118))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_175, c_474])).
% 3.52/1.60  tff(c_554, plain, (![B_47]: (k5_relat_1(k1_xboole_0, B_47)=k1_xboole_0 | ~v1_relat_1(B_47) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_550])).
% 3.52/1.60  tff(c_558, plain, (![B_119]: (k5_relat_1(k1_xboole_0, B_119)=k1_xboole_0 | ~v1_relat_1(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_554])).
% 3.52/1.60  tff(c_573, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_558])).
% 3.52/1.60  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_573])).
% 3.52/1.60  tff(c_582, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.52/1.60  tff(c_20, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.52/1.60  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.52/1.60  tff(c_700, plain, (![A_139, B_140]: (k5_xboole_0(A_139, k3_xboole_0(A_139, B_140))=k4_xboole_0(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.52/1.60  tff(c_712, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_700])).
% 3.52/1.60  tff(c_715, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_712])).
% 3.52/1.60  tff(c_36, plain, (![A_40, B_41]: (k6_subset_1(A_40, B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.52/1.60  tff(c_50, plain, (![A_50, B_52]: (k6_subset_1(k4_relat_1(A_50), k4_relat_1(B_52))=k4_relat_1(k6_subset_1(A_50, B_52)) | ~v1_relat_1(B_52) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.52/1.60  tff(c_1124, plain, (![A_171, B_172]: (k4_xboole_0(k4_relat_1(A_171), k4_relat_1(B_172))=k4_relat_1(k4_xboole_0(A_171, B_172)) | ~v1_relat_1(B_172) | ~v1_relat_1(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_50])).
% 3.52/1.60  tff(c_1131, plain, (![B_172]: (k4_relat_1(k4_xboole_0(B_172, B_172))=k1_xboole_0 | ~v1_relat_1(B_172) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_1124, c_715])).
% 3.52/1.60  tff(c_1146, plain, (![B_172]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_172) | ~v1_relat_1(B_172))), inference(demodulation, [status(thm), theory('equality')], [c_715, c_1131])).
% 3.52/1.60  tff(c_1150, plain, (![B_173]: (~v1_relat_1(B_173) | ~v1_relat_1(B_173))), inference(splitLeft, [status(thm)], [c_1146])).
% 3.52/1.60  tff(c_1158, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_1150])).
% 3.52/1.60  tff(c_1167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_1158])).
% 3.52/1.60  tff(c_1168, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1146])).
% 3.52/1.60  tff(c_54, plain, (![B_58, A_56]: (k5_relat_1(k4_relat_1(B_58), k4_relat_1(A_56))=k4_relat_1(k5_relat_1(A_56, B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.52/1.60  tff(c_1181, plain, (![A_56]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_56))=k4_relat_1(k5_relat_1(A_56, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_1168, c_54])).
% 3.52/1.60  tff(c_1218, plain, (![A_179]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_179))=k4_relat_1(k5_relat_1(A_179, k1_xboole_0)) | ~v1_relat_1(A_179))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1181])).
% 3.52/1.60  tff(c_42, plain, (![A_45]: (v1_relat_1(k4_relat_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.60  tff(c_613, plain, (![A_123, B_124]: (v1_xboole_0(k2_zfmisc_1(A_123, B_124)) | ~v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.52/1.60  tff(c_661, plain, (![A_132, B_133]: (k2_zfmisc_1(A_132, B_133)=k1_xboole_0 | ~v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_613, c_6])).
% 3.52/1.60  tff(c_667, plain, (![B_133]: (k2_zfmisc_1(k1_xboole_0, B_133)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_661])).
% 3.52/1.60  tff(c_846, plain, (![A_154, B_155]: (r1_tarski(k1_relat_1(k5_relat_1(A_154, B_155)), k1_relat_1(A_154)) | ~v1_relat_1(B_155) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.52/1.60  tff(c_854, plain, (![B_155]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_155)), k1_xboole_0) | ~v1_relat_1(B_155) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_846])).
% 3.52/1.60  tff(c_860, plain, (![B_156]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_156)), k1_xboole_0) | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_854])).
% 3.52/1.60  tff(c_716, plain, (![B_141, A_142]: (B_141=A_142 | ~r1_tarski(B_141, A_142) | ~r1_tarski(A_142, B_141))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.52/1.60  tff(c_725, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_716])).
% 3.52/1.60  tff(c_884, plain, (![B_161]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_161))=k1_xboole_0 | ~v1_relat_1(B_161))), inference(resolution, [status(thm)], [c_860, c_725])).
% 3.52/1.60  tff(c_902, plain, (![B_161]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_161), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_161))))=k5_relat_1(k1_xboole_0, B_161) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_161)) | ~v1_relat_1(B_161))), inference(superposition, [status(thm), theory('equality')], [c_884, c_48])).
% 3.52/1.60  tff(c_918, plain, (![B_162]: (k5_relat_1(k1_xboole_0, B_162)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_162)) | ~v1_relat_1(B_162))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_667, c_902])).
% 3.52/1.60  tff(c_922, plain, (![B_47]: (k5_relat_1(k1_xboole_0, B_47)=k1_xboole_0 | ~v1_relat_1(B_47) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_918])).
% 3.52/1.60  tff(c_952, plain, (![B_165]: (k5_relat_1(k1_xboole_0, B_165)=k1_xboole_0 | ~v1_relat_1(B_165))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_922])).
% 3.52/1.60  tff(c_970, plain, (![A_45]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_45))=k1_xboole_0 | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_42, c_952])).
% 3.52/1.60  tff(c_1262, plain, (![A_180]: (k4_relat_1(k5_relat_1(A_180, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_180) | ~v1_relat_1(A_180))), inference(superposition, [status(thm), theory('equality')], [c_1218, c_970])).
% 3.52/1.60  tff(c_46, plain, (![A_48]: (k4_relat_1(k4_relat_1(A_48))=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.52/1.60  tff(c_1286, plain, (![A_180]: (k5_relat_1(A_180, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_180, k1_xboole_0)) | ~v1_relat_1(A_180) | ~v1_relat_1(A_180))), inference(superposition, [status(thm), theory('equality')], [c_1262, c_46])).
% 3.52/1.60  tff(c_1913, plain, (![A_209]: (k5_relat_1(A_209, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_209, k1_xboole_0)) | ~v1_relat_1(A_209) | ~v1_relat_1(A_209))), inference(demodulation, [status(thm), theory('equality')], [c_1168, c_1286])).
% 3.52/1.60  tff(c_1923, plain, (![A_46]: (k5_relat_1(A_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_44, c_1913])).
% 3.52/1.60  tff(c_2007, plain, (![A_212]: (k5_relat_1(A_212, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1923])).
% 3.52/1.60  tff(c_2031, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_2007])).
% 3.52/1.60  tff(c_2043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_582, c_2031])).
% 3.52/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.60  
% 3.52/1.60  Inference rules
% 3.52/1.60  ----------------------
% 3.52/1.60  #Ref     : 0
% 3.52/1.60  #Sup     : 464
% 3.52/1.60  #Fact    : 0
% 3.52/1.60  #Define  : 0
% 3.52/1.60  #Split   : 3
% 3.52/1.60  #Chain   : 0
% 3.52/1.60  #Close   : 0
% 3.52/1.60  
% 3.52/1.60  Ordering : KBO
% 3.52/1.60  
% 3.52/1.60  Simplification rules
% 3.52/1.60  ----------------------
% 3.52/1.60  #Subsume      : 18
% 3.52/1.60  #Demod        : 438
% 3.52/1.60  #Tautology    : 286
% 3.52/1.60  #SimpNegUnit  : 2
% 3.52/1.60  #BackRed      : 0
% 3.52/1.60  
% 3.52/1.60  #Partial instantiations: 0
% 3.52/1.60  #Strategies tried      : 1
% 3.52/1.60  
% 3.52/1.60  Timing (in seconds)
% 3.52/1.60  ----------------------
% 3.52/1.60  Preprocessing        : 0.33
% 3.52/1.60  Parsing              : 0.18
% 3.52/1.60  CNF conversion       : 0.02
% 3.52/1.60  Main loop            : 0.48
% 3.52/1.60  Inferencing          : 0.18
% 3.52/1.60  Reduction            : 0.16
% 3.52/1.60  Demodulation         : 0.11
% 3.52/1.60  BG Simplification    : 0.03
% 3.52/1.60  Subsumption          : 0.09
% 3.52/1.60  Abstraction          : 0.03
% 3.52/1.60  MUC search           : 0.00
% 3.52/1.60  Cooper               : 0.00
% 3.52/1.60  Total                : 0.86
% 3.52/1.60  Index Insertion      : 0.00
% 3.52/1.60  Index Deletion       : 0.00
% 3.52/1.60  Index Matching       : 0.00
% 3.52/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
