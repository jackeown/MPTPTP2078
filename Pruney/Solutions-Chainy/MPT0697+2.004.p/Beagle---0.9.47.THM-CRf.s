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
% DateTime   : Thu Dec  3 10:04:58 EST 2020

% Result     : Theorem 48.41s
% Output     : CNFRefutation 48.41s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 876 expanded)
%              Number of leaves         :   37 ( 318 expanded)
%              Depth                    :   21
%              Number of atoms          :  240 (1679 expanded)
%              Number of equality atoms :   91 ( 578 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_206,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(A_61,B_62) = B_62
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_222,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(resolution,[status(thm)],[c_22,c_206])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_549,plain,(
    ! [A_93,B_94] :
      ( k2_xboole_0(A_93,B_94) = B_94
      | k4_xboole_0(A_93,B_94) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_206])).

tff(c_573,plain,(
    ! [A_95] :
      ( k2_xboole_0(A_95,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_549])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_277,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(A_69,C_70)
      | ~ r1_tarski(k2_xboole_0(A_69,B_71),C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_298,plain,(
    ! [A_72,B_73] : r1_tarski(A_72,k2_xboole_0(A_72,B_73)) ),
    inference(resolution,[status(thm)],[c_12,c_277])).

tff(c_18,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(k2_xboole_0(A_10,B_11),C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_318,plain,(
    ! [A_10,B_11,B_73] : r1_tarski(A_10,k2_xboole_0(k2_xboole_0(A_10,B_11),B_73)) ),
    inference(resolution,[status(thm)],[c_298,c_18])).

tff(c_582,plain,(
    ! [A_95,B_73] :
      ( r1_tarski(A_95,k2_xboole_0(k1_xboole_0,B_73))
      | k1_xboole_0 != A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_318])).

tff(c_624,plain,(
    ! [A_95,B_73] :
      ( r1_tarski(A_95,B_73)
      | k1_xboole_0 != A_95 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_582])).

tff(c_93,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_28,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    ! [C_41,A_39,B_40] :
      ( k6_subset_1(k10_relat_1(C_41,A_39),k10_relat_1(C_41,B_40)) = k10_relat_1(C_41,k6_subset_1(A_39,B_40))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1743,plain,(
    ! [C_152,A_153,B_154] :
      ( k4_xboole_0(k10_relat_1(C_152,A_153),k10_relat_1(C_152,B_154)) = k10_relat_1(C_152,k4_xboole_0(A_153,B_154))
      | ~ v1_funct_1(C_152)
      | ~ v1_relat_1(C_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_52])).

tff(c_1786,plain,(
    ! [C_152,B_154] :
      ( k10_relat_1(C_152,k4_xboole_0(B_154,B_154)) = k1_xboole_0
      | ~ v1_funct_1(C_152)
      | ~ v1_relat_1(C_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1743,c_104])).

tff(c_1807,plain,(
    ! [C_155] :
      ( k10_relat_1(C_155,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1786])).

tff(c_1810,plain,
    ( k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1807])).

tff(c_1813,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1810])).

tff(c_30,plain,(
    ! [C_23,A_21,B_22] :
      ( r1_tarski(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22))
      | ~ r1_tarski(A_21,B_22)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1829,plain,(
    ! [A_21] :
      ( r1_tarski(k10_relat_1('#skF_5',A_21),k1_xboole_0)
      | ~ r1_tarski(A_21,k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1813,c_30])).

tff(c_1907,plain,(
    ! [A_160] :
      ( r1_tarski(k10_relat_1('#skF_5',A_160),k1_xboole_0)
      | ~ r1_tarski(A_160,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1829])).

tff(c_645,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(A_96,B_97)
      | k1_xboole_0 != A_96 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_582])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_666,plain,(
    ! [B_97,A_96] :
      ( B_97 = A_96
      | ~ r1_tarski(B_97,A_96)
      | k1_xboole_0 != A_96 ) ),
    inference(resolution,[status(thm)],[c_645,c_8])).

tff(c_1938,plain,(
    ! [A_161] :
      ( k10_relat_1('#skF_5',A_161) = k1_xboole_0
      | ~ r1_tarski(A_161,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1907,c_666])).

tff(c_1989,plain,(
    ! [A_162] :
      ( k10_relat_1('#skF_5',A_162) = k1_xboole_0
      | k1_xboole_0 != A_162 ) ),
    inference(resolution,[status(thm)],[c_624,c_1938])).

tff(c_65,plain,(
    ! [C_41,A_39,B_40] :
      ( k4_xboole_0(k10_relat_1(C_41,A_39),k10_relat_1(C_41,B_40)) = k10_relat_1(C_41,k4_xboole_0(A_39,B_40))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_52])).

tff(c_2001,plain,(
    ! [A_39,A_162] :
      ( k4_xboole_0(k10_relat_1('#skF_5',A_39),k1_xboole_0) = k10_relat_1('#skF_5',k4_xboole_0(A_39,A_162))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | k1_xboole_0 != A_162 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1989,c_65])).

tff(c_31855,plain,(
    ! [A_640,A_641] :
      ( k10_relat_1('#skF_5',k4_xboole_0(A_640,A_641)) = k10_relat_1('#skF_5',A_640)
      | k1_xboole_0 != A_641 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_26,c_2001])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1179,plain,(
    ! [D_130,A_131,B_132] :
      ( r2_hidden(D_130,k1_relat_1(A_131))
      | ~ r2_hidden(D_130,k10_relat_1(A_131,B_132))
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_17895,plain,(
    ! [A_482,B_483,B_484] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_482,B_483),B_484),k1_relat_1(A_482))
      | ~ v1_funct_1(A_482)
      | ~ v1_relat_1(A_482)
      | r1_tarski(k10_relat_1(A_482,B_483),B_484) ) ),
    inference(resolution,[status(thm)],[c_6,c_1179])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17927,plain,(
    ! [A_482,B_483] :
      ( ~ v1_funct_1(A_482)
      | ~ v1_relat_1(A_482)
      | r1_tarski(k10_relat_1(A_482,B_483),k1_relat_1(A_482)) ) ),
    inference(resolution,[status(thm)],[c_17895,c_4])).

tff(c_31905,plain,(
    ! [A_640,A_641] :
      ( ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | r1_tarski(k10_relat_1('#skF_5',A_640),k1_relat_1('#skF_5'))
      | k1_xboole_0 != A_641 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31855,c_17927])).

tff(c_32156,plain,(
    ! [A_640,A_641] :
      ( r1_tarski(k10_relat_1('#skF_5',A_640),k1_relat_1('#skF_5'))
      | k1_xboole_0 != A_641 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_31905])).

tff(c_32218,plain,(
    ! [A_641] : k1_xboole_0 != A_641 ),
    inference(splitLeft,[status(thm)],[c_32156])).

tff(c_24,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_220,plain,(
    ! [A_16,B_17] : k2_xboole_0(k4_xboole_0(A_16,B_17),A_16) = A_16 ),
    inference(resolution,[status(thm)],[c_24,c_206])).

tff(c_363,plain,(
    ! [A_76,B_77,B_78] : r1_tarski(A_76,k2_xboole_0(k2_xboole_0(A_76,B_77),B_78)) ),
    inference(resolution,[status(thm)],[c_298,c_18])).

tff(c_393,plain,(
    ! [A_79,B_80,B_81] : r1_tarski(k4_xboole_0(A_79,B_80),k2_xboole_0(A_79,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_363])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12960,plain,(
    ! [A_410,B_411,B_412] : k2_xboole_0(k4_xboole_0(A_410,B_411),k2_xboole_0(A_410,B_412)) = k2_xboole_0(A_410,B_412) ),
    inference(resolution,[status(thm)],[c_393,c_20])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_425,plain,(
    ! [A_79,B_80,B_81] : k4_xboole_0(k4_xboole_0(A_79,B_80),k2_xboole_0(A_79,B_81)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_393,c_16])).

tff(c_14739,plain,(
    ! [A_444,B_445,B_446,B_447] : k4_xboole_0(k4_xboole_0(k4_xboole_0(A_444,B_445),B_446),k2_xboole_0(A_444,B_447)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12960,c_425])).

tff(c_15143,plain,(
    ! [A_16,B_17,B_445,B_446] : k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_16,B_17),B_445),B_446),A_16) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_14739])).

tff(c_32598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32218,c_15143])).

tff(c_32600,plain,(
    ! [A_643] : r1_tarski(k10_relat_1('#skF_5',A_643),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_32156])).

tff(c_33278,plain,(
    ! [A_645] : k2_xboole_0(k10_relat_1('#skF_5',A_645),k1_relat_1('#skF_5')) = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32600,c_20])).

tff(c_376,plain,(
    ! [A_16,B_17,B_78] : r1_tarski(k4_xboole_0(A_16,B_17),k2_xboole_0(A_16,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_363])).

tff(c_33392,plain,(
    ! [A_645,B_17] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_5',A_645),B_17),k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33278,c_376])).

tff(c_1978,plain,(
    ! [A_95] :
      ( k10_relat_1('#skF_5',A_95) = k1_xboole_0
      | k1_xboole_0 != A_95 ) ),
    inference(resolution,[status(thm)],[c_624,c_1938])).

tff(c_6958,plain,(
    ! [C_312,A_313,B_314] :
      ( r1_tarski(k10_relat_1(C_312,k4_xboole_0(A_313,B_314)),k10_relat_1(C_312,A_313))
      | ~ v1_funct_1(C_312)
      | ~ v1_relat_1(C_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1743,c_24])).

tff(c_7017,plain,(
    ! [A_95,B_314] :
      ( r1_tarski(k10_relat_1('#skF_5',k4_xboole_0(A_95,B_314)),k1_xboole_0)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | k1_xboole_0 != A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1978,c_6958])).

tff(c_7075,plain,(
    ! [A_315,B_316] :
      ( r1_tarski(k10_relat_1('#skF_5',k4_xboole_0(A_315,B_316)),k1_xboole_0)
      | k1_xboole_0 != A_315 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_7017])).

tff(c_7201,plain,(
    ! [A_317] :
      ( r1_tarski(k10_relat_1('#skF_5',A_317),k1_xboole_0)
      | k1_xboole_0 != A_317 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7075])).

tff(c_1136,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_tarski(k4_xboole_0(A_127,B_128),C_129)
      | ~ r1_tarski(A_127,C_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_277])).

tff(c_486,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_513,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_486])).

tff(c_1171,plain,(
    ! [A_127,B_128] :
      ( k4_xboole_0(A_127,B_128) = k1_xboole_0
      | ~ r1_tarski(A_127,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1136,c_513])).

tff(c_7254,plain,(
    ! [A_317,B_128] :
      ( k4_xboole_0(k10_relat_1('#skF_5',A_317),B_128) = k1_xboole_0
      | k1_xboole_0 != A_317 ) ),
    inference(resolution,[status(thm)],[c_7201,c_1171])).

tff(c_3539,plain,(
    ! [A_209,B_210,B_211] :
      ( r1_tarski(A_209,B_210)
      | k4_xboole_0(k2_xboole_0(A_209,B_211),B_210) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_277])).

tff(c_3640,plain,(
    ! [A_214,B_215,B_216] :
      ( r1_tarski(k4_xboole_0(A_214,B_215),B_216)
      | k4_xboole_0(A_214,B_216) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_3539])).

tff(c_14343,plain,(
    ! [A_428,B_429,B_430] :
      ( k4_xboole_0(A_428,B_429) = B_430
      | k1_xboole_0 != B_430
      | k4_xboole_0(A_428,B_430) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3640,c_666])).

tff(c_56893,plain,(
    ! [B_429] : k4_xboole_0(k10_relat_1('#skF_5',k1_xboole_0),B_429) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7254,c_14343])).

tff(c_7587,plain,(
    ! [A_322,B_323] :
      ( k4_xboole_0(k10_relat_1('#skF_5',A_322),B_323) = k1_xboole_0
      | k1_xboole_0 != A_322 ) ),
    inference(resolution,[status(thm)],[c_7201,c_1171])).

tff(c_867,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ r1_tarski(B_111,A_112)
      | k1_xboole_0 != A_112 ) ),
    inference(resolution,[status(thm)],[c_645,c_8])).

tff(c_905,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | k1_xboole_0 != B_9
      | k4_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_867])).

tff(c_8192,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7587,c_905])).

tff(c_60,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    ! [C_38,A_36,B_37] :
      ( k6_subset_1(k9_relat_1(C_38,A_36),k9_relat_1(C_38,B_37)) = k9_relat_1(C_38,k6_subset_1(A_36,B_37))
      | ~ v2_funct_1(C_38)
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_66,plain,(
    ! [C_38,A_36,B_37] :
      ( k4_xboole_0(k9_relat_1(C_38,A_36),k9_relat_1(C_38,B_37)) = k9_relat_1(C_38,k4_xboole_0(A_36,B_37))
      | ~ v2_funct_1(C_38)
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_50])).

tff(c_54,plain,(
    ! [B_43,A_42] :
      ( r1_tarski(k9_relat_1(B_43,k10_relat_1(B_43,A_42)),A_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32012,plain,(
    ! [A_640,A_641] :
      ( r1_tarski(k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_640)),k4_xboole_0(A_640,A_641))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | k1_xboole_0 != A_641 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31855,c_54])).

tff(c_180609,plain,(
    ! [A_1688,A_1689] :
      ( r1_tarski(k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_1688)),k4_xboole_0(A_1688,A_1689))
      | k1_xboole_0 != A_1689 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_32012])).

tff(c_181214,plain,(
    ! [A_1690] : r1_tarski(k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_1690)),A_1690) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_180609])).

tff(c_182713,plain,(
    ! [A_1692] : k4_xboole_0(k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_1692)),A_1692) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_181214,c_16])).

tff(c_183510,plain,(
    ! [B_37] :
      ( k9_relat_1('#skF_5',k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5',B_37)),B_37)) = k1_xboole_0
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_182713])).

tff(c_183735,plain,(
    ! [B_37] : k9_relat_1('#skF_5',k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5',B_37)),B_37)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_183510])).

tff(c_193731,plain,(
    ! [B_1725] : k9_relat_1('#skF_5',k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5',B_1725)),B_1725)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_183510])).

tff(c_56,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,k10_relat_1(B_45,k9_relat_1(B_45,A_44)))
      | ~ r1_tarski(A_44,k1_relat_1(B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3479,plain,(
    ! [B_207,A_208] :
      ( B_207 = A_208
      | ~ r1_tarski(B_207,A_208)
      | k4_xboole_0(A_208,B_207) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_486])).

tff(c_3525,plain,(
    ! [B_45,A_44] :
      ( k10_relat_1(B_45,k9_relat_1(B_45,A_44)) = A_44
      | k4_xboole_0(k10_relat_1(B_45,k9_relat_1(B_45,A_44)),A_44) != k1_xboole_0
      | ~ r1_tarski(A_44,k1_relat_1(B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_56,c_3479])).

tff(c_193799,plain,(
    ! [B_1725] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5',B_1725)),B_1725))) = k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5',B_1725)),B_1725)
      | k4_xboole_0(k10_relat_1('#skF_5',k1_xboole_0),k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5',B_1725)),B_1725)) != k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5',B_1725)),B_1725),k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193731,c_3525])).

tff(c_194100,plain,(
    ! [B_1725] : k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5',B_1725)),B_1725) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_33392,c_56893,c_8192,c_183735,c_193799])).

tff(c_197,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | k4_xboole_0(A_59,B_60) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    ~ r1_tarski(k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_4')),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_204,plain,(
    k4_xboole_0(k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_4')),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_197,c_58])).

tff(c_194608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194100,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.41/38.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.41/38.74  
% 48.41/38.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.41/38.75  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 48.41/38.75  
% 48.41/38.75  %Foreground sorts:
% 48.41/38.75  
% 48.41/38.75  
% 48.41/38.75  %Background operators:
% 48.41/38.75  
% 48.41/38.75  
% 48.41/38.75  %Foreground operators:
% 48.41/38.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 48.41/38.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 48.41/38.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.41/38.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.41/38.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 48.41/38.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.41/38.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.41/38.75  tff('#skF_5', type, '#skF_5': $i).
% 48.41/38.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 48.41/38.75  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 48.41/38.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 48.41/38.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 48.41/38.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.41/38.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 48.41/38.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.41/38.75  tff('#skF_4', type, '#skF_4': $i).
% 48.41/38.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 48.41/38.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.41/38.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 48.41/38.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 48.41/38.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.41/38.75  
% 48.41/38.77  tff(f_113, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 48.41/38.77  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 48.41/38.77  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 48.41/38.77  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 48.41/38.77  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 48.41/38.77  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 48.41/38.77  tff(f_46, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 48.41/38.77  tff(f_58, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 48.41/38.77  tff(f_92, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 48.41/38.77  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 48.41/38.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 48.41/38.77  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 48.41/38.77  tff(f_54, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 48.41/38.77  tff(f_86, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 48.41/38.77  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 48.41/38.77  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 48.41/38.77  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 48.41/38.77  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 48.41/38.77  tff(c_26, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 48.41/38.77  tff(c_22, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 48.41/38.77  tff(c_206, plain, (![A_61, B_62]: (k2_xboole_0(A_61, B_62)=B_62 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 48.41/38.77  tff(c_222, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(resolution, [status(thm)], [c_22, c_206])).
% 48.41/38.77  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | k4_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 48.41/38.77  tff(c_549, plain, (![A_93, B_94]: (k2_xboole_0(A_93, B_94)=B_94 | k4_xboole_0(A_93, B_94)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_206])).
% 48.41/38.77  tff(c_573, plain, (![A_95]: (k2_xboole_0(A_95, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_95)), inference(superposition, [status(thm), theory('equality')], [c_26, c_549])).
% 48.41/38.77  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 48.41/38.77  tff(c_277, plain, (![A_69, C_70, B_71]: (r1_tarski(A_69, C_70) | ~r1_tarski(k2_xboole_0(A_69, B_71), C_70))), inference(cnfTransformation, [status(thm)], [f_46])).
% 48.41/38.77  tff(c_298, plain, (![A_72, B_73]: (r1_tarski(A_72, k2_xboole_0(A_72, B_73)))), inference(resolution, [status(thm)], [c_12, c_277])).
% 48.41/38.77  tff(c_18, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(k2_xboole_0(A_10, B_11), C_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 48.41/38.77  tff(c_318, plain, (![A_10, B_11, B_73]: (r1_tarski(A_10, k2_xboole_0(k2_xboole_0(A_10, B_11), B_73)))), inference(resolution, [status(thm)], [c_298, c_18])).
% 48.41/38.77  tff(c_582, plain, (![A_95, B_73]: (r1_tarski(A_95, k2_xboole_0(k1_xboole_0, B_73)) | k1_xboole_0!=A_95)), inference(superposition, [status(thm), theory('equality')], [c_573, c_318])).
% 48.41/38.77  tff(c_624, plain, (![A_95, B_73]: (r1_tarski(A_95, B_73) | k1_xboole_0!=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_582])).
% 48.41/38.77  tff(c_93, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_42])).
% 48.41/38.77  tff(c_104, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_93])).
% 48.41/38.77  tff(c_28, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 48.41/38.77  tff(c_52, plain, (![C_41, A_39, B_40]: (k6_subset_1(k10_relat_1(C_41, A_39), k10_relat_1(C_41, B_40))=k10_relat_1(C_41, k6_subset_1(A_39, B_40)) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_92])).
% 48.41/38.77  tff(c_1743, plain, (![C_152, A_153, B_154]: (k4_xboole_0(k10_relat_1(C_152, A_153), k10_relat_1(C_152, B_154))=k10_relat_1(C_152, k4_xboole_0(A_153, B_154)) | ~v1_funct_1(C_152) | ~v1_relat_1(C_152))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_52])).
% 48.41/38.77  tff(c_1786, plain, (![C_152, B_154]: (k10_relat_1(C_152, k4_xboole_0(B_154, B_154))=k1_xboole_0 | ~v1_funct_1(C_152) | ~v1_relat_1(C_152))), inference(superposition, [status(thm), theory('equality')], [c_1743, c_104])).
% 48.41/38.77  tff(c_1807, plain, (![C_155]: (k10_relat_1(C_155, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_155) | ~v1_relat_1(C_155))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1786])).
% 48.41/38.77  tff(c_1810, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_1807])).
% 48.41/38.77  tff(c_1813, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1810])).
% 48.41/38.77  tff(c_30, plain, (![C_23, A_21, B_22]: (r1_tarski(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22)) | ~r1_tarski(A_21, B_22) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 48.41/38.77  tff(c_1829, plain, (![A_21]: (r1_tarski(k10_relat_1('#skF_5', A_21), k1_xboole_0) | ~r1_tarski(A_21, k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1813, c_30])).
% 48.41/38.77  tff(c_1907, plain, (![A_160]: (r1_tarski(k10_relat_1('#skF_5', A_160), k1_xboole_0) | ~r1_tarski(A_160, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1829])).
% 48.41/38.77  tff(c_645, plain, (![A_96, B_97]: (r1_tarski(A_96, B_97) | k1_xboole_0!=A_96)), inference(demodulation, [status(thm), theory('equality')], [c_222, c_582])).
% 48.41/38.77  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 48.41/38.77  tff(c_666, plain, (![B_97, A_96]: (B_97=A_96 | ~r1_tarski(B_97, A_96) | k1_xboole_0!=A_96)), inference(resolution, [status(thm)], [c_645, c_8])).
% 48.41/38.77  tff(c_1938, plain, (![A_161]: (k10_relat_1('#skF_5', A_161)=k1_xboole_0 | ~r1_tarski(A_161, k1_xboole_0))), inference(resolution, [status(thm)], [c_1907, c_666])).
% 48.41/38.77  tff(c_1989, plain, (![A_162]: (k10_relat_1('#skF_5', A_162)=k1_xboole_0 | k1_xboole_0!=A_162)), inference(resolution, [status(thm)], [c_624, c_1938])).
% 48.41/38.77  tff(c_65, plain, (![C_41, A_39, B_40]: (k4_xboole_0(k10_relat_1(C_41, A_39), k10_relat_1(C_41, B_40))=k10_relat_1(C_41, k4_xboole_0(A_39, B_40)) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_52])).
% 48.41/38.77  tff(c_2001, plain, (![A_39, A_162]: (k4_xboole_0(k10_relat_1('#skF_5', A_39), k1_xboole_0)=k10_relat_1('#skF_5', k4_xboole_0(A_39, A_162)) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | k1_xboole_0!=A_162)), inference(superposition, [status(thm), theory('equality')], [c_1989, c_65])).
% 48.41/38.77  tff(c_31855, plain, (![A_640, A_641]: (k10_relat_1('#skF_5', k4_xboole_0(A_640, A_641))=k10_relat_1('#skF_5', A_640) | k1_xboole_0!=A_641)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_26, c_2001])).
% 48.41/38.77  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.41/38.77  tff(c_1179, plain, (![D_130, A_131, B_132]: (r2_hidden(D_130, k1_relat_1(A_131)) | ~r2_hidden(D_130, k10_relat_1(A_131, B_132)) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.41/38.77  tff(c_17895, plain, (![A_482, B_483, B_484]: (r2_hidden('#skF_1'(k10_relat_1(A_482, B_483), B_484), k1_relat_1(A_482)) | ~v1_funct_1(A_482) | ~v1_relat_1(A_482) | r1_tarski(k10_relat_1(A_482, B_483), B_484))), inference(resolution, [status(thm)], [c_6, c_1179])).
% 48.41/38.77  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 48.41/38.77  tff(c_17927, plain, (![A_482, B_483]: (~v1_funct_1(A_482) | ~v1_relat_1(A_482) | r1_tarski(k10_relat_1(A_482, B_483), k1_relat_1(A_482)))), inference(resolution, [status(thm)], [c_17895, c_4])).
% 48.41/38.77  tff(c_31905, plain, (![A_640, A_641]: (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | r1_tarski(k10_relat_1('#skF_5', A_640), k1_relat_1('#skF_5')) | k1_xboole_0!=A_641)), inference(superposition, [status(thm), theory('equality')], [c_31855, c_17927])).
% 48.41/38.77  tff(c_32156, plain, (![A_640, A_641]: (r1_tarski(k10_relat_1('#skF_5', A_640), k1_relat_1('#skF_5')) | k1_xboole_0!=A_641)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_31905])).
% 48.41/38.77  tff(c_32218, plain, (![A_641]: (k1_xboole_0!=A_641)), inference(splitLeft, [status(thm)], [c_32156])).
% 48.41/38.77  tff(c_24, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 48.41/38.77  tff(c_220, plain, (![A_16, B_17]: (k2_xboole_0(k4_xboole_0(A_16, B_17), A_16)=A_16)), inference(resolution, [status(thm)], [c_24, c_206])).
% 48.41/38.77  tff(c_363, plain, (![A_76, B_77, B_78]: (r1_tarski(A_76, k2_xboole_0(k2_xboole_0(A_76, B_77), B_78)))), inference(resolution, [status(thm)], [c_298, c_18])).
% 48.41/38.77  tff(c_393, plain, (![A_79, B_80, B_81]: (r1_tarski(k4_xboole_0(A_79, B_80), k2_xboole_0(A_79, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_220, c_363])).
% 48.41/38.77  tff(c_20, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 48.41/38.77  tff(c_12960, plain, (![A_410, B_411, B_412]: (k2_xboole_0(k4_xboole_0(A_410, B_411), k2_xboole_0(A_410, B_412))=k2_xboole_0(A_410, B_412))), inference(resolution, [status(thm)], [c_393, c_20])).
% 48.41/38.77  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 48.41/38.77  tff(c_425, plain, (![A_79, B_80, B_81]: (k4_xboole_0(k4_xboole_0(A_79, B_80), k2_xboole_0(A_79, B_81))=k1_xboole_0)), inference(resolution, [status(thm)], [c_393, c_16])).
% 48.41/38.77  tff(c_14739, plain, (![A_444, B_445, B_446, B_447]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(A_444, B_445), B_446), k2_xboole_0(A_444, B_447))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12960, c_425])).
% 48.41/38.77  tff(c_15143, plain, (![A_16, B_17, B_445, B_446]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(A_16, B_17), B_445), B_446), A_16)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_220, c_14739])).
% 48.41/38.77  tff(c_32598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32218, c_15143])).
% 48.41/38.77  tff(c_32600, plain, (![A_643]: (r1_tarski(k10_relat_1('#skF_5', A_643), k1_relat_1('#skF_5')))), inference(splitRight, [status(thm)], [c_32156])).
% 48.41/38.77  tff(c_33278, plain, (![A_645]: (k2_xboole_0(k10_relat_1('#skF_5', A_645), k1_relat_1('#skF_5'))=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32600, c_20])).
% 48.41/38.77  tff(c_376, plain, (![A_16, B_17, B_78]: (r1_tarski(k4_xboole_0(A_16, B_17), k2_xboole_0(A_16, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_220, c_363])).
% 48.41/38.77  tff(c_33392, plain, (![A_645, B_17]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_5', A_645), B_17), k1_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_33278, c_376])).
% 48.41/38.77  tff(c_1978, plain, (![A_95]: (k10_relat_1('#skF_5', A_95)=k1_xboole_0 | k1_xboole_0!=A_95)), inference(resolution, [status(thm)], [c_624, c_1938])).
% 48.41/38.77  tff(c_6958, plain, (![C_312, A_313, B_314]: (r1_tarski(k10_relat_1(C_312, k4_xboole_0(A_313, B_314)), k10_relat_1(C_312, A_313)) | ~v1_funct_1(C_312) | ~v1_relat_1(C_312))), inference(superposition, [status(thm), theory('equality')], [c_1743, c_24])).
% 48.41/38.77  tff(c_7017, plain, (![A_95, B_314]: (r1_tarski(k10_relat_1('#skF_5', k4_xboole_0(A_95, B_314)), k1_xboole_0) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | k1_xboole_0!=A_95)), inference(superposition, [status(thm), theory('equality')], [c_1978, c_6958])).
% 48.41/38.77  tff(c_7075, plain, (![A_315, B_316]: (r1_tarski(k10_relat_1('#skF_5', k4_xboole_0(A_315, B_316)), k1_xboole_0) | k1_xboole_0!=A_315)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_7017])).
% 48.41/38.77  tff(c_7201, plain, (![A_317]: (r1_tarski(k10_relat_1('#skF_5', A_317), k1_xboole_0) | k1_xboole_0!=A_317)), inference(superposition, [status(thm), theory('equality')], [c_26, c_7075])).
% 48.41/38.77  tff(c_1136, plain, (![A_127, B_128, C_129]: (r1_tarski(k4_xboole_0(A_127, B_128), C_129) | ~r1_tarski(A_127, C_129))), inference(superposition, [status(thm), theory('equality')], [c_220, c_277])).
% 48.41/38.77  tff(c_486, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_38])).
% 48.41/38.77  tff(c_513, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_486])).
% 48.41/38.77  tff(c_1171, plain, (![A_127, B_128]: (k4_xboole_0(A_127, B_128)=k1_xboole_0 | ~r1_tarski(A_127, k1_xboole_0))), inference(resolution, [status(thm)], [c_1136, c_513])).
% 48.41/38.77  tff(c_7254, plain, (![A_317, B_128]: (k4_xboole_0(k10_relat_1('#skF_5', A_317), B_128)=k1_xboole_0 | k1_xboole_0!=A_317)), inference(resolution, [status(thm)], [c_7201, c_1171])).
% 48.41/38.77  tff(c_3539, plain, (![A_209, B_210, B_211]: (r1_tarski(A_209, B_210) | k4_xboole_0(k2_xboole_0(A_209, B_211), B_210)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_277])).
% 48.41/38.77  tff(c_3640, plain, (![A_214, B_215, B_216]: (r1_tarski(k4_xboole_0(A_214, B_215), B_216) | k4_xboole_0(A_214, B_216)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_220, c_3539])).
% 48.41/38.77  tff(c_14343, plain, (![A_428, B_429, B_430]: (k4_xboole_0(A_428, B_429)=B_430 | k1_xboole_0!=B_430 | k4_xboole_0(A_428, B_430)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3640, c_666])).
% 48.41/38.77  tff(c_56893, plain, (![B_429]: (k4_xboole_0(k10_relat_1('#skF_5', k1_xboole_0), B_429)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7254, c_14343])).
% 48.41/38.77  tff(c_7587, plain, (![A_322, B_323]: (k4_xboole_0(k10_relat_1('#skF_5', A_322), B_323)=k1_xboole_0 | k1_xboole_0!=A_322)), inference(resolution, [status(thm)], [c_7201, c_1171])).
% 48.41/38.77  tff(c_867, plain, (![B_111, A_112]: (B_111=A_112 | ~r1_tarski(B_111, A_112) | k1_xboole_0!=A_112)), inference(resolution, [status(thm)], [c_645, c_8])).
% 48.41/38.77  tff(c_905, plain, (![B_9, A_8]: (B_9=A_8 | k1_xboole_0!=B_9 | k4_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_867])).
% 48.41/38.77  tff(c_8192, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7587, c_905])).
% 48.41/38.77  tff(c_60, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 48.41/38.77  tff(c_50, plain, (![C_38, A_36, B_37]: (k6_subset_1(k9_relat_1(C_38, A_36), k9_relat_1(C_38, B_37))=k9_relat_1(C_38, k6_subset_1(A_36, B_37)) | ~v2_funct_1(C_38) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_86])).
% 48.41/38.77  tff(c_66, plain, (![C_38, A_36, B_37]: (k4_xboole_0(k9_relat_1(C_38, A_36), k9_relat_1(C_38, B_37))=k9_relat_1(C_38, k4_xboole_0(A_36, B_37)) | ~v2_funct_1(C_38) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_50])).
% 48.41/38.77  tff(c_54, plain, (![B_43, A_42]: (r1_tarski(k9_relat_1(B_43, k10_relat_1(B_43, A_42)), A_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_98])).
% 48.41/38.77  tff(c_32012, plain, (![A_640, A_641]: (r1_tarski(k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_640)), k4_xboole_0(A_640, A_641)) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | k1_xboole_0!=A_641)), inference(superposition, [status(thm), theory('equality')], [c_31855, c_54])).
% 48.41/38.77  tff(c_180609, plain, (![A_1688, A_1689]: (r1_tarski(k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_1688)), k4_xboole_0(A_1688, A_1689)) | k1_xboole_0!=A_1689)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_32012])).
% 48.41/38.77  tff(c_181214, plain, (![A_1690]: (r1_tarski(k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_1690)), A_1690))), inference(superposition, [status(thm), theory('equality')], [c_26, c_180609])).
% 48.41/38.77  tff(c_182713, plain, (![A_1692]: (k4_xboole_0(k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_1692)), A_1692)=k1_xboole_0)), inference(resolution, [status(thm)], [c_181214, c_16])).
% 48.41/38.77  tff(c_183510, plain, (![B_37]: (k9_relat_1('#skF_5', k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', B_37)), B_37))=k1_xboole_0 | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_182713])).
% 48.41/38.77  tff(c_183735, plain, (![B_37]: (k9_relat_1('#skF_5', k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', B_37)), B_37))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_183510])).
% 48.41/38.77  tff(c_193731, plain, (![B_1725]: (k9_relat_1('#skF_5', k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', B_1725)), B_1725))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_183510])).
% 48.41/38.77  tff(c_56, plain, (![A_44, B_45]: (r1_tarski(A_44, k10_relat_1(B_45, k9_relat_1(B_45, A_44))) | ~r1_tarski(A_44, k1_relat_1(B_45)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_104])).
% 48.41/38.77  tff(c_3479, plain, (![B_207, A_208]: (B_207=A_208 | ~r1_tarski(B_207, A_208) | k4_xboole_0(A_208, B_207)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_486])).
% 48.41/38.77  tff(c_3525, plain, (![B_45, A_44]: (k10_relat_1(B_45, k9_relat_1(B_45, A_44))=A_44 | k4_xboole_0(k10_relat_1(B_45, k9_relat_1(B_45, A_44)), A_44)!=k1_xboole_0 | ~r1_tarski(A_44, k1_relat_1(B_45)) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_56, c_3479])).
% 48.41/38.77  tff(c_193799, plain, (![B_1725]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', B_1725)), B_1725)))=k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', B_1725)), B_1725) | k4_xboole_0(k10_relat_1('#skF_5', k1_xboole_0), k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', B_1725)), B_1725))!=k1_xboole_0 | ~r1_tarski(k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', B_1725)), B_1725), k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_193731, c_3525])).
% 48.41/38.77  tff(c_194100, plain, (![B_1725]: (k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', B_1725)), B_1725)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_33392, c_56893, c_8192, c_183735, c_193799])).
% 48.41/38.77  tff(c_197, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | k4_xboole_0(A_59, B_60)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 48.41/38.77  tff(c_58, plain, (~r1_tarski(k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_4')), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 48.41/38.77  tff(c_204, plain, (k4_xboole_0(k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_4')), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_197, c_58])).
% 48.41/38.77  tff(c_194608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194100, c_204])).
% 48.41/38.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.41/38.77  
% 48.41/38.77  Inference rules
% 48.41/38.77  ----------------------
% 48.41/38.77  #Ref     : 17
% 48.41/38.77  #Sup     : 51893
% 48.41/38.77  #Fact    : 0
% 48.41/38.77  #Define  : 0
% 48.41/38.77  #Split   : 17
% 48.41/38.77  #Chain   : 0
% 48.41/38.77  #Close   : 0
% 48.41/38.77  
% 48.41/38.77  Ordering : KBO
% 48.41/38.77  
% 48.41/38.77  Simplification rules
% 48.41/38.77  ----------------------
% 48.41/38.77  #Subsume      : 22882
% 48.41/38.77  #Demod        : 38389
% 48.41/38.77  #Tautology    : 14341
% 48.41/38.77  #SimpNegUnit  : 677
% 48.41/38.77  #BackRed      : 332
% 48.41/38.77  
% 48.41/38.77  #Partial instantiations: 0
% 48.41/38.77  #Strategies tried      : 1
% 48.41/38.77  
% 48.41/38.77  Timing (in seconds)
% 48.41/38.77  ----------------------
% 48.41/38.78  Preprocessing        : 0.34
% 48.41/38.78  Parsing              : 0.18
% 48.41/38.78  CNF conversion       : 0.02
% 48.41/38.78  Main loop            : 37.66
% 48.41/38.78  Inferencing          : 3.26
% 48.41/38.78  Reduction            : 17.36
% 48.41/38.78  Demodulation         : 15.10
% 48.41/38.78  BG Simplification    : 0.40
% 48.41/38.78  Subsumption          : 15.47
% 48.41/38.78  Abstraction          : 0.73
% 48.41/38.78  MUC search           : 0.00
% 48.41/38.78  Cooper               : 0.00
% 48.41/38.78  Total                : 38.04
% 48.41/38.78  Index Insertion      : 0.00
% 48.41/38.78  Index Deletion       : 0.00
% 48.41/38.78  Index Matching       : 0.00
% 48.41/38.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
