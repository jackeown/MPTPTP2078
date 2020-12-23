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
% DateTime   : Thu Dec  3 10:05:25 EST 2020

% Result     : Theorem 11.94s
% Output     : CNFRefutation 12.11s
% Verified   : 
% Statistics : Number of formulae       :  129 (1613 expanded)
%              Number of leaves         :   41 ( 585 expanded)
%              Depth                    :   32
%              Number of atoms          :  246 (3121 expanded)
%              Number of equality atoms :   70 (1258 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
          & r1_tarski(A,k1_relat_1(C))
          & v2_funct_1(C) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(c_50,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_58,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,B_54) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_12,c_142])).

tff(c_244,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_274,plain,(
    ! [B_67] : k3_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_279,plain,(
    ! [B_67] : k3_xboole_0(B_67,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_2])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_263,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_244])).

tff(c_347,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_263])).

tff(c_22,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [C_29,A_27,B_28] :
      ( k6_subset_1(k10_relat_1(C_29,A_27),k10_relat_1(C_29,B_28)) = k10_relat_1(C_29,k6_subset_1(A_27,B_28))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1189,plain,(
    ! [C_114,A_115,B_116] :
      ( k4_xboole_0(k10_relat_1(C_114,A_115),k10_relat_1(C_114,B_116)) = k10_relat_1(C_114,k4_xboole_0(A_115,B_116))
      | ~ v1_funct_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_38])).

tff(c_1202,plain,(
    ! [C_114,B_116] :
      ( k10_relat_1(C_114,k4_xboole_0(B_116,B_116)) = k1_xboole_0
      | ~ v1_funct_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1189,c_347])).

tff(c_1243,plain,(
    ! [C_117] :
      ( k10_relat_1(C_117,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_1202])).

tff(c_1249,plain,
    ( k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1243])).

tff(c_1253,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1249])).

tff(c_28,plain,(
    ! [A_20] :
      ( k10_relat_1(A_20,k2_relat_1(A_20)) = k1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_297,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(k10_relat_1(B_68,A_69),k10_relat_1(B_68,k2_relat_1(B_68)))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1068,plain,(
    ! [B_108,A_109] :
      ( k2_xboole_0(k10_relat_1(B_108,A_109),k10_relat_1(B_108,k2_relat_1(B_108))) = k10_relat_1(B_108,k2_relat_1(B_108))
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_297,c_10])).

tff(c_1101,plain,(
    ! [A_20,A_109] :
      ( k2_xboole_0(k10_relat_1(A_20,A_109),k1_relat_1(A_20)) = k10_relat_1(A_20,k2_relat_1(A_20))
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1068])).

tff(c_1263,plain,
    ( k2_xboole_0(k1_xboole_0,k1_relat_1('#skF_2')) = k10_relat_1('#skF_2',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_1101])).

tff(c_1295,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_154,c_1263])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_926,plain,(
    ! [B_99,A_100] :
      ( k9_relat_1(B_99,k10_relat_1(B_99,A_100)) = A_100
      | ~ r1_tarski(A_100,k2_relat_1(B_99))
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_933,plain,(
    ! [B_99] :
      ( k9_relat_1(B_99,k10_relat_1(B_99,k2_relat_1(B_99))) = k2_relat_1(B_99)
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(resolution,[status(thm)],[c_8,c_926])).

tff(c_1353,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1295,c_933])).

tff(c_1402,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1353])).

tff(c_467,plain,(
    ! [B_79,A_80] :
      ( k10_relat_1(k2_funct_1(B_79),A_80) = k9_relat_1(B_79,A_80)
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k10_relat_1(B_19,A_18),k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1552,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(k9_relat_1(B_120,A_121),k1_relat_1(k2_funct_1(B_120)))
      | ~ v1_relat_1(k2_funct_1(B_120))
      | ~ v2_funct_1(B_120)
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_26])).

tff(c_1560,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1402,c_1552])).

tff(c_1579,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_1560])).

tff(c_1583,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1579])).

tff(c_1586,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_1583])).

tff(c_1590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1586])).

tff(c_1592,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1579])).

tff(c_34,plain,(
    ! [A_26] :
      ( v1_funct_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1240,plain,(
    ! [C_114] :
      ( k10_relat_1(C_114,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_1202])).

tff(c_1596,plain,
    ( k10_relat_1(k2_funct_1('#skF_2'),k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1592,c_1240])).

tff(c_1638,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1596])).

tff(c_1641,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1638])).

tff(c_1645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1641])).

tff(c_1646,plain,(
    k10_relat_1(k2_funct_1('#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1596])).

tff(c_44,plain,(
    ! [B_35,A_34] :
      ( k10_relat_1(k2_funct_1(B_35),A_34) = k9_relat_1(B_35,A_34)
      | ~ v2_funct_1(B_35)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_810,plain,(
    ! [C_92,A_93,B_94] :
      ( k2_xboole_0(k10_relat_1(C_92,A_93),k10_relat_1(C_92,B_94)) = k10_relat_1(C_92,k2_xboole_0(A_93,B_94))
      | ~ v1_relat_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6452,plain,(
    ! [B_185,A_186,A_187] :
      ( k2_xboole_0(k10_relat_1(k2_funct_1(B_185),A_186),k9_relat_1(B_185,A_187)) = k10_relat_1(k2_funct_1(B_185),k2_xboole_0(A_186,A_187))
      | ~ v1_relat_1(k2_funct_1(B_185))
      | ~ v2_funct_1(B_185)
      | ~ v1_funct_1(B_185)
      | ~ v1_relat_1(B_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_810])).

tff(c_6485,plain,(
    ! [A_187] :
      ( k10_relat_1(k2_funct_1('#skF_2'),k2_xboole_0(k1_xboole_0,A_187)) = k2_xboole_0(k1_xboole_0,k9_relat_1('#skF_2',A_187))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_6452])).

tff(c_6536,plain,(
    ! [A_187] : k10_relat_1(k2_funct_1('#skF_2'),A_187) = k9_relat_1('#skF_2',A_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_1592,c_154,c_154,c_6485])).

tff(c_1647,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1596])).

tff(c_1717,plain,(
    ! [A_123,A_124] :
      ( k2_xboole_0(k10_relat_1(A_123,A_124),k1_relat_1(A_123)) = k10_relat_1(A_123,k2_xboole_0(A_124,k2_relat_1(A_123)))
      | ~ v1_relat_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_810])).

tff(c_1736,plain,
    ( k10_relat_1(k2_funct_1('#skF_2'),k2_xboole_0(k1_xboole_0,k2_relat_1(k2_funct_1('#skF_2')))) = k2_xboole_0(k1_xboole_0,k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_1717])).

tff(c_1769,plain,(
    k10_relat_1(k2_funct_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2'))) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1592,c_154,c_154,c_1736])).

tff(c_2163,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1769,c_933])).

tff(c_2222,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) = k2_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1647,c_2163])).

tff(c_46,plain,(
    ! [B_37,A_36] :
      ( k9_relat_1(k2_funct_1(B_37),A_36) = k10_relat_1(B_37,A_36)
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2539,plain,
    ( k10_relat_1('#skF_2',k1_relat_1(k2_funct_1('#skF_2'))) = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2222,c_46])).

tff(c_2563,plain,(
    k10_relat_1('#skF_2',k1_relat_1(k2_funct_1('#skF_2'))) = k2_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2539])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k10_relat_1(B_22,A_21),k10_relat_1(B_22,k2_relat_1(B_22)))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1377,plain,(
    ! [A_21] :
      ( r1_tarski(k10_relat_1('#skF_2',A_21),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1295,c_30])).

tff(c_1418,plain,(
    ! [A_21] : r1_tarski(k10_relat_1('#skF_2',A_21),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1377])).

tff(c_2588,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_1418])).

tff(c_1591,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1579])).

tff(c_498,plain,(
    ! [B_79] :
      ( k9_relat_1(B_79,k2_relat_1(k2_funct_1(B_79))) = k1_relat_1(k2_funct_1(B_79))
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k2_funct_1(B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_467])).

tff(c_48,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,B_39)
      | ~ v2_funct_1(C_40)
      | ~ r1_tarski(A_38,k1_relat_1(C_40))
      | ~ r1_tarski(k9_relat_1(C_40,A_38),k9_relat_1(C_40,B_39))
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1431,plain,(
    ! [B_39] :
      ( r1_tarski(k1_relat_1('#skF_2'),B_39)
      | ~ v2_funct_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
      | ~ r1_tarski(k2_relat_1('#skF_2'),k9_relat_1('#skF_2',B_39))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1402,c_48])).

tff(c_2991,plain,(
    ! [B_137] :
      ( r1_tarski(k1_relat_1('#skF_2'),B_137)
      | ~ r1_tarski(k2_relat_1('#skF_2'),k9_relat_1('#skF_2',B_137)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_8,c_52,c_1431])).

tff(c_2995,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2')))
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_2991])).

tff(c_3018,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_58,c_56,c_52,c_1591,c_2995])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3032,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3018,c_4])).

tff(c_3041,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2588,c_3032])).

tff(c_42,plain,(
    ! [B_33,A_32] :
      ( k9_relat_1(B_33,k10_relat_1(B_33,A_32)) = A_32
      | ~ r1_tarski(A_32,k2_relat_1(B_33))
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3080,plain,(
    ! [A_32] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),A_32)) = A_32
      | ~ r1_tarski(A_32,k1_relat_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3041,c_42])).

tff(c_3108,plain,(
    ! [A_32] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),A_32)) = A_32
      | ~ r1_tarski(A_32,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1647,c_3080])).

tff(c_25935,plain,(
    ! [A_356] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k9_relat_1('#skF_2',A_356)) = A_356
      | ~ r1_tarski(A_356,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6536,c_3108])).

tff(c_25993,plain,(
    ! [A_356] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_356)) = A_356
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_356,k1_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25935,c_46])).

tff(c_26160,plain,(
    ! [A_357] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_357)) = A_357
      | ~ r1_tarski(A_357,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_25993])).

tff(c_26183,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_26160])).

tff(c_26206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_26183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.94/5.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.94/5.32  
% 11.94/5.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.94/5.33  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.94/5.33  
% 11.94/5.33  %Foreground sorts:
% 11.94/5.33  
% 11.94/5.33  
% 11.94/5.33  %Background operators:
% 11.94/5.33  
% 11.94/5.33  
% 11.94/5.33  %Foreground operators:
% 11.94/5.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.94/5.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.94/5.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.94/5.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.94/5.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.94/5.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.94/5.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.94/5.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.94/5.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.94/5.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.94/5.33  tff('#skF_2', type, '#skF_2': $i).
% 11.94/5.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.94/5.33  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.94/5.33  tff('#skF_1', type, '#skF_1': $i).
% 11.94/5.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.94/5.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.94/5.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.94/5.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.94/5.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.94/5.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.94/5.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.94/5.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.94/5.33  
% 12.11/5.35  tff(f_134, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 12.11/5.35  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.11/5.35  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.11/5.35  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.11/5.35  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.11/5.35  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 12.11/5.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.11/5.35  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.11/5.35  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.11/5.35  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 12.11/5.35  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 12.11/5.35  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 12.11/5.35  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.11/5.35  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 12.11/5.35  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 12.11/5.35  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 12.11/5.35  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 12.11/5.35  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 12.11/5.35  tff(f_123, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 12.11/5.35  tff(c_50, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.11/5.35  tff(c_54, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.11/5.35  tff(c_58, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.11/5.35  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.11/5.35  tff(c_52, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 12.11/5.35  tff(c_36, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.11/5.35  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.11/5.35  tff(c_142, plain, (![A_53, B_54]: (k2_xboole_0(A_53, B_54)=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.11/5.35  tff(c_154, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(resolution, [status(thm)], [c_12, c_142])).
% 12.11/5.35  tff(c_244, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.11/5.35  tff(c_18, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.11/5.35  tff(c_274, plain, (![B_67]: (k3_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_18])).
% 12.11/5.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.11/5.35  tff(c_279, plain, (![B_67]: (k3_xboole_0(B_67, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_274, c_2])).
% 12.11/5.35  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.11/5.35  tff(c_263, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_244])).
% 12.11/5.35  tff(c_347, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_279, c_263])).
% 12.11/5.35  tff(c_22, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.11/5.35  tff(c_38, plain, (![C_29, A_27, B_28]: (k6_subset_1(k10_relat_1(C_29, A_27), k10_relat_1(C_29, B_28))=k10_relat_1(C_29, k6_subset_1(A_27, B_28)) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.11/5.35  tff(c_1189, plain, (![C_114, A_115, B_116]: (k4_xboole_0(k10_relat_1(C_114, A_115), k10_relat_1(C_114, B_116))=k10_relat_1(C_114, k4_xboole_0(A_115, B_116)) | ~v1_funct_1(C_114) | ~v1_relat_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_38])).
% 12.11/5.35  tff(c_1202, plain, (![C_114, B_116]: (k10_relat_1(C_114, k4_xboole_0(B_116, B_116))=k1_xboole_0 | ~v1_funct_1(C_114) | ~v1_relat_1(C_114))), inference(superposition, [status(thm), theory('equality')], [c_1189, c_347])).
% 12.11/5.35  tff(c_1243, plain, (![C_117]: (k10_relat_1(C_117, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_117) | ~v1_relat_1(C_117))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_1202])).
% 12.11/5.35  tff(c_1249, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_58, c_1243])).
% 12.11/5.35  tff(c_1253, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1249])).
% 12.11/5.35  tff(c_28, plain, (![A_20]: (k10_relat_1(A_20, k2_relat_1(A_20))=k1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.11/5.35  tff(c_297, plain, (![B_68, A_69]: (r1_tarski(k10_relat_1(B_68, A_69), k10_relat_1(B_68, k2_relat_1(B_68))) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.11/5.35  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.11/5.35  tff(c_1068, plain, (![B_108, A_109]: (k2_xboole_0(k10_relat_1(B_108, A_109), k10_relat_1(B_108, k2_relat_1(B_108)))=k10_relat_1(B_108, k2_relat_1(B_108)) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_297, c_10])).
% 12.11/5.35  tff(c_1101, plain, (![A_20, A_109]: (k2_xboole_0(k10_relat_1(A_20, A_109), k1_relat_1(A_20))=k10_relat_1(A_20, k2_relat_1(A_20)) | ~v1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1068])).
% 12.11/5.35  tff(c_1263, plain, (k2_xboole_0(k1_xboole_0, k1_relat_1('#skF_2'))=k10_relat_1('#skF_2', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1253, c_1101])).
% 12.11/5.35  tff(c_1295, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_154, c_1263])).
% 12.11/5.35  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.11/5.35  tff(c_926, plain, (![B_99, A_100]: (k9_relat_1(B_99, k10_relat_1(B_99, A_100))=A_100 | ~r1_tarski(A_100, k2_relat_1(B_99)) | ~v1_funct_1(B_99) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.11/5.35  tff(c_933, plain, (![B_99]: (k9_relat_1(B_99, k10_relat_1(B_99, k2_relat_1(B_99)))=k2_relat_1(B_99) | ~v1_funct_1(B_99) | ~v1_relat_1(B_99))), inference(resolution, [status(thm)], [c_8, c_926])).
% 12.11/5.35  tff(c_1353, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1295, c_933])).
% 12.11/5.35  tff(c_1402, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1353])).
% 12.11/5.35  tff(c_467, plain, (![B_79, A_80]: (k10_relat_1(k2_funct_1(B_79), A_80)=k9_relat_1(B_79, A_80) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.11/5.35  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k10_relat_1(B_19, A_18), k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.11/5.35  tff(c_1552, plain, (![B_120, A_121]: (r1_tarski(k9_relat_1(B_120, A_121), k1_relat_1(k2_funct_1(B_120))) | ~v1_relat_1(k2_funct_1(B_120)) | ~v2_funct_1(B_120) | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(superposition, [status(thm), theory('equality')], [c_467, c_26])).
% 12.11/5.35  tff(c_1560, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1402, c_1552])).
% 12.11/5.35  tff(c_1579, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_1560])).
% 12.11/5.35  tff(c_1583, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1579])).
% 12.11/5.35  tff(c_1586, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_1583])).
% 12.11/5.35  tff(c_1590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1586])).
% 12.11/5.35  tff(c_1592, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1579])).
% 12.11/5.35  tff(c_34, plain, (![A_26]: (v1_funct_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.11/5.35  tff(c_1240, plain, (![C_114]: (k10_relat_1(C_114, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_114) | ~v1_relat_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_1202])).
% 12.11/5.35  tff(c_1596, plain, (k10_relat_1(k2_funct_1('#skF_2'), k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1592, c_1240])).
% 12.11/5.35  tff(c_1638, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1596])).
% 12.11/5.35  tff(c_1641, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1638])).
% 12.11/5.35  tff(c_1645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1641])).
% 12.11/5.35  tff(c_1646, plain, (k10_relat_1(k2_funct_1('#skF_2'), k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1596])).
% 12.11/5.35  tff(c_44, plain, (![B_35, A_34]: (k10_relat_1(k2_funct_1(B_35), A_34)=k9_relat_1(B_35, A_34) | ~v2_funct_1(B_35) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.11/5.35  tff(c_810, plain, (![C_92, A_93, B_94]: (k2_xboole_0(k10_relat_1(C_92, A_93), k10_relat_1(C_92, B_94))=k10_relat_1(C_92, k2_xboole_0(A_93, B_94)) | ~v1_relat_1(C_92))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.11/5.35  tff(c_6452, plain, (![B_185, A_186, A_187]: (k2_xboole_0(k10_relat_1(k2_funct_1(B_185), A_186), k9_relat_1(B_185, A_187))=k10_relat_1(k2_funct_1(B_185), k2_xboole_0(A_186, A_187)) | ~v1_relat_1(k2_funct_1(B_185)) | ~v2_funct_1(B_185) | ~v1_funct_1(B_185) | ~v1_relat_1(B_185))), inference(superposition, [status(thm), theory('equality')], [c_44, c_810])).
% 12.11/5.35  tff(c_6485, plain, (![A_187]: (k10_relat_1(k2_funct_1('#skF_2'), k2_xboole_0(k1_xboole_0, A_187))=k2_xboole_0(k1_xboole_0, k9_relat_1('#skF_2', A_187)) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_6452])).
% 12.11/5.35  tff(c_6536, plain, (![A_187]: (k10_relat_1(k2_funct_1('#skF_2'), A_187)=k9_relat_1('#skF_2', A_187))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_1592, c_154, c_154, c_6485])).
% 12.11/5.35  tff(c_1647, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1596])).
% 12.11/5.35  tff(c_1717, plain, (![A_123, A_124]: (k2_xboole_0(k10_relat_1(A_123, A_124), k1_relat_1(A_123))=k10_relat_1(A_123, k2_xboole_0(A_124, k2_relat_1(A_123))) | ~v1_relat_1(A_123) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_28, c_810])).
% 12.11/5.35  tff(c_1736, plain, (k10_relat_1(k2_funct_1('#skF_2'), k2_xboole_0(k1_xboole_0, k2_relat_1(k2_funct_1('#skF_2'))))=k2_xboole_0(k1_xboole_0, k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_1717])).
% 12.11/5.35  tff(c_1769, plain, (k10_relat_1(k2_funct_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2')))=k1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1592, c_154, c_154, c_1736])).
% 12.11/5.35  tff(c_2163, plain, (k9_relat_1(k2_funct_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1769, c_933])).
% 12.11/5.35  tff(c_2222, plain, (k9_relat_1(k2_funct_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))=k2_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1647, c_2163])).
% 12.11/5.35  tff(c_46, plain, (![B_37, A_36]: (k9_relat_1(k2_funct_1(B_37), A_36)=k10_relat_1(B_37, A_36) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.11/5.35  tff(c_2539, plain, (k10_relat_1('#skF_2', k1_relat_1(k2_funct_1('#skF_2')))=k2_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2222, c_46])).
% 12.11/5.35  tff(c_2563, plain, (k10_relat_1('#skF_2', k1_relat_1(k2_funct_1('#skF_2')))=k2_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2539])).
% 12.11/5.35  tff(c_30, plain, (![B_22, A_21]: (r1_tarski(k10_relat_1(B_22, A_21), k10_relat_1(B_22, k2_relat_1(B_22))) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.11/5.35  tff(c_1377, plain, (![A_21]: (r1_tarski(k10_relat_1('#skF_2', A_21), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1295, c_30])).
% 12.11/5.35  tff(c_1418, plain, (![A_21]: (r1_tarski(k10_relat_1('#skF_2', A_21), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1377])).
% 12.11/5.35  tff(c_2588, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2563, c_1418])).
% 12.11/5.35  tff(c_1591, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_1579])).
% 12.11/5.35  tff(c_498, plain, (![B_79]: (k9_relat_1(B_79, k2_relat_1(k2_funct_1(B_79)))=k1_relat_1(k2_funct_1(B_79)) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(k2_funct_1(B_79)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_467])).
% 12.11/5.35  tff(c_48, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, B_39) | ~v2_funct_1(C_40) | ~r1_tarski(A_38, k1_relat_1(C_40)) | ~r1_tarski(k9_relat_1(C_40, A_38), k9_relat_1(C_40, B_39)) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.11/5.35  tff(c_1431, plain, (![B_39]: (r1_tarski(k1_relat_1('#skF_2'), B_39) | ~v2_funct_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1('#skF_2'), k9_relat_1('#skF_2', B_39)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1402, c_48])).
% 12.11/5.35  tff(c_2991, plain, (![B_137]: (r1_tarski(k1_relat_1('#skF_2'), B_137) | ~r1_tarski(k2_relat_1('#skF_2'), k9_relat_1('#skF_2', B_137)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_8, c_52, c_1431])).
% 12.11/5.35  tff(c_2995, plain, (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_498, c_2991])).
% 12.11/5.35  tff(c_3018, plain, (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_58, c_56, c_52, c_1591, c_2995])).
% 12.11/5.35  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.11/5.35  tff(c_3032, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3018, c_4])).
% 12.11/5.35  tff(c_3041, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2588, c_3032])).
% 12.11/5.35  tff(c_42, plain, (![B_33, A_32]: (k9_relat_1(B_33, k10_relat_1(B_33, A_32))=A_32 | ~r1_tarski(A_32, k2_relat_1(B_33)) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.11/5.35  tff(c_3080, plain, (![A_32]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), A_32))=A_32 | ~r1_tarski(A_32, k1_relat_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3041, c_42])).
% 12.11/5.35  tff(c_3108, plain, (![A_32]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), A_32))=A_32 | ~r1_tarski(A_32, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1647, c_3080])).
% 12.11/5.35  tff(c_25935, plain, (![A_356]: (k9_relat_1(k2_funct_1('#skF_2'), k9_relat_1('#skF_2', A_356))=A_356 | ~r1_tarski(A_356, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6536, c_3108])).
% 12.11/5.35  tff(c_25993, plain, (![A_356]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_356))=A_356 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_356, k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_25935, c_46])).
% 12.11/5.35  tff(c_26160, plain, (![A_357]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_357))=A_357 | ~r1_tarski(A_357, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_25993])).
% 12.11/5.35  tff(c_26183, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(resolution, [status(thm)], [c_54, c_26160])).
% 12.11/5.35  tff(c_26206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_26183])).
% 12.11/5.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.11/5.35  
% 12.11/5.35  Inference rules
% 12.11/5.35  ----------------------
% 12.11/5.35  #Ref     : 0
% 12.11/5.35  #Sup     : 6210
% 12.11/5.35  #Fact    : 0
% 12.11/5.35  #Define  : 0
% 12.11/5.35  #Split   : 5
% 12.11/5.35  #Chain   : 0
% 12.11/5.35  #Close   : 0
% 12.11/5.35  
% 12.11/5.35  Ordering : KBO
% 12.11/5.35  
% 12.11/5.35  Simplification rules
% 12.11/5.35  ----------------------
% 12.11/5.35  #Subsume      : 377
% 12.11/5.35  #Demod        : 13725
% 12.11/5.35  #Tautology    : 3169
% 12.11/5.35  #SimpNegUnit  : 1
% 12.11/5.35  #BackRed      : 16
% 12.11/5.35  
% 12.11/5.35  #Partial instantiations: 0
% 12.11/5.35  #Strategies tried      : 1
% 12.11/5.35  
% 12.11/5.35  Timing (in seconds)
% 12.11/5.35  ----------------------
% 12.11/5.35  Preprocessing        : 0.35
% 12.11/5.35  Parsing              : 0.19
% 12.11/5.35  CNF conversion       : 0.02
% 12.11/5.35  Main loop            : 4.11
% 12.11/5.35  Inferencing          : 0.82
% 12.11/5.35  Reduction            : 2.40
% 12.11/5.35  Demodulation         : 2.12
% 12.11/5.35  BG Simplification    : 0.10
% 12.11/5.35  Subsumption          : 0.62
% 12.11/5.35  Abstraction          : 0.18
% 12.11/5.35  MUC search           : 0.00
% 12.11/5.35  Cooper               : 0.00
% 12.11/5.35  Total                : 4.50
% 12.11/5.35  Index Insertion      : 0.00
% 12.11/5.35  Index Deletion       : 0.00
% 12.11/5.35  Index Matching       : 0.00
% 12.11/5.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
