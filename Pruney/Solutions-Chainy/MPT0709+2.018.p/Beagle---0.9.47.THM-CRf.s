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
% DateTime   : Thu Dec  3 10:05:26 EST 2020

% Result     : Theorem 8.70s
% Output     : CNFRefutation 8.90s
% Verified   : 
% Statistics : Number of formulae       :  136 (1738 expanded)
%              Number of leaves         :   38 ( 616 expanded)
%              Depth                    :   34
%              Number of atoms          :  280 (4463 expanded)
%              Number of equality atoms :   64 (1064 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_48,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    ! [A_25] :
      ( v1_relat_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,k10_relat_1(B_30,k9_relat_1(B_30,A_29)))
      | ~ r1_tarski(A_29,k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k10_relat_1(B_19,A_18),k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_165,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_813,plain,(
    ! [B_97,A_98] :
      ( k10_relat_1(B_97,A_98) = k1_relat_1(B_97)
      | ~ r1_tarski(k1_relat_1(B_97),k10_relat_1(B_97,A_98))
      | ~ v1_relat_1(B_97) ) ),
    inference(resolution,[status(thm)],[c_28,c_165])).

tff(c_838,plain,(
    ! [B_30] :
      ( k10_relat_1(B_30,k9_relat_1(B_30,k1_relat_1(B_30))) = k1_relat_1(B_30)
      | ~ r1_tarski(k1_relat_1(B_30),k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_40,c_813])).

tff(c_850,plain,(
    ! [B_30] :
      ( k10_relat_1(B_30,k9_relat_1(B_30,k1_relat_1(B_30))) = k1_relat_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_838])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_356,plain,(
    ! [B_80,A_81] :
      ( k9_relat_1(B_80,k10_relat_1(B_80,A_81)) = A_81
      | ~ r1_tarski(A_81,k2_relat_1(B_80))
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_369,plain,(
    ! [B_82] :
      ( k9_relat_1(B_82,k10_relat_1(B_82,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_14,c_356])).

tff(c_236,plain,(
    ! [B_67,A_68] :
      ( k9_relat_1(B_67,A_68) != k1_xboole_0
      | ~ r1_tarski(A_68,k1_relat_1(B_67))
      | k1_xboole_0 = A_68
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_255,plain,(
    ! [B_19,A_18] :
      ( k9_relat_1(B_19,k10_relat_1(B_19,A_18)) != k1_xboole_0
      | k10_relat_1(B_19,A_18) = k1_xboole_0
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_236])).

tff(c_398,plain,(
    ! [B_83] :
      ( k10_relat_1(B_83,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_255])).

tff(c_404,plain,
    ( k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_398])).

tff(c_408,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_404])).

tff(c_32,plain,(
    ! [C_24,A_22,B_23] :
      ( r1_tarski(k10_relat_1(C_24,A_22),k10_relat_1(C_24,B_23))
      | ~ r1_tarski(A_22,B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_421,plain,(
    ! [A_22] :
      ( r1_tarski(k10_relat_1('#skF_2',A_22),k1_xboole_0)
      | ~ r1_tarski(A_22,k1_xboole_0)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_32])).

tff(c_437,plain,(
    ! [A_22] :
      ( r1_tarski(k10_relat_1('#skF_2',A_22),k1_xboole_0)
      | ~ r1_tarski(A_22,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_421])).

tff(c_452,plain,(
    ! [A_84] :
      ( r1_tarski(k10_relat_1('#skF_2',A_84),k1_xboole_0)
      | ~ r1_tarski(A_84,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_421])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_454,plain,(
    ! [A_84] :
      ( k10_relat_1('#skF_2',A_84) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1('#skF_2',A_84))
      | ~ r1_tarski(A_84,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_452,c_2])).

tff(c_492,plain,(
    ! [A_88] :
      ( k10_relat_1('#skF_2',A_88) = k1_xboole_0
      | ~ r1_tarski(A_88,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_454])).

tff(c_515,plain,(
    ! [A_89] :
      ( k10_relat_1('#skF_2',k10_relat_1('#skF_2',A_89)) = k1_xboole_0
      | ~ r1_tarski(A_89,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_437,c_492])).

tff(c_20,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    ! [C_28,A_26,B_27] :
      ( k6_subset_1(k10_relat_1(C_28,A_26),k10_relat_1(C_28,B_27)) = k10_relat_1(C_28,k6_subset_1(A_26,B_27))
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,(
    ! [C_28,A_26,B_27] :
      ( k4_xboole_0(k10_relat_1(C_28,A_26),k10_relat_1(C_28,B_27)) = k10_relat_1(C_28,k4_xboole_0(A_26,B_27))
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_38])).

tff(c_527,plain,(
    ! [A_26,A_89] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_26,k10_relat_1('#skF_2',A_89))) = k4_xboole_0(k10_relat_1('#skF_2',A_26),k1_xboole_0)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_89,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_57])).

tff(c_1040,plain,(
    ! [A_105,A_106] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_105,k10_relat_1('#skF_2',A_106))) = k10_relat_1('#skF_2',A_105)
      | ~ r1_tarski(A_106,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_16,c_527])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k10_relat_1(B_21,A_20),k10_relat_1(B_21,k2_relat_1(B_21)))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1083,plain,(
    ! [A_105,A_106] :
      ( r1_tarski(k10_relat_1('#skF_2',A_105),k10_relat_1('#skF_2',k2_relat_1('#skF_2')))
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_106,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_30])).

tff(c_1139,plain,(
    ! [A_105,A_106] :
      ( r1_tarski(k10_relat_1('#skF_2',A_105),k10_relat_1('#skF_2',k2_relat_1('#skF_2')))
      | ~ r1_tarski(A_106,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1083])).

tff(c_1352,plain,(
    ! [A_114] : ~ r1_tarski(A_114,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_1363,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_1352])).

tff(c_1365,plain,(
    ! [A_115] : r1_tarski(k10_relat_1('#skF_2',A_115),k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_1373,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k10_relat_1('#skF_2',k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_1365])).

tff(c_1392,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1373])).

tff(c_176,plain,(
    ! [B_19,A_18] :
      ( k10_relat_1(B_19,A_18) = k1_relat_1(B_19)
      | ~ r1_tarski(k1_relat_1(B_19),k10_relat_1(B_19,A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_165])).

tff(c_1403,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1392,c_176])).

tff(c_1411,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1403])).

tff(c_367,plain,(
    ! [B_80] :
      ( k9_relat_1(B_80,k10_relat_1(B_80,k2_relat_1(B_80))) = k2_relat_1(B_80)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_356])).

tff(c_1489,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1411,c_367])).

tff(c_1539,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1489])).

tff(c_320,plain,(
    ! [B_78,A_79] :
      ( k10_relat_1(k2_funct_1(B_78),A_79) = k9_relat_1(B_78,A_79)
      | ~ v2_funct_1(B_78)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_350,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(k9_relat_1(B_78,A_79),k1_relat_1(k2_funct_1(B_78)))
      | ~ v1_relat_1(k2_funct_1(B_78))
      | ~ v2_funct_1(B_78)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_28])).

tff(c_1568,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1539,c_350])).

tff(c_1587,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_1568])).

tff(c_1602,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1587])).

tff(c_1647,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_1602])).

tff(c_1651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1647])).

tff(c_1653,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1587])).

tff(c_34,plain,(
    ! [A_25] :
      ( v1_funct_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_396,plain,(
    ! [B_82] :
      ( k10_relat_1(B_82,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_255])).

tff(c_1659,plain,
    ( k10_relat_1(k2_funct_1('#skF_2'),k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1653,c_396])).

tff(c_1679,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1659])).

tff(c_1682,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1679])).

tff(c_1686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1682])).

tff(c_1688,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1659])).

tff(c_1687,plain,(
    k10_relat_1(k2_funct_1('#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1659])).

tff(c_44,plain,(
    ! [B_34,A_33] :
      ( k10_relat_1(k2_funct_1(B_34),A_33) = k9_relat_1(B_34,A_33)
      | ~ v2_funct_1(B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_467,plain,(
    ! [C_85,A_86,B_87] :
      ( k4_xboole_0(k10_relat_1(C_85,A_86),k10_relat_1(C_85,B_87)) = k10_relat_1(C_85,k4_xboole_0(A_86,B_87))
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_38])).

tff(c_7385,plain,(
    ! [B_215,A_216,B_217] :
      ( k4_xboole_0(k9_relat_1(B_215,A_216),k10_relat_1(k2_funct_1(B_215),B_217)) = k10_relat_1(k2_funct_1(B_215),k4_xboole_0(A_216,B_217))
      | ~ v1_funct_1(k2_funct_1(B_215))
      | ~ v1_relat_1(k2_funct_1(B_215))
      | ~ v2_funct_1(B_215)
      | ~ v1_funct_1(B_215)
      | ~ v1_relat_1(B_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_467])).

tff(c_7449,plain,(
    ! [A_216] :
      ( k10_relat_1(k2_funct_1('#skF_2'),k4_xboole_0(A_216,k1_xboole_0)) = k4_xboole_0(k9_relat_1('#skF_2',A_216),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1687,c_7385])).

tff(c_7512,plain,(
    ! [A_216] : k10_relat_1(k2_funct_1('#skF_2'),A_216) = k9_relat_1('#skF_2',A_216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_1653,c_1688,c_16,c_16,c_7449])).

tff(c_292,plain,(
    ! [B_76,A_77] :
      ( k9_relat_1(k2_funct_1(B_76),A_77) = k10_relat_1(B_76,A_77)
      | ~ v2_funct_1(B_76)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_24,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2085,plain,(
    ! [B_128] :
      ( k10_relat_1(B_128,k1_relat_1(k2_funct_1(B_128))) = k2_relat_1(k2_funct_1(B_128))
      | ~ v1_relat_1(k2_funct_1(B_128))
      | ~ v2_funct_1(B_128)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_24])).

tff(c_1086,plain,(
    ! [A_105,A_106] :
      ( r1_tarski(k10_relat_1('#skF_2',A_105),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_106,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_28])).

tff(c_1141,plain,(
    ! [A_105,A_106] :
      ( r1_tarski(k10_relat_1('#skF_2',A_105),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_106,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1086])).

tff(c_1157,plain,(
    ! [A_107] : ~ r1_tarski(A_107,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1141])).

tff(c_1168,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_1157])).

tff(c_1169,plain,(
    ! [A_105] : r1_tarski(k10_relat_1('#skF_2',A_105),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1141])).

tff(c_2111,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_1169])).

tff(c_2183,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_1653,c_2111])).

tff(c_1652,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1587])).

tff(c_310,plain,(
    ! [B_76] :
      ( k10_relat_1(B_76,k1_relat_1(k2_funct_1(B_76))) = k2_relat_1(k2_funct_1(B_76))
      | ~ v1_relat_1(k2_funct_1(B_76))
      | ~ v2_funct_1(B_76)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_24])).

tff(c_1513,plain,(
    ! [B_23] :
      ( r1_tarski(k1_relat_1('#skF_2'),k10_relat_1('#skF_2',B_23))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_23)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1411,c_32])).

tff(c_2602,plain,(
    ! [B_133] :
      ( r1_tarski(k1_relat_1('#skF_2'),k10_relat_1('#skF_2',B_133))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1513])).

tff(c_2614,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2')))
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_2602])).

tff(c_2649,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_1653,c_1652,c_2614])).

tff(c_2663,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2649,c_2])).

tff(c_2669,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_2663])).

tff(c_42,plain,(
    ! [B_32,A_31] :
      ( k9_relat_1(B_32,k10_relat_1(B_32,A_31)) = A_31
      | ~ r1_tarski(A_31,k2_relat_1(B_32))
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2689,plain,(
    ! [A_31] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),A_31)) = A_31
      | ~ r1_tarski(A_31,k1_relat_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2669,c_42])).

tff(c_2705,plain,(
    ! [A_31] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),A_31)) = A_31
      | ~ r1_tarski(A_31,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1653,c_1688,c_2689])).

tff(c_14990,plain,(
    ! [A_302] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k9_relat_1('#skF_2',A_302)) = A_302
      | ~ r1_tarski(A_302,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7512,c_2705])).

tff(c_46,plain,(
    ! [B_36,A_35] :
      ( k9_relat_1(k2_funct_1(B_36),A_35) = k10_relat_1(B_36,A_35)
      | ~ v2_funct_1(B_36)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_15023,plain,(
    ! [A_302] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_302)) = A_302
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_302,k1_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14990,c_46])).

tff(c_15138,plain,(
    ! [A_303] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_303)) = A_303
      | ~ r1_tarski(A_303,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_15023])).

tff(c_15159,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_15138])).

tff(c_15180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_15159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.70/3.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.70/3.04  
% 8.70/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.70/3.05  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.70/3.05  
% 8.70/3.05  %Foreground sorts:
% 8.70/3.05  
% 8.70/3.05  
% 8.70/3.05  %Background operators:
% 8.70/3.05  
% 8.70/3.05  
% 8.70/3.05  %Foreground operators:
% 8.70/3.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.70/3.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.70/3.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.70/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.70/3.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.70/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.70/3.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.70/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.70/3.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.70/3.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.70/3.05  tff('#skF_2', type, '#skF_2': $i).
% 8.70/3.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.70/3.05  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.70/3.05  tff('#skF_1', type, '#skF_1': $i).
% 8.70/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.70/3.05  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.70/3.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.70/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.70/3.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.70/3.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.70/3.05  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.70/3.05  
% 8.90/3.07  tff(f_132, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 8.90/3.07  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.90/3.07  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.90/3.07  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 8.90/3.07  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 8.90/3.07  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.90/3.07  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.90/3.07  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.90/3.07  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 8.90/3.07  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 8.90/3.07  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 8.90/3.07  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.90/3.07  tff(f_91, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 8.90/3.07  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 8.90/3.07  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 8.90/3.07  tff(f_121, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 8.90/3.07  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 8.90/3.07  tff(c_48, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.90/3.07  tff(c_52, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.90/3.07  tff(c_56, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.90/3.07  tff(c_54, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.90/3.07  tff(c_50, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.90/3.07  tff(c_36, plain, (![A_25]: (v1_relat_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.90/3.07  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.90/3.07  tff(c_40, plain, (![A_29, B_30]: (r1_tarski(A_29, k10_relat_1(B_30, k9_relat_1(B_30, A_29))) | ~r1_tarski(A_29, k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.90/3.07  tff(c_28, plain, (![B_19, A_18]: (r1_tarski(k10_relat_1(B_19, A_18), k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.90/3.07  tff(c_165, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.90/3.07  tff(c_813, plain, (![B_97, A_98]: (k10_relat_1(B_97, A_98)=k1_relat_1(B_97) | ~r1_tarski(k1_relat_1(B_97), k10_relat_1(B_97, A_98)) | ~v1_relat_1(B_97))), inference(resolution, [status(thm)], [c_28, c_165])).
% 8.90/3.07  tff(c_838, plain, (![B_30]: (k10_relat_1(B_30, k9_relat_1(B_30, k1_relat_1(B_30)))=k1_relat_1(B_30) | ~r1_tarski(k1_relat_1(B_30), k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_40, c_813])).
% 8.90/3.07  tff(c_850, plain, (![B_30]: (k10_relat_1(B_30, k9_relat_1(B_30, k1_relat_1(B_30)))=k1_relat_1(B_30) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_838])).
% 8.90/3.07  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.90/3.07  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.90/3.07  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.90/3.07  tff(c_356, plain, (![B_80, A_81]: (k9_relat_1(B_80, k10_relat_1(B_80, A_81))=A_81 | ~r1_tarski(A_81, k2_relat_1(B_80)) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.90/3.07  tff(c_369, plain, (![B_82]: (k9_relat_1(B_82, k10_relat_1(B_82, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_14, c_356])).
% 8.90/3.07  tff(c_236, plain, (![B_67, A_68]: (k9_relat_1(B_67, A_68)!=k1_xboole_0 | ~r1_tarski(A_68, k1_relat_1(B_67)) | k1_xboole_0=A_68 | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.90/3.07  tff(c_255, plain, (![B_19, A_18]: (k9_relat_1(B_19, k10_relat_1(B_19, A_18))!=k1_xboole_0 | k10_relat_1(B_19, A_18)=k1_xboole_0 | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_28, c_236])).
% 8.90/3.07  tff(c_398, plain, (![B_83]: (k10_relat_1(B_83, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(superposition, [status(thm), theory('equality')], [c_369, c_255])).
% 8.90/3.07  tff(c_404, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_398])).
% 8.90/3.07  tff(c_408, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_404])).
% 8.90/3.07  tff(c_32, plain, (![C_24, A_22, B_23]: (r1_tarski(k10_relat_1(C_24, A_22), k10_relat_1(C_24, B_23)) | ~r1_tarski(A_22, B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.90/3.07  tff(c_421, plain, (![A_22]: (r1_tarski(k10_relat_1('#skF_2', A_22), k1_xboole_0) | ~r1_tarski(A_22, k1_xboole_0) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_408, c_32])).
% 8.90/3.07  tff(c_437, plain, (![A_22]: (r1_tarski(k10_relat_1('#skF_2', A_22), k1_xboole_0) | ~r1_tarski(A_22, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_421])).
% 8.90/3.07  tff(c_452, plain, (![A_84]: (r1_tarski(k10_relat_1('#skF_2', A_84), k1_xboole_0) | ~r1_tarski(A_84, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_421])).
% 8.90/3.07  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.90/3.07  tff(c_454, plain, (![A_84]: (k10_relat_1('#skF_2', A_84)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k10_relat_1('#skF_2', A_84)) | ~r1_tarski(A_84, k1_xboole_0))), inference(resolution, [status(thm)], [c_452, c_2])).
% 8.90/3.07  tff(c_492, plain, (![A_88]: (k10_relat_1('#skF_2', A_88)=k1_xboole_0 | ~r1_tarski(A_88, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_454])).
% 8.90/3.07  tff(c_515, plain, (![A_89]: (k10_relat_1('#skF_2', k10_relat_1('#skF_2', A_89))=k1_xboole_0 | ~r1_tarski(A_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_437, c_492])).
% 8.90/3.07  tff(c_20, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.90/3.07  tff(c_38, plain, (![C_28, A_26, B_27]: (k6_subset_1(k10_relat_1(C_28, A_26), k10_relat_1(C_28, B_27))=k10_relat_1(C_28, k6_subset_1(A_26, B_27)) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.90/3.07  tff(c_57, plain, (![C_28, A_26, B_27]: (k4_xboole_0(k10_relat_1(C_28, A_26), k10_relat_1(C_28, B_27))=k10_relat_1(C_28, k4_xboole_0(A_26, B_27)) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_38])).
% 8.90/3.07  tff(c_527, plain, (![A_26, A_89]: (k10_relat_1('#skF_2', k4_xboole_0(A_26, k10_relat_1('#skF_2', A_89)))=k4_xboole_0(k10_relat_1('#skF_2', A_26), k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_515, c_57])).
% 8.90/3.07  tff(c_1040, plain, (![A_105, A_106]: (k10_relat_1('#skF_2', k4_xboole_0(A_105, k10_relat_1('#skF_2', A_106)))=k10_relat_1('#skF_2', A_105) | ~r1_tarski(A_106, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_16, c_527])).
% 8.90/3.07  tff(c_30, plain, (![B_21, A_20]: (r1_tarski(k10_relat_1(B_21, A_20), k10_relat_1(B_21, k2_relat_1(B_21))) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.90/3.07  tff(c_1083, plain, (![A_105, A_106]: (r1_tarski(k10_relat_1('#skF_2', A_105), k10_relat_1('#skF_2', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2') | ~r1_tarski(A_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1040, c_30])).
% 8.90/3.07  tff(c_1139, plain, (![A_105, A_106]: (r1_tarski(k10_relat_1('#skF_2', A_105), k10_relat_1('#skF_2', k2_relat_1('#skF_2'))) | ~r1_tarski(A_106, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1083])).
% 8.90/3.07  tff(c_1352, plain, (![A_114]: (~r1_tarski(A_114, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1139])).
% 8.90/3.07  tff(c_1363, plain, $false, inference(resolution, [status(thm)], [c_10, c_1352])).
% 8.90/3.07  tff(c_1365, plain, (![A_115]: (r1_tarski(k10_relat_1('#skF_2', A_115), k10_relat_1('#skF_2', k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_1139])).
% 8.90/3.07  tff(c_1373, plain, (r1_tarski(k1_relat_1('#skF_2'), k10_relat_1('#skF_2', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_850, c_1365])).
% 8.90/3.07  tff(c_1392, plain, (r1_tarski(k1_relat_1('#skF_2'), k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1373])).
% 8.90/3.07  tff(c_176, plain, (![B_19, A_18]: (k10_relat_1(B_19, A_18)=k1_relat_1(B_19) | ~r1_tarski(k1_relat_1(B_19), k10_relat_1(B_19, A_18)) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_28, c_165])).
% 8.90/3.07  tff(c_1403, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1392, c_176])).
% 8.90/3.07  tff(c_1411, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1403])).
% 8.90/3.07  tff(c_367, plain, (![B_80]: (k9_relat_1(B_80, k10_relat_1(B_80, k2_relat_1(B_80)))=k2_relat_1(B_80) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_6, c_356])).
% 8.90/3.07  tff(c_1489, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1411, c_367])).
% 8.90/3.07  tff(c_1539, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1489])).
% 8.90/3.07  tff(c_320, plain, (![B_78, A_79]: (k10_relat_1(k2_funct_1(B_78), A_79)=k9_relat_1(B_78, A_79) | ~v2_funct_1(B_78) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.90/3.07  tff(c_350, plain, (![B_78, A_79]: (r1_tarski(k9_relat_1(B_78, A_79), k1_relat_1(k2_funct_1(B_78))) | ~v1_relat_1(k2_funct_1(B_78)) | ~v2_funct_1(B_78) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(superposition, [status(thm), theory('equality')], [c_320, c_28])).
% 8.90/3.07  tff(c_1568, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1539, c_350])).
% 8.90/3.07  tff(c_1587, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_1568])).
% 8.90/3.07  tff(c_1602, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1587])).
% 8.90/3.07  tff(c_1647, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_1602])).
% 8.90/3.07  tff(c_1651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1647])).
% 8.90/3.07  tff(c_1653, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1587])).
% 8.90/3.07  tff(c_34, plain, (![A_25]: (v1_funct_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.90/3.07  tff(c_396, plain, (![B_82]: (k10_relat_1(B_82, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_369, c_255])).
% 8.90/3.07  tff(c_1659, plain, (k10_relat_1(k2_funct_1('#skF_2'), k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1653, c_396])).
% 8.90/3.07  tff(c_1679, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1659])).
% 8.90/3.07  tff(c_1682, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1679])).
% 8.90/3.07  tff(c_1686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1682])).
% 8.90/3.07  tff(c_1688, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1659])).
% 8.90/3.07  tff(c_1687, plain, (k10_relat_1(k2_funct_1('#skF_2'), k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1659])).
% 8.90/3.07  tff(c_44, plain, (![B_34, A_33]: (k10_relat_1(k2_funct_1(B_34), A_33)=k9_relat_1(B_34, A_33) | ~v2_funct_1(B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.90/3.07  tff(c_467, plain, (![C_85, A_86, B_87]: (k4_xboole_0(k10_relat_1(C_85, A_86), k10_relat_1(C_85, B_87))=k10_relat_1(C_85, k4_xboole_0(A_86, B_87)) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_38])).
% 8.90/3.07  tff(c_7385, plain, (![B_215, A_216, B_217]: (k4_xboole_0(k9_relat_1(B_215, A_216), k10_relat_1(k2_funct_1(B_215), B_217))=k10_relat_1(k2_funct_1(B_215), k4_xboole_0(A_216, B_217)) | ~v1_funct_1(k2_funct_1(B_215)) | ~v1_relat_1(k2_funct_1(B_215)) | ~v2_funct_1(B_215) | ~v1_funct_1(B_215) | ~v1_relat_1(B_215))), inference(superposition, [status(thm), theory('equality')], [c_44, c_467])).
% 8.90/3.07  tff(c_7449, plain, (![A_216]: (k10_relat_1(k2_funct_1('#skF_2'), k4_xboole_0(A_216, k1_xboole_0))=k4_xboole_0(k9_relat_1('#skF_2', A_216), k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1687, c_7385])).
% 8.90/3.07  tff(c_7512, plain, (![A_216]: (k10_relat_1(k2_funct_1('#skF_2'), A_216)=k9_relat_1('#skF_2', A_216))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_1653, c_1688, c_16, c_16, c_7449])).
% 8.90/3.07  tff(c_292, plain, (![B_76, A_77]: (k9_relat_1(k2_funct_1(B_76), A_77)=k10_relat_1(B_76, A_77) | ~v2_funct_1(B_76) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.90/3.07  tff(c_24, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.90/3.07  tff(c_2085, plain, (![B_128]: (k10_relat_1(B_128, k1_relat_1(k2_funct_1(B_128)))=k2_relat_1(k2_funct_1(B_128)) | ~v1_relat_1(k2_funct_1(B_128)) | ~v2_funct_1(B_128) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(superposition, [status(thm), theory('equality')], [c_292, c_24])).
% 8.90/3.07  tff(c_1086, plain, (![A_105, A_106]: (r1_tarski(k10_relat_1('#skF_2', A_105), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~r1_tarski(A_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1040, c_28])).
% 8.90/3.07  tff(c_1141, plain, (![A_105, A_106]: (r1_tarski(k10_relat_1('#skF_2', A_105), k1_relat_1('#skF_2')) | ~r1_tarski(A_106, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1086])).
% 8.90/3.07  tff(c_1157, plain, (![A_107]: (~r1_tarski(A_107, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1141])).
% 8.90/3.07  tff(c_1168, plain, $false, inference(resolution, [status(thm)], [c_10, c_1157])).
% 8.90/3.07  tff(c_1169, plain, (![A_105]: (r1_tarski(k10_relat_1('#skF_2', A_105), k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_1141])).
% 8.90/3.07  tff(c_2111, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2085, c_1169])).
% 8.90/3.07  tff(c_2183, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_1653, c_2111])).
% 8.90/3.07  tff(c_1652, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_1587])).
% 8.90/3.07  tff(c_310, plain, (![B_76]: (k10_relat_1(B_76, k1_relat_1(k2_funct_1(B_76)))=k2_relat_1(k2_funct_1(B_76)) | ~v1_relat_1(k2_funct_1(B_76)) | ~v2_funct_1(B_76) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_292, c_24])).
% 8.90/3.07  tff(c_1513, plain, (![B_23]: (r1_tarski(k1_relat_1('#skF_2'), k10_relat_1('#skF_2', B_23)) | ~r1_tarski(k2_relat_1('#skF_2'), B_23) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1411, c_32])).
% 8.90/3.07  tff(c_2602, plain, (![B_133]: (r1_tarski(k1_relat_1('#skF_2'), k10_relat_1('#skF_2', B_133)) | ~r1_tarski(k2_relat_1('#skF_2'), B_133))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1513])).
% 8.90/3.07  tff(c_2614, plain, (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_310, c_2602])).
% 8.90/3.07  tff(c_2649, plain, (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_1653, c_1652, c_2614])).
% 8.90/3.07  tff(c_2663, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_2649, c_2])).
% 8.90/3.07  tff(c_2669, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_2663])).
% 8.90/3.07  tff(c_42, plain, (![B_32, A_31]: (k9_relat_1(B_32, k10_relat_1(B_32, A_31))=A_31 | ~r1_tarski(A_31, k2_relat_1(B_32)) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.90/3.07  tff(c_2689, plain, (![A_31]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), A_31))=A_31 | ~r1_tarski(A_31, k1_relat_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2669, c_42])).
% 8.90/3.07  tff(c_2705, plain, (![A_31]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), A_31))=A_31 | ~r1_tarski(A_31, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1653, c_1688, c_2689])).
% 8.90/3.07  tff(c_14990, plain, (![A_302]: (k9_relat_1(k2_funct_1('#skF_2'), k9_relat_1('#skF_2', A_302))=A_302 | ~r1_tarski(A_302, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7512, c_2705])).
% 8.90/3.07  tff(c_46, plain, (![B_36, A_35]: (k9_relat_1(k2_funct_1(B_36), A_35)=k10_relat_1(B_36, A_35) | ~v2_funct_1(B_36) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.90/3.07  tff(c_15023, plain, (![A_302]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_302))=A_302 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_302, k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_14990, c_46])).
% 8.90/3.07  tff(c_15138, plain, (![A_303]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_303))=A_303 | ~r1_tarski(A_303, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_15023])).
% 8.90/3.07  tff(c_15159, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(resolution, [status(thm)], [c_52, c_15138])).
% 8.90/3.07  tff(c_15180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_15159])).
% 8.90/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.90/3.07  
% 8.90/3.07  Inference rules
% 8.90/3.07  ----------------------
% 8.90/3.07  #Ref     : 0
% 8.90/3.07  #Sup     : 3369
% 8.90/3.07  #Fact    : 0
% 8.90/3.07  #Define  : 0
% 8.90/3.07  #Split   : 15
% 8.90/3.07  #Chain   : 0
% 8.90/3.07  #Close   : 0
% 8.90/3.07  
% 8.90/3.07  Ordering : KBO
% 8.90/3.07  
% 8.90/3.07  Simplification rules
% 8.90/3.07  ----------------------
% 8.90/3.07  #Subsume      : 1220
% 8.90/3.07  #Demod        : 5306
% 8.90/3.07  #Tautology    : 1170
% 8.90/3.07  #SimpNegUnit  : 120
% 8.90/3.07  #BackRed      : 24
% 8.90/3.07  
% 8.90/3.07  #Partial instantiations: 0
% 8.90/3.07  #Strategies tried      : 1
% 8.90/3.07  
% 8.90/3.07  Timing (in seconds)
% 8.90/3.07  ----------------------
% 8.90/3.07  Preprocessing        : 0.34
% 8.90/3.07  Parsing              : 0.18
% 8.90/3.07  CNF conversion       : 0.02
% 8.90/3.07  Main loop            : 1.95
% 8.90/3.07  Inferencing          : 0.55
% 8.90/3.07  Reduction            : 0.77
% 8.90/3.07  Demodulation         : 0.59
% 8.90/3.07  BG Simplification    : 0.06
% 8.90/3.07  Subsumption          : 0.45
% 8.90/3.07  Abstraction          : 0.09
% 8.90/3.07  MUC search           : 0.00
% 8.90/3.07  Cooper               : 0.00
% 8.90/3.07  Total                : 2.33
% 8.90/3.07  Index Insertion      : 0.00
% 8.90/3.07  Index Deletion       : 0.00
% 8.90/3.07  Index Matching       : 0.00
% 8.90/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
