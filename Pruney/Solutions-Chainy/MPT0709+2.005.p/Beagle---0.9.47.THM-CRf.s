%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:25 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 153 expanded)
%              Number of leaves         :   35 (  67 expanded)
%              Depth                    :   21
%              Number of atoms          :  157 ( 296 expanded)
%              Number of equality atoms :   47 (  96 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
          & r1_tarski(A,k1_relat_1(C))
          & v2_funct_1(C) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(c_36,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_123])).

tff(c_20,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_20])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_58])).

tff(c_177,plain,(
    ! [B_44] : k3_xboole_0(B_44,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_67])).

tff(c_318,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_333,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_318])).

tff(c_336,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_333])).

tff(c_18,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [C_22,A_20,B_21] :
      ( k6_subset_1(k9_relat_1(C_22,A_20),k9_relat_1(C_22,B_21)) = k9_relat_1(C_22,k6_subset_1(A_20,B_21))
      | ~ v2_funct_1(C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1111,plain,(
    ! [C_94,A_95,B_96] :
      ( k4_xboole_0(k9_relat_1(C_94,A_95),k9_relat_1(C_94,B_96)) = k9_relat_1(C_94,k4_xboole_0(A_95,B_96))
      | ~ v2_funct_1(C_94)
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_28])).

tff(c_1124,plain,(
    ! [C_94,B_96] :
      ( k9_relat_1(C_94,k4_xboole_0(B_96,B_96)) = k1_xboole_0
      | ~ v2_funct_1(C_94)
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_336])).

tff(c_1154,plain,(
    ! [C_97] :
      ( k9_relat_1(C_97,k1_xboole_0) = k1_xboole_0
      | ~ v2_funct_1(C_97)
      | ~ v1_funct_1(C_97)
      | ~ v1_relat_1(C_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_1124])).

tff(c_1157,plain,
    ( k9_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1154])).

tff(c_1160,plain,(
    k9_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1157])).

tff(c_22,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3490,plain,(
    ! [A_152,B_153] :
      ( k9_relat_1(A_152,k4_xboole_0(k1_relat_1(A_152),B_153)) = k4_xboole_0(k2_relat_1(A_152),k9_relat_1(A_152,B_153))
      | ~ v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1111])).

tff(c_6578,plain,(
    ! [A_192] :
      ( k4_xboole_0(k2_relat_1(A_192),k9_relat_1(A_192,k1_xboole_0)) = k9_relat_1(A_192,k1_relat_1(A_192))
      | ~ v2_funct_1(A_192)
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3490])).

tff(c_6605,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k4_xboole_0(k2_relat_1('#skF_2'),k1_xboole_0)
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1160,c_6578])).

tff(c_6613,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_42,c_38,c_10,c_6605])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,k10_relat_1(B_24,k9_relat_1(B_24,A_23)))
      | ~ r1_tarski(A_23,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_312,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(k10_relat_1(B_53,A_54),k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1288,plain,(
    ! [B_100,A_101] :
      ( k10_relat_1(B_100,A_101) = k1_relat_1(B_100)
      | ~ r1_tarski(k1_relat_1(B_100),k10_relat_1(B_100,A_101))
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_312,c_2])).

tff(c_1295,plain,(
    ! [B_24] :
      ( k10_relat_1(B_24,k9_relat_1(B_24,k1_relat_1(B_24))) = k1_relat_1(B_24)
      | ~ r1_tarski(k1_relat_1(B_24),k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_30,c_1288])).

tff(c_1299,plain,(
    ! [B_24] :
      ( k10_relat_1(B_24,k9_relat_1(B_24,k1_relat_1(B_24))) = k1_relat_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1295])).

tff(c_6691,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6613,c_1299])).

tff(c_6745,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6691])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k10_relat_1(B_19,A_18),k10_relat_1(B_19,k2_relat_1(B_19)))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6819,plain,(
    ! [A_18] :
      ( r1_tarski(k10_relat_1('#skF_2',A_18),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6745,c_26])).

tff(c_6858,plain,(
    ! [A_18] : r1_tarski(k10_relat_1('#skF_2',A_18),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6819])).

tff(c_594,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,k9_relat_1(B_77,k1_relat_1(B_77))) = k9_relat_1(B_77,k10_relat_1(B_77,A_76))
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_635,plain,(
    ! [B_77,A_76] :
      ( r1_tarski(k9_relat_1(B_77,k10_relat_1(B_77,A_76)),A_76)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_8])).

tff(c_686,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,B_82)
      | ~ v2_funct_1(C_83)
      | ~ r1_tarski(A_81,k1_relat_1(C_83))
      | ~ r1_tarski(k9_relat_1(C_83,A_81),k9_relat_1(C_83,B_82))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8208,plain,(
    ! [B_207,B_208] :
      ( r1_tarski(k10_relat_1(B_207,k9_relat_1(B_207,B_208)),B_208)
      | ~ v2_funct_1(B_207)
      | ~ r1_tarski(k10_relat_1(B_207,k9_relat_1(B_207,B_208)),k1_relat_1(B_207))
      | ~ v1_funct_1(B_207)
      | ~ v1_relat_1(B_207) ) ),
    inference(resolution,[status(thm)],[c_635,c_686])).

tff(c_8219,plain,(
    ! [B_208] :
      ( r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_208)),B_208)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6858,c_8208])).

tff(c_8265,plain,(
    ! [B_209] : r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_209)),B_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_8219])).

tff(c_507,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,k10_relat_1(B_70,k9_relat_1(B_70,A_69)))
      | ~ r1_tarski(A_69,k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_513,plain,(
    ! [B_70,A_69] :
      ( k10_relat_1(B_70,k9_relat_1(B_70,A_69)) = A_69
      | ~ r1_tarski(k10_relat_1(B_70,k9_relat_1(B_70,A_69)),A_69)
      | ~ r1_tarski(A_69,k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_507,c_2])).

tff(c_8271,plain,(
    ! [B_209] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_209)) = B_209
      | ~ r1_tarski(B_209,k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8265,c_513])).

tff(c_8898,plain,(
    ! [B_216] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',B_216)) = B_216
      | ~ r1_tarski(B_216,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8271])).

tff(c_8928,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_40,c_8898])).

tff(c_8948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_8928])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:02:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.63/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.63/2.75  
% 7.63/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.63/2.76  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.63/2.76  
% 7.63/2.76  %Foreground sorts:
% 7.63/2.76  
% 7.63/2.76  
% 7.63/2.76  %Background operators:
% 7.63/2.76  
% 7.63/2.76  
% 7.63/2.76  %Foreground operators:
% 7.63/2.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.63/2.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.63/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.63/2.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.63/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.63/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.63/2.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.63/2.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.63/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.63/2.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.63/2.76  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.63/2.76  tff('#skF_1', type, '#skF_1': $i).
% 7.63/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.63/2.76  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.63/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.63/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.63/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.63/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.63/2.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.63/2.76  
% 7.63/2.77  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 7.63/2.77  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.63/2.77  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.63/2.77  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.63/2.77  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.63/2.77  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.63/2.77  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.63/2.77  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.63/2.77  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 7.63/2.77  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 7.63/2.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.63/2.77  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 7.63/2.77  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 7.63/2.77  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 7.63/2.77  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 7.63/2.77  tff(f_91, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 7.63/2.77  tff(c_36, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.63/2.77  tff(c_40, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.63/2.77  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.63/2.77  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.63/2.77  tff(c_38, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.63/2.77  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.63/2.77  tff(c_16, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.63/2.77  tff(c_123, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.63/2.77  tff(c_138, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_16, c_123])).
% 7.63/2.77  tff(c_20, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.63/2.77  tff(c_161, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_138, c_20])).
% 7.63/2.77  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.63/2.77  tff(c_58, plain, (![A_34]: (k1_xboole_0=A_34 | ~r1_tarski(A_34, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.63/2.77  tff(c_67, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_58])).
% 7.63/2.77  tff(c_177, plain, (![B_44]: (k3_xboole_0(B_44, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_161, c_67])).
% 7.63/2.77  tff(c_318, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.63/2.77  tff(c_333, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_318])).
% 7.63/2.77  tff(c_336, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_177, c_333])).
% 7.63/2.77  tff(c_18, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.63/2.77  tff(c_28, plain, (![C_22, A_20, B_21]: (k6_subset_1(k9_relat_1(C_22, A_20), k9_relat_1(C_22, B_21))=k9_relat_1(C_22, k6_subset_1(A_20, B_21)) | ~v2_funct_1(C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.63/2.77  tff(c_1111, plain, (![C_94, A_95, B_96]: (k4_xboole_0(k9_relat_1(C_94, A_95), k9_relat_1(C_94, B_96))=k9_relat_1(C_94, k4_xboole_0(A_95, B_96)) | ~v2_funct_1(C_94) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_28])).
% 7.63/2.77  tff(c_1124, plain, (![C_94, B_96]: (k9_relat_1(C_94, k4_xboole_0(B_96, B_96))=k1_xboole_0 | ~v2_funct_1(C_94) | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(superposition, [status(thm), theory('equality')], [c_1111, c_336])).
% 7.63/2.77  tff(c_1154, plain, (![C_97]: (k9_relat_1(C_97, k1_xboole_0)=k1_xboole_0 | ~v2_funct_1(C_97) | ~v1_funct_1(C_97) | ~v1_relat_1(C_97))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_1124])).
% 7.63/2.77  tff(c_1157, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_1154])).
% 7.63/2.77  tff(c_1160, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1157])).
% 7.63/2.77  tff(c_22, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.63/2.77  tff(c_3490, plain, (![A_152, B_153]: (k9_relat_1(A_152, k4_xboole_0(k1_relat_1(A_152), B_153))=k4_xboole_0(k2_relat_1(A_152), k9_relat_1(A_152, B_153)) | ~v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152) | ~v1_relat_1(A_152))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1111])).
% 7.63/2.77  tff(c_6578, plain, (![A_192]: (k4_xboole_0(k2_relat_1(A_192), k9_relat_1(A_192, k1_xboole_0))=k9_relat_1(A_192, k1_relat_1(A_192)) | ~v2_funct_1(A_192) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192) | ~v1_relat_1(A_192))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3490])).
% 7.63/2.77  tff(c_6605, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k4_xboole_0(k2_relat_1('#skF_2'), k1_xboole_0) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1160, c_6578])).
% 7.63/2.77  tff(c_6613, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_42, c_38, c_10, c_6605])).
% 7.63/2.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.63/2.77  tff(c_30, plain, (![A_23, B_24]: (r1_tarski(A_23, k10_relat_1(B_24, k9_relat_1(B_24, A_23))) | ~r1_tarski(A_23, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.63/2.77  tff(c_312, plain, (![B_53, A_54]: (r1_tarski(k10_relat_1(B_53, A_54), k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.63/2.77  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.63/2.77  tff(c_1288, plain, (![B_100, A_101]: (k10_relat_1(B_100, A_101)=k1_relat_1(B_100) | ~r1_tarski(k1_relat_1(B_100), k10_relat_1(B_100, A_101)) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_312, c_2])).
% 7.63/2.77  tff(c_1295, plain, (![B_24]: (k10_relat_1(B_24, k9_relat_1(B_24, k1_relat_1(B_24)))=k1_relat_1(B_24) | ~r1_tarski(k1_relat_1(B_24), k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_30, c_1288])).
% 7.63/2.77  tff(c_1299, plain, (![B_24]: (k10_relat_1(B_24, k9_relat_1(B_24, k1_relat_1(B_24)))=k1_relat_1(B_24) | ~v1_relat_1(B_24))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1295])).
% 7.63/2.77  tff(c_6691, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6613, c_1299])).
% 7.63/2.77  tff(c_6745, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6691])).
% 7.63/2.77  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k10_relat_1(B_19, A_18), k10_relat_1(B_19, k2_relat_1(B_19))) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.63/2.77  tff(c_6819, plain, (![A_18]: (r1_tarski(k10_relat_1('#skF_2', A_18), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6745, c_26])).
% 7.63/2.77  tff(c_6858, plain, (![A_18]: (r1_tarski(k10_relat_1('#skF_2', A_18), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6819])).
% 7.63/2.77  tff(c_594, plain, (![A_76, B_77]: (k3_xboole_0(A_76, k9_relat_1(B_77, k1_relat_1(B_77)))=k9_relat_1(B_77, k10_relat_1(B_77, A_76)) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.63/2.77  tff(c_635, plain, (![B_77, A_76]: (r1_tarski(k9_relat_1(B_77, k10_relat_1(B_77, A_76)), A_76) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(superposition, [status(thm), theory('equality')], [c_594, c_8])).
% 7.63/2.77  tff(c_686, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, B_82) | ~v2_funct_1(C_83) | ~r1_tarski(A_81, k1_relat_1(C_83)) | ~r1_tarski(k9_relat_1(C_83, A_81), k9_relat_1(C_83, B_82)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.63/2.77  tff(c_8208, plain, (![B_207, B_208]: (r1_tarski(k10_relat_1(B_207, k9_relat_1(B_207, B_208)), B_208) | ~v2_funct_1(B_207) | ~r1_tarski(k10_relat_1(B_207, k9_relat_1(B_207, B_208)), k1_relat_1(B_207)) | ~v1_funct_1(B_207) | ~v1_relat_1(B_207))), inference(resolution, [status(thm)], [c_635, c_686])).
% 7.63/2.77  tff(c_8219, plain, (![B_208]: (r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_208)), B_208) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_6858, c_8208])).
% 7.63/2.77  tff(c_8265, plain, (![B_209]: (r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_209)), B_209))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_8219])).
% 7.63/2.77  tff(c_507, plain, (![A_69, B_70]: (r1_tarski(A_69, k10_relat_1(B_70, k9_relat_1(B_70, A_69))) | ~r1_tarski(A_69, k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.63/2.77  tff(c_513, plain, (![B_70, A_69]: (k10_relat_1(B_70, k9_relat_1(B_70, A_69))=A_69 | ~r1_tarski(k10_relat_1(B_70, k9_relat_1(B_70, A_69)), A_69) | ~r1_tarski(A_69, k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_507, c_2])).
% 7.63/2.77  tff(c_8271, plain, (![B_209]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_209))=B_209 | ~r1_tarski(B_209, k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_8265, c_513])).
% 7.63/2.77  tff(c_8898, plain, (![B_216]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', B_216))=B_216 | ~r1_tarski(B_216, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8271])).
% 7.63/2.77  tff(c_8928, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(resolution, [status(thm)], [c_40, c_8898])).
% 7.63/2.77  tff(c_8948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_8928])).
% 7.63/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.63/2.77  
% 7.63/2.77  Inference rules
% 7.63/2.77  ----------------------
% 7.63/2.77  #Ref     : 0
% 7.63/2.77  #Sup     : 2075
% 7.63/2.77  #Fact    : 0
% 7.63/2.77  #Define  : 0
% 7.63/2.77  #Split   : 4
% 7.63/2.77  #Chain   : 0
% 7.63/2.77  #Close   : 0
% 7.63/2.77  
% 7.63/2.77  Ordering : KBO
% 7.63/2.77  
% 7.63/2.77  Simplification rules
% 7.63/2.77  ----------------------
% 7.63/2.77  #Subsume      : 121
% 7.63/2.77  #Demod        : 3662
% 7.63/2.77  #Tautology    : 973
% 7.63/2.77  #SimpNegUnit  : 1
% 7.63/2.77  #BackRed      : 9
% 7.63/2.77  
% 7.63/2.77  #Partial instantiations: 0
% 7.63/2.77  #Strategies tried      : 1
% 7.63/2.77  
% 7.63/2.77  Timing (in seconds)
% 7.63/2.77  ----------------------
% 7.63/2.78  Preprocessing        : 0.34
% 7.63/2.78  Parsing              : 0.18
% 7.63/2.78  CNF conversion       : 0.02
% 7.63/2.78  Main loop            : 1.67
% 7.63/2.78  Inferencing          : 0.42
% 7.63/2.78  Reduction            : 0.87
% 7.63/2.78  Demodulation         : 0.75
% 7.63/2.78  BG Simplification    : 0.06
% 7.63/2.78  Subsumption          : 0.25
% 7.63/2.78  Abstraction          : 0.08
% 7.63/2.78  MUC search           : 0.00
% 7.63/2.78  Cooper               : 0.00
% 7.63/2.78  Total                : 2.04
% 7.63/2.78  Index Insertion      : 0.00
% 7.63/2.78  Index Deletion       : 0.00
% 7.63/2.78  Index Matching       : 0.00
% 7.63/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
