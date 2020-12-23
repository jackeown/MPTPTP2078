%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:10 EST 2020

% Result     : Theorem 21.33s
% Output     : CNFRefutation 21.51s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 305 expanded)
%              Number of leaves         :   36 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  211 ( 678 expanded)
%              Number of equality atoms :   34 ( 106 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40449,plain,(
    ! [A_633,B_634] :
      ( r1_tarski(A_633,B_634)
      | ~ m1_subset_1(A_633,k1_zfmisc_1(B_634)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40466,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_40449])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40622,plain,(
    ! [A_648,C_649,B_650] :
      ( r1_tarski(k4_xboole_0(A_648,C_649),B_650)
      | ~ r1_tarski(A_648,B_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40719,plain,(
    ! [A_657,B_658,B_659] :
      ( r1_tarski(k3_xboole_0(A_657,B_658),B_659)
      | ~ r1_tarski(A_657,B_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_40622])).

tff(c_40734,plain,(
    ! [B_2,A_1,B_659] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_659)
      | ~ r1_tarski(A_1,B_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_40719])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_41268,plain,(
    ! [A_700,B_701,C_702] :
      ( k9_subset_1(A_700,B_701,C_702) = k3_xboole_0(B_701,C_702)
      | ~ m1_subset_1(C_702,k1_zfmisc_1(A_700)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_41284,plain,(
    ! [B_701] : k9_subset_1(u1_struct_0('#skF_1'),B_701,'#skF_3') = k3_xboole_0(B_701,'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_41268])).

tff(c_50,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_41323,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41284,c_50])).

tff(c_41324,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_41323])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k3_subset_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40669,plain,(
    ! [A_653,B_654] :
      ( k3_subset_1(A_653,k3_subset_1(A_653,B_654)) = B_654
      | ~ m1_subset_1(B_654,k1_zfmisc_1(A_653)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40681,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_40669])).

tff(c_42034,plain,(
    ! [A_737,B_738,C_739] :
      ( r1_tarski(k3_subset_1(A_737,B_738),k3_subset_1(A_737,k9_subset_1(A_737,B_738,C_739)))
      | ~ m1_subset_1(C_739,k1_zfmisc_1(A_737))
      | ~ m1_subset_1(B_738,k1_zfmisc_1(A_737)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42063,plain,(
    ! [C_739] :
      ( r1_tarski('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),k9_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_739)))
      | ~ m1_subset_1(C_739,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40681,c_42034])).

tff(c_43136,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_42063])).

tff(c_43139,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_26,c_43136])).

tff(c_43146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_43139])).

tff(c_43148,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_42063])).

tff(c_42,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_43169,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_43148,c_42])).

tff(c_41283,plain,(
    ! [B_701] : k9_subset_1(u1_struct_0('#skF_1'),B_701,'#skF_2') = k3_xboole_0(B_701,'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_41268])).

tff(c_41082,plain,(
    ! [A_685,B_686,C_687] :
      ( k7_subset_1(A_685,B_686,C_687) = k4_xboole_0(B_686,C_687)
      | ~ m1_subset_1(B_686,k1_zfmisc_1(A_685)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_41098,plain,(
    ! [C_687] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_687) = k4_xboole_0('#skF_3',C_687) ),
    inference(resolution,[status(thm)],[c_54,c_41082])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_41418,plain,(
    ! [A_713,B_714,C_715] :
      ( k9_subset_1(A_713,B_714,k3_subset_1(A_713,C_715)) = k7_subset_1(A_713,B_714,C_715)
      | ~ m1_subset_1(C_715,k1_zfmisc_1(A_713))
      | ~ m1_subset_1(B_714,k1_zfmisc_1(A_713)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_49050,plain,(
    ! [B_867,B_868,A_869] :
      ( k9_subset_1(B_867,B_868,k3_subset_1(B_867,A_869)) = k7_subset_1(B_867,B_868,A_869)
      | ~ m1_subset_1(B_868,k1_zfmisc_1(B_867))
      | ~ r1_tarski(A_869,B_867) ) ),
    inference(resolution,[status(thm)],[c_44,c_41418])).

tff(c_49062,plain,(
    ! [A_869] :
      ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',k3_subset_1(u1_struct_0('#skF_1'),A_869)) = k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',A_869)
      | ~ r1_tarski(A_869,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_54,c_49050])).

tff(c_50593,plain,(
    ! [A_908] :
      ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',k3_subset_1(u1_struct_0('#skF_1'),A_908)) = k4_xboole_0('#skF_3',A_908)
      | ~ r1_tarski(A_908,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41098,c_49062])).

tff(c_50652,plain,
    ( k4_xboole_0('#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40681,c_50593])).

tff(c_50692,plain,(
    k4_xboole_0('#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43169,c_41283,c_50652])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_204,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_221,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_204])).

tff(c_295,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(k4_xboole_0(A_82,C_83),B_84)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_452,plain,(
    ! [A_102,B_103,B_104] :
      ( r1_tarski(k3_xboole_0(A_102,B_103),B_104)
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_295])).

tff(c_467,plain,(
    ! [B_2,A_1,B_104] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_104)
      | ~ r1_tarski(A_1,B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_452])).

tff(c_899,plain,(
    ! [A_133,B_134,C_135] :
      ( k9_subset_1(A_133,B_134,C_135) = k3_xboole_0(B_134,C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_915,plain,(
    ! [B_134] : k9_subset_1(u1_struct_0('#skF_1'),B_134,'#skF_3') = k3_xboole_0(B_134,'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_899])).

tff(c_996,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_50])).

tff(c_997,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_996])).

tff(c_483,plain,(
    ! [A_105,B_106] :
      ( k3_subset_1(A_105,k3_subset_1(A_105,B_106)) = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_499,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_483])).

tff(c_1466,plain,(
    ! [A_166,B_167,C_168] :
      ( r1_tarski(k3_subset_1(A_166,B_167),k3_subset_1(A_166,k9_subset_1(A_166,B_167,C_168)))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1492,plain,(
    ! [C_168] :
      ( r1_tarski('#skF_3',k3_subset_1(u1_struct_0('#skF_1'),k9_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),C_168)))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_1466])).

tff(c_2514,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1492])).

tff(c_2517,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_26,c_2514])).

tff(c_2524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2517])).

tff(c_2526,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1492])).

tff(c_2547,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2526,c_42])).

tff(c_745,plain,(
    ! [A_118,B_119,C_120] :
      ( k7_subset_1(A_118,B_119,C_120) = k4_xboole_0(B_119,C_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_760,plain,(
    ! [C_120] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_120) = k4_xboole_0('#skF_2',C_120) ),
    inference(resolution,[status(thm)],[c_56,c_745])).

tff(c_1089,plain,(
    ! [A_147,B_148,C_149] :
      ( k9_subset_1(A_147,B_148,k3_subset_1(A_147,C_149)) = k7_subset_1(A_147,B_148,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(A_147))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5727,plain,(
    ! [B_282,B_283,A_284] :
      ( k9_subset_1(B_282,B_283,k3_subset_1(B_282,A_284)) = k7_subset_1(B_282,B_283,A_284)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(B_282))
      | ~ r1_tarski(A_284,B_282) ) ),
    inference(resolution,[status(thm)],[c_44,c_1089])).

tff(c_5737,plain,(
    ! [A_284] :
      ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),A_284)) = k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_284)
      | ~ r1_tarski(A_284,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_56,c_5727])).

tff(c_8579,plain,(
    ! [A_331] :
      ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),A_331)) = k4_xboole_0('#skF_2',A_331)
      | ~ r1_tarski(A_331,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_5737])).

tff(c_8634,plain,
    ( k4_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_8579])).

tff(c_8661,plain,(
    k4_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2547,c_2,c_915,c_8634])).

tff(c_52,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_193,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k4_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2226,plain,(
    ! [C_188,A_189,B_190] :
      ( v2_tex_2(C_188,A_189)
      | ~ v2_tex_2(B_190,A_189)
      | ~ r1_tarski(C_188,B_190)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7109,plain,(
    ! [A_313,C_314,A_315,B_316] :
      ( v2_tex_2(k4_xboole_0(A_313,C_314),A_315)
      | ~ v2_tex_2(B_316,A_315)
      | ~ m1_subset_1(k4_xboole_0(A_313,C_314),k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315)
      | ~ r1_tarski(A_313,B_316) ) ),
    inference(resolution,[status(thm)],[c_12,c_2226])).

tff(c_39165,plain,(
    ! [A_617,C_618,A_619,B_620] :
      ( v2_tex_2(k4_xboole_0(A_617,C_618),A_619)
      | ~ v2_tex_2(B_620,A_619)
      | ~ m1_subset_1(B_620,k1_zfmisc_1(u1_struct_0(A_619)))
      | ~ l1_pre_topc(A_619)
      | ~ r1_tarski(A_617,B_620)
      | ~ r1_tarski(k4_xboole_0(A_617,C_618),u1_struct_0(A_619)) ) ),
    inference(resolution,[status(thm)],[c_44,c_7109])).

tff(c_39177,plain,(
    ! [A_617,C_618] :
      ( v2_tex_2(k4_xboole_0(A_617,C_618),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_617,'#skF_2')
      | ~ r1_tarski(k4_xboole_0(A_617,C_618),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_56,c_39165])).

tff(c_40153,plain,(
    ! [A_627,C_628] :
      ( v2_tex_2(k4_xboole_0(A_627,C_628),'#skF_1')
      | ~ r1_tarski(A_627,'#skF_2')
      | ~ r1_tarski(k4_xboole_0(A_627,C_628),u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_193,c_39177])).

tff(c_40256,plain,
    ( v2_tex_2(k4_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')),'#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8661,c_40153])).

tff(c_40375,plain,
    ( v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8661,c_40256])).

tff(c_40376,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_997,c_40375])).

tff(c_40427,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_467,c_40376])).

tff(c_40436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_40427])).

tff(c_40437,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_42583,plain,(
    ! [C_754,A_755,B_756] :
      ( v2_tex_2(C_754,A_755)
      | ~ v2_tex_2(B_756,A_755)
      | ~ r1_tarski(C_754,B_756)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(u1_struct_0(A_755)))
      | ~ m1_subset_1(B_756,k1_zfmisc_1(u1_struct_0(A_755)))
      | ~ l1_pre_topc(A_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50359,plain,(
    ! [A_900,C_901,A_902,B_903] :
      ( v2_tex_2(k4_xboole_0(A_900,C_901),A_902)
      | ~ v2_tex_2(B_903,A_902)
      | ~ m1_subset_1(k4_xboole_0(A_900,C_901),k1_zfmisc_1(u1_struct_0(A_902)))
      | ~ m1_subset_1(B_903,k1_zfmisc_1(u1_struct_0(A_902)))
      | ~ l1_pre_topc(A_902)
      | ~ r1_tarski(A_900,B_903) ) ),
    inference(resolution,[status(thm)],[c_12,c_42583])).

tff(c_89370,plain,(
    ! [A_1224,C_1225,A_1226,B_1227] :
      ( v2_tex_2(k4_xboole_0(A_1224,C_1225),A_1226)
      | ~ v2_tex_2(B_1227,A_1226)
      | ~ m1_subset_1(B_1227,k1_zfmisc_1(u1_struct_0(A_1226)))
      | ~ l1_pre_topc(A_1226)
      | ~ r1_tarski(A_1224,B_1227)
      | ~ r1_tarski(k4_xboole_0(A_1224,C_1225),u1_struct_0(A_1226)) ) ),
    inference(resolution,[status(thm)],[c_44,c_50359])).

tff(c_89384,plain,(
    ! [A_1224,C_1225] :
      ( v2_tex_2(k4_xboole_0(A_1224,C_1225),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_1224,'#skF_3')
      | ~ r1_tarski(k4_xboole_0(A_1224,C_1225),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_54,c_89370])).

tff(c_89410,plain,(
    ! [A_1228,C_1229] :
      ( v2_tex_2(k4_xboole_0(A_1228,C_1229),'#skF_1')
      | ~ r1_tarski(A_1228,'#skF_3')
      | ~ r1_tarski(k4_xboole_0(A_1228,C_1229),u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_40437,c_89384])).

tff(c_89488,plain,
    ( v2_tex_2(k4_xboole_0('#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50692,c_89410])).

tff(c_89566,plain,
    ( v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_50692,c_89488])).

tff(c_89567,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_41324,c_89566])).

tff(c_89592,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40734,c_89567])).

tff(c_89601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40466,c_89592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.33/12.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.33/12.96  
% 21.33/12.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.33/12.96  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 21.33/12.96  
% 21.33/12.96  %Foreground sorts:
% 21.33/12.96  
% 21.33/12.96  
% 21.33/12.96  %Background operators:
% 21.33/12.96  
% 21.33/12.96  
% 21.33/12.96  %Foreground operators:
% 21.33/12.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.33/12.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.33/12.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.33/12.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.33/12.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.33/12.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.33/12.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.33/12.96  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 21.33/12.96  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 21.33/12.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 21.33/12.96  tff('#skF_2', type, '#skF_2': $i).
% 21.33/12.96  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 21.33/12.96  tff('#skF_3', type, '#skF_3': $i).
% 21.33/12.96  tff('#skF_1', type, '#skF_1': $i).
% 21.33/12.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.33/12.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.33/12.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.33/12.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.33/12.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.33/12.96  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 21.33/12.96  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.33/12.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.33/12.96  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.33/12.96  
% 21.51/12.98  tff(f_124, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 21.51/12.98  tff(f_89, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.51/12.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 21.51/12.98  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.51/12.98  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 21.51/12.98  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 21.51/12.98  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.51/12.98  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 21.51/12.98  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 21.51/12.98  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 21.51/12.98  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 21.51/12.98  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 21.51/12.98  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 21.51/12.98  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.51/12.98  tff(c_40449, plain, (![A_633, B_634]: (r1_tarski(A_633, B_634) | ~m1_subset_1(A_633, k1_zfmisc_1(B_634)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.51/12.98  tff(c_40466, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_40449])).
% 21.51/12.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.51/12.98  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.51/12.98  tff(c_40622, plain, (![A_648, C_649, B_650]: (r1_tarski(k4_xboole_0(A_648, C_649), B_650) | ~r1_tarski(A_648, B_650))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.51/12.98  tff(c_40719, plain, (![A_657, B_658, B_659]: (r1_tarski(k3_xboole_0(A_657, B_658), B_659) | ~r1_tarski(A_657, B_659))), inference(superposition, [status(thm), theory('equality')], [c_18, c_40622])).
% 21.51/12.98  tff(c_40734, plain, (![B_2, A_1, B_659]: (r1_tarski(k3_xboole_0(B_2, A_1), B_659) | ~r1_tarski(A_1, B_659))), inference(superposition, [status(thm), theory('equality')], [c_2, c_40719])).
% 21.51/12.98  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.51/12.98  tff(c_41268, plain, (![A_700, B_701, C_702]: (k9_subset_1(A_700, B_701, C_702)=k3_xboole_0(B_701, C_702) | ~m1_subset_1(C_702, k1_zfmisc_1(A_700)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 21.51/12.98  tff(c_41284, plain, (![B_701]: (k9_subset_1(u1_struct_0('#skF_1'), B_701, '#skF_3')=k3_xboole_0(B_701, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_41268])).
% 21.51/12.98  tff(c_50, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.51/12.98  tff(c_41323, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41284, c_50])).
% 21.51/12.98  tff(c_41324, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_41323])).
% 21.51/12.98  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.51/12.98  tff(c_26, plain, (![A_19, B_20]: (m1_subset_1(k3_subset_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.51/12.98  tff(c_40669, plain, (![A_653, B_654]: (k3_subset_1(A_653, k3_subset_1(A_653, B_654))=B_654 | ~m1_subset_1(B_654, k1_zfmisc_1(A_653)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.51/12.98  tff(c_40681, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_56, c_40669])).
% 21.51/12.98  tff(c_42034, plain, (![A_737, B_738, C_739]: (r1_tarski(k3_subset_1(A_737, B_738), k3_subset_1(A_737, k9_subset_1(A_737, B_738, C_739))) | ~m1_subset_1(C_739, k1_zfmisc_1(A_737)) | ~m1_subset_1(B_738, k1_zfmisc_1(A_737)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.51/12.98  tff(c_42063, plain, (![C_739]: (r1_tarski('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), k9_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_739))) | ~m1_subset_1(C_739, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_40681, c_42034])).
% 21.51/12.98  tff(c_43136, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_42063])).
% 21.51/12.98  tff(c_43139, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_43136])).
% 21.51/12.98  tff(c_43146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_43139])).
% 21.51/12.98  tff(c_43148, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_42063])).
% 21.51/12.98  tff(c_42, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.51/12.98  tff(c_43169, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_43148, c_42])).
% 21.51/12.98  tff(c_41283, plain, (![B_701]: (k9_subset_1(u1_struct_0('#skF_1'), B_701, '#skF_2')=k3_xboole_0(B_701, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_41268])).
% 21.51/12.98  tff(c_41082, plain, (![A_685, B_686, C_687]: (k7_subset_1(A_685, B_686, C_687)=k4_xboole_0(B_686, C_687) | ~m1_subset_1(B_686, k1_zfmisc_1(A_685)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 21.51/12.98  tff(c_41098, plain, (![C_687]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_687)=k4_xboole_0('#skF_3', C_687))), inference(resolution, [status(thm)], [c_54, c_41082])).
% 21.51/12.98  tff(c_44, plain, (![A_40, B_41]: (m1_subset_1(A_40, k1_zfmisc_1(B_41)) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.51/12.98  tff(c_41418, plain, (![A_713, B_714, C_715]: (k9_subset_1(A_713, B_714, k3_subset_1(A_713, C_715))=k7_subset_1(A_713, B_714, C_715) | ~m1_subset_1(C_715, k1_zfmisc_1(A_713)) | ~m1_subset_1(B_714, k1_zfmisc_1(A_713)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 21.51/12.98  tff(c_49050, plain, (![B_867, B_868, A_869]: (k9_subset_1(B_867, B_868, k3_subset_1(B_867, A_869))=k7_subset_1(B_867, B_868, A_869) | ~m1_subset_1(B_868, k1_zfmisc_1(B_867)) | ~r1_tarski(A_869, B_867))), inference(resolution, [status(thm)], [c_44, c_41418])).
% 21.51/12.98  tff(c_49062, plain, (![A_869]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', k3_subset_1(u1_struct_0('#skF_1'), A_869))=k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', A_869) | ~r1_tarski(A_869, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_49050])).
% 21.51/12.98  tff(c_50593, plain, (![A_908]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', k3_subset_1(u1_struct_0('#skF_1'), A_908))=k4_xboole_0('#skF_3', A_908) | ~r1_tarski(A_908, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41098, c_49062])).
% 21.51/12.98  tff(c_50652, plain, (k4_xboole_0('#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40681, c_50593])).
% 21.51/12.98  tff(c_50692, plain, (k4_xboole_0('#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_43169, c_41283, c_50652])).
% 21.51/12.98  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.51/12.98  tff(c_204, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.51/12.98  tff(c_221, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_204])).
% 21.51/12.98  tff(c_295, plain, (![A_82, C_83, B_84]: (r1_tarski(k4_xboole_0(A_82, C_83), B_84) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.51/12.98  tff(c_452, plain, (![A_102, B_103, B_104]: (r1_tarski(k3_xboole_0(A_102, B_103), B_104) | ~r1_tarski(A_102, B_104))), inference(superposition, [status(thm), theory('equality')], [c_18, c_295])).
% 21.51/12.98  tff(c_467, plain, (![B_2, A_1, B_104]: (r1_tarski(k3_xboole_0(B_2, A_1), B_104) | ~r1_tarski(A_1, B_104))), inference(superposition, [status(thm), theory('equality')], [c_2, c_452])).
% 21.51/12.98  tff(c_899, plain, (![A_133, B_134, C_135]: (k9_subset_1(A_133, B_134, C_135)=k3_xboole_0(B_134, C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 21.51/12.98  tff(c_915, plain, (![B_134]: (k9_subset_1(u1_struct_0('#skF_1'), B_134, '#skF_3')=k3_xboole_0(B_134, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_899])).
% 21.51/12.98  tff(c_996, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_915, c_50])).
% 21.51/12.98  tff(c_997, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_996])).
% 21.51/12.98  tff(c_483, plain, (![A_105, B_106]: (k3_subset_1(A_105, k3_subset_1(A_105, B_106))=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.51/12.98  tff(c_499, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_54, c_483])).
% 21.51/12.98  tff(c_1466, plain, (![A_166, B_167, C_168]: (r1_tarski(k3_subset_1(A_166, B_167), k3_subset_1(A_166, k9_subset_1(A_166, B_167, C_168))) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.51/12.98  tff(c_1492, plain, (![C_168]: (r1_tarski('#skF_3', k3_subset_1(u1_struct_0('#skF_1'), k9_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), C_168))) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_499, c_1466])).
% 21.51/12.98  tff(c_2514, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1492])).
% 21.51/12.98  tff(c_2517, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_2514])).
% 21.51/12.98  tff(c_2524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_2517])).
% 21.51/12.98  tff(c_2526, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1492])).
% 21.51/12.98  tff(c_2547, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2526, c_42])).
% 21.51/12.98  tff(c_745, plain, (![A_118, B_119, C_120]: (k7_subset_1(A_118, B_119, C_120)=k4_xboole_0(B_119, C_120) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 21.51/12.98  tff(c_760, plain, (![C_120]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_120)=k4_xboole_0('#skF_2', C_120))), inference(resolution, [status(thm)], [c_56, c_745])).
% 21.51/12.98  tff(c_1089, plain, (![A_147, B_148, C_149]: (k9_subset_1(A_147, B_148, k3_subset_1(A_147, C_149))=k7_subset_1(A_147, B_148, C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(A_147)) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 21.51/12.98  tff(c_5727, plain, (![B_282, B_283, A_284]: (k9_subset_1(B_282, B_283, k3_subset_1(B_282, A_284))=k7_subset_1(B_282, B_283, A_284) | ~m1_subset_1(B_283, k1_zfmisc_1(B_282)) | ~r1_tarski(A_284, B_282))), inference(resolution, [status(thm)], [c_44, c_1089])).
% 21.51/12.98  tff(c_5737, plain, (![A_284]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), A_284))=k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_284) | ~r1_tarski(A_284, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_56, c_5727])).
% 21.51/12.98  tff(c_8579, plain, (![A_331]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), A_331))=k4_xboole_0('#skF_2', A_331) | ~r1_tarski(A_331, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_760, c_5737])).
% 21.51/12.98  tff(c_8634, plain, (k4_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_499, c_8579])).
% 21.51/12.98  tff(c_8661, plain, (k4_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2547, c_2, c_915, c_8634])).
% 21.51/12.98  tff(c_52, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.51/12.98  tff(c_193, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 21.51/12.98  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(k4_xboole_0(A_7, C_9), B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.51/12.98  tff(c_2226, plain, (![C_188, A_189, B_190]: (v2_tex_2(C_188, A_189) | ~v2_tex_2(B_190, A_189) | ~r1_tarski(C_188, B_190) | ~m1_subset_1(C_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.51/12.98  tff(c_7109, plain, (![A_313, C_314, A_315, B_316]: (v2_tex_2(k4_xboole_0(A_313, C_314), A_315) | ~v2_tex_2(B_316, A_315) | ~m1_subset_1(k4_xboole_0(A_313, C_314), k1_zfmisc_1(u1_struct_0(A_315))) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315) | ~r1_tarski(A_313, B_316))), inference(resolution, [status(thm)], [c_12, c_2226])).
% 21.51/12.98  tff(c_39165, plain, (![A_617, C_618, A_619, B_620]: (v2_tex_2(k4_xboole_0(A_617, C_618), A_619) | ~v2_tex_2(B_620, A_619) | ~m1_subset_1(B_620, k1_zfmisc_1(u1_struct_0(A_619))) | ~l1_pre_topc(A_619) | ~r1_tarski(A_617, B_620) | ~r1_tarski(k4_xboole_0(A_617, C_618), u1_struct_0(A_619)))), inference(resolution, [status(thm)], [c_44, c_7109])).
% 21.51/12.98  tff(c_39177, plain, (![A_617, C_618]: (v2_tex_2(k4_xboole_0(A_617, C_618), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_617, '#skF_2') | ~r1_tarski(k4_xboole_0(A_617, C_618), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_56, c_39165])).
% 21.51/12.98  tff(c_40153, plain, (![A_627, C_628]: (v2_tex_2(k4_xboole_0(A_627, C_628), '#skF_1') | ~r1_tarski(A_627, '#skF_2') | ~r1_tarski(k4_xboole_0(A_627, C_628), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_193, c_39177])).
% 21.51/12.98  tff(c_40256, plain, (v2_tex_2(k4_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8661, c_40153])).
% 21.51/12.98  tff(c_40375, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8661, c_40256])).
% 21.51/12.98  tff(c_40376, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_997, c_40375])).
% 21.51/12.98  tff(c_40427, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_467, c_40376])).
% 21.51/12.98  tff(c_40436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_40427])).
% 21.51/12.98  tff(c_40437, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 21.51/12.98  tff(c_42583, plain, (![C_754, A_755, B_756]: (v2_tex_2(C_754, A_755) | ~v2_tex_2(B_756, A_755) | ~r1_tarski(C_754, B_756) | ~m1_subset_1(C_754, k1_zfmisc_1(u1_struct_0(A_755))) | ~m1_subset_1(B_756, k1_zfmisc_1(u1_struct_0(A_755))) | ~l1_pre_topc(A_755))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.51/12.98  tff(c_50359, plain, (![A_900, C_901, A_902, B_903]: (v2_tex_2(k4_xboole_0(A_900, C_901), A_902) | ~v2_tex_2(B_903, A_902) | ~m1_subset_1(k4_xboole_0(A_900, C_901), k1_zfmisc_1(u1_struct_0(A_902))) | ~m1_subset_1(B_903, k1_zfmisc_1(u1_struct_0(A_902))) | ~l1_pre_topc(A_902) | ~r1_tarski(A_900, B_903))), inference(resolution, [status(thm)], [c_12, c_42583])).
% 21.51/12.98  tff(c_89370, plain, (![A_1224, C_1225, A_1226, B_1227]: (v2_tex_2(k4_xboole_0(A_1224, C_1225), A_1226) | ~v2_tex_2(B_1227, A_1226) | ~m1_subset_1(B_1227, k1_zfmisc_1(u1_struct_0(A_1226))) | ~l1_pre_topc(A_1226) | ~r1_tarski(A_1224, B_1227) | ~r1_tarski(k4_xboole_0(A_1224, C_1225), u1_struct_0(A_1226)))), inference(resolution, [status(thm)], [c_44, c_50359])).
% 21.51/12.98  tff(c_89384, plain, (![A_1224, C_1225]: (v2_tex_2(k4_xboole_0(A_1224, C_1225), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_1224, '#skF_3') | ~r1_tarski(k4_xboole_0(A_1224, C_1225), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_89370])).
% 21.51/12.98  tff(c_89410, plain, (![A_1228, C_1229]: (v2_tex_2(k4_xboole_0(A_1228, C_1229), '#skF_1') | ~r1_tarski(A_1228, '#skF_3') | ~r1_tarski(k4_xboole_0(A_1228, C_1229), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_40437, c_89384])).
% 21.51/12.98  tff(c_89488, plain, (v2_tex_2(k4_xboole_0('#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50692, c_89410])).
% 21.51/12.98  tff(c_89566, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_50692, c_89488])).
% 21.51/12.98  tff(c_89567, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_41324, c_89566])).
% 21.51/12.98  tff(c_89592, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40734, c_89567])).
% 21.51/12.98  tff(c_89601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40466, c_89592])).
% 21.51/12.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.51/12.98  
% 21.51/12.98  Inference rules
% 21.51/12.98  ----------------------
% 21.51/12.98  #Ref     : 0
% 21.51/12.98  #Sup     : 22600
% 21.51/12.98  #Fact    : 0
% 21.51/12.98  #Define  : 0
% 21.51/12.98  #Split   : 22
% 21.51/12.98  #Chain   : 0
% 21.51/12.98  #Close   : 0
% 21.51/12.98  
% 21.51/12.98  Ordering : KBO
% 21.51/12.98  
% 21.51/12.98  Simplification rules
% 21.51/12.98  ----------------------
% 21.51/12.98  #Subsume      : 5421
% 21.51/12.98  #Demod        : 22960
% 21.51/12.98  #Tautology    : 10149
% 21.51/12.98  #SimpNegUnit  : 9
% 21.51/12.98  #BackRed      : 152
% 21.51/12.98  
% 21.51/12.98  #Partial instantiations: 0
% 21.51/12.98  #Strategies tried      : 1
% 21.51/12.98  
% 21.51/12.98  Timing (in seconds)
% 21.51/12.98  ----------------------
% 21.51/12.99  Preprocessing        : 0.33
% 21.51/12.99  Parsing              : 0.18
% 21.51/12.99  CNF conversion       : 0.02
% 21.51/12.99  Main loop            : 11.88
% 21.51/12.99  Inferencing          : 1.80
% 21.51/12.99  Reduction            : 6.52
% 21.51/12.99  Demodulation         : 5.74
% 21.51/12.99  BG Simplification    : 0.19
% 21.51/12.99  Subsumption          : 2.84
% 21.51/12.99  Abstraction          : 0.35
% 21.51/12.99  MUC search           : 0.00
% 21.51/12.99  Cooper               : 0.00
% 21.51/12.99  Total                : 12.25
% 21.51/12.99  Index Insertion      : 0.00
% 21.51/12.99  Index Deletion       : 0.00
% 21.51/12.99  Index Matching       : 0.00
% 21.51/12.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
