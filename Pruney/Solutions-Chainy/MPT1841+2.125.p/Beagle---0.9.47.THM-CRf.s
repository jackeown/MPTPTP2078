%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:44 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 209 expanded)
%              Number of leaves         :   54 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 358 expanded)
%              Number of equality atoms :   47 (  76 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_114,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_77,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( ~ v1_xboole_0(k3_xboole_0(A,B))
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_79,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_118,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_struct_0)).

tff(c_60,plain,(
    ! [A_41] : l1_orders_2(k2_yellow_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    ! [A_38] :
      ( l1_struct_0(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,(
    ! [A_55,B_56] : k2_xboole_0(k1_tarski(A_55),B_56) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_112,plain,(
    ! [A_55] : k1_tarski(A_55) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_108])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_72,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_632,plain,(
    ! [A_127,B_128] :
      ( k6_domain_1(A_127,B_128) = k1_tarski(B_128)
      | ~ m1_subset_1(B_128,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_638,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_632])).

tff(c_642,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_638])).

tff(c_648,plain,(
    ! [A_129,B_130] :
      ( m1_subset_1(k6_domain_1(A_129,B_130),k1_zfmisc_1(A_129))
      | ~ m1_subset_1(B_130,A_129)
      | v1_xboole_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_657,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_648])).

tff(c_661,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_657])).

tff(c_662,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_661])).

tff(c_44,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_670,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_662,c_44])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_547,plain,(
    ! [B_110,A_111] :
      ( ~ r1_xboole_0(B_110,A_111)
      | ~ r1_tarski(B_110,A_111)
      | v1_xboole_0(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_551,plain,(
    ! [A_19,B_20] :
      ( ~ r1_tarski(A_19,B_20)
      | v1_xboole_0(A_19)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(resolution,[status(thm)],[c_30,c_547])).

tff(c_683,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_670,c_551])).

tff(c_691,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_24,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_692,plain,(
    ! [A_131,B_132] :
      ( r1_tarski(A_131,B_132)
      | v1_xboole_0(k3_xboole_0(A_131,B_132))
      | ~ v1_zfmisc_1(A_131)
      | v1_xboole_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_732,plain,(
    ! [A_135,B_136] :
      ( k3_xboole_0(A_135,B_136) = k1_xboole_0
      | r1_tarski(A_135,B_136)
      | ~ v1_zfmisc_1(A_135)
      | v1_xboole_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_692,c_12])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_685,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_670,c_14])).

tff(c_686,plain,(
    ~ r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_735,plain,
    ( k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_732,c_686])).

tff(c_749,plain,
    ( k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_735])).

tff(c_750,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_749])).

tff(c_32,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_262,plain,(
    ! [A_84,B_85] : k1_setfam_1(k2_tarski(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_463,plain,(
    ! [B_102,A_103] : k1_setfam_1(k2_tarski(B_102,A_103)) = k3_xboole_0(A_103,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_262])).

tff(c_42,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_496,plain,(
    ! [B_106,A_107] : k3_xboole_0(B_106,A_107) = k3_xboole_0(A_107,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_42])).

tff(c_20,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_514,plain,(
    ! [B_106,A_107] : k5_xboole_0(B_106,k3_xboole_0(A_107,B_106)) = k4_xboole_0(B_106,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_20])).

tff(c_761,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_514])).

tff(c_770,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_761])).

tff(c_772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_770])).

tff(c_773,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_787,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_773,c_12])).

tff(c_792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_787])).

tff(c_793,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_70,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_643,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_70])).

tff(c_797,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_643])).

tff(c_62,plain,(
    ! [A_42] : u1_struct_0(k2_yellow_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_133,plain,(
    ! [A_62] :
      ( u1_struct_0(A_62) = k2_struct_0(A_62)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_176,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_orders_2(A_66) ) ),
    inference(resolution,[status(thm)],[c_54,c_133])).

tff(c_179,plain,(
    ! [A_41] : u1_struct_0(k2_yellow_1(A_41)) = k2_struct_0(k2_yellow_1(A_41)) ),
    inference(resolution,[status(thm)],[c_60,c_176])).

tff(c_181,plain,(
    ! [A_41] : k2_struct_0(k2_yellow_1(A_41)) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_179])).

tff(c_201,plain,(
    ! [A_72] :
      ( ~ v1_subset_1(k2_struct_0(A_72),u1_struct_0(A_72))
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_207,plain,(
    ! [A_42] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_42)),A_42)
      | ~ l1_struct_0(k2_yellow_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_201])).

tff(c_209,plain,(
    ! [A_42] :
      ( ~ v1_subset_1(A_42,A_42)
      | ~ l1_struct_0(k2_yellow_1(A_42)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_207])).

tff(c_824,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_797,c_209])).

tff(c_845,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_824])).

tff(c_849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:45:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.51  
% 3.04/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.51  %$ v1_subset_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.04/1.51  
% 3.04/1.51  %Foreground sorts:
% 3.04/1.51  
% 3.04/1.51  
% 3.04/1.51  %Background operators:
% 3.04/1.51  
% 3.04/1.51  
% 3.04/1.51  %Foreground operators:
% 3.04/1.51  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.04/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.51  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.04/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.04/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.04/1.51  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.04/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.51  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.04/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.51  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.04/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.04/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.04/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.04/1.51  
% 3.20/1.53  tff(f_114, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.20/1.53  tff(f_103, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.20/1.53  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.20/1.53  tff(f_77, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.20/1.53  tff(f_141, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.20/1.53  tff(f_110, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.20/1.53  tff(f_99, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.20/1.53  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.20/1.53  tff(f_66, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.20/1.53  tff(f_62, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.20/1.53  tff(f_54, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.20/1.53  tff(f_129, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 3.20/1.53  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.20/1.53  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.53  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.20/1.53  tff(f_79, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.20/1.53  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.20/1.53  tff(f_118, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.20/1.53  tff(f_87, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.20/1.53  tff(f_92, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc12_struct_0)).
% 3.20/1.53  tff(c_60, plain, (![A_41]: (l1_orders_2(k2_yellow_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.20/1.53  tff(c_54, plain, (![A_38]: (l1_struct_0(A_38) | ~l1_orders_2(A_38))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.20/1.53  tff(c_22, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.20/1.53  tff(c_108, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.53  tff(c_112, plain, (![A_55]: (k1_tarski(A_55)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_108])).
% 3.20/1.53  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.20/1.53  tff(c_72, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.20/1.53  tff(c_632, plain, (![A_127, B_128]: (k6_domain_1(A_127, B_128)=k1_tarski(B_128) | ~m1_subset_1(B_128, A_127) | v1_xboole_0(A_127))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.20/1.53  tff(c_638, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_632])).
% 3.20/1.53  tff(c_642, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_638])).
% 3.20/1.53  tff(c_648, plain, (![A_129, B_130]: (m1_subset_1(k6_domain_1(A_129, B_130), k1_zfmisc_1(A_129)) | ~m1_subset_1(B_130, A_129) | v1_xboole_0(A_129))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.20/1.53  tff(c_657, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_642, c_648])).
% 3.20/1.53  tff(c_661, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_657])).
% 3.20/1.53  tff(c_662, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_661])).
% 3.20/1.53  tff(c_44, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.20/1.53  tff(c_670, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_662, c_44])).
% 3.20/1.53  tff(c_30, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.20/1.53  tff(c_547, plain, (![B_110, A_111]: (~r1_xboole_0(B_110, A_111) | ~r1_tarski(B_110, A_111) | v1_xboole_0(B_110))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.53  tff(c_551, plain, (![A_19, B_20]: (~r1_tarski(A_19, B_20) | v1_xboole_0(A_19) | k4_xboole_0(A_19, B_20)!=A_19)), inference(resolution, [status(thm)], [c_30, c_547])).
% 3.20/1.53  tff(c_683, plain, (v1_xboole_0(k1_tarski('#skF_4')) | k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_670, c_551])).
% 3.20/1.53  tff(c_691, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_683])).
% 3.20/1.53  tff(c_24, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.53  tff(c_68, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.20/1.53  tff(c_692, plain, (![A_131, B_132]: (r1_tarski(A_131, B_132) | v1_xboole_0(k3_xboole_0(A_131, B_132)) | ~v1_zfmisc_1(A_131) | v1_xboole_0(A_131))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.20/1.53  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.53  tff(c_732, plain, (![A_135, B_136]: (k3_xboole_0(A_135, B_136)=k1_xboole_0 | r1_tarski(A_135, B_136) | ~v1_zfmisc_1(A_135) | v1_xboole_0(A_135))), inference(resolution, [status(thm)], [c_692, c_12])).
% 3.20/1.53  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.20/1.53  tff(c_685, plain, (k1_tarski('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_670, c_14])).
% 3.20/1.53  tff(c_686, plain, (~r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_685])).
% 3.20/1.53  tff(c_735, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_732, c_686])).
% 3.20/1.53  tff(c_749, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_735])).
% 3.20/1.53  tff(c_750, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_749])).
% 3.20/1.53  tff(c_32, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.53  tff(c_262, plain, (![A_84, B_85]: (k1_setfam_1(k2_tarski(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.53  tff(c_463, plain, (![B_102, A_103]: (k1_setfam_1(k2_tarski(B_102, A_103))=k3_xboole_0(A_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_32, c_262])).
% 3.20/1.53  tff(c_42, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.53  tff(c_496, plain, (![B_106, A_107]: (k3_xboole_0(B_106, A_107)=k3_xboole_0(A_107, B_106))), inference(superposition, [status(thm), theory('equality')], [c_463, c_42])).
% 3.20/1.53  tff(c_20, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.20/1.53  tff(c_514, plain, (![B_106, A_107]: (k5_xboole_0(B_106, k3_xboole_0(A_107, B_106))=k4_xboole_0(B_106, A_107))), inference(superposition, [status(thm), theory('equality')], [c_496, c_20])).
% 3.20/1.53  tff(c_761, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_750, c_514])).
% 3.20/1.53  tff(c_770, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_761])).
% 3.20/1.53  tff(c_772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_691, c_770])).
% 3.20/1.53  tff(c_773, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_683])).
% 3.20/1.53  tff(c_787, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_773, c_12])).
% 3.20/1.53  tff(c_792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_787])).
% 3.20/1.53  tff(c_793, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_685])).
% 3.20/1.53  tff(c_70, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.20/1.53  tff(c_643, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_70])).
% 3.20/1.53  tff(c_797, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_793, c_643])).
% 3.20/1.53  tff(c_62, plain, (![A_42]: (u1_struct_0(k2_yellow_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.20/1.53  tff(c_133, plain, (![A_62]: (u1_struct_0(A_62)=k2_struct_0(A_62) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.20/1.53  tff(c_176, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_orders_2(A_66))), inference(resolution, [status(thm)], [c_54, c_133])).
% 3.20/1.53  tff(c_179, plain, (![A_41]: (u1_struct_0(k2_yellow_1(A_41))=k2_struct_0(k2_yellow_1(A_41)))), inference(resolution, [status(thm)], [c_60, c_176])).
% 3.20/1.53  tff(c_181, plain, (![A_41]: (k2_struct_0(k2_yellow_1(A_41))=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_179])).
% 3.20/1.53  tff(c_201, plain, (![A_72]: (~v1_subset_1(k2_struct_0(A_72), u1_struct_0(A_72)) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.20/1.53  tff(c_207, plain, (![A_42]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_42)), A_42) | ~l1_struct_0(k2_yellow_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_201])).
% 3.20/1.53  tff(c_209, plain, (![A_42]: (~v1_subset_1(A_42, A_42) | ~l1_struct_0(k2_yellow_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_207])).
% 3.20/1.53  tff(c_824, plain, (~l1_struct_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_797, c_209])).
% 3.20/1.53  tff(c_845, plain, (~l1_orders_2(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_824])).
% 3.20/1.53  tff(c_849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_845])).
% 3.20/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.53  
% 3.20/1.53  Inference rules
% 3.20/1.53  ----------------------
% 3.20/1.53  #Ref     : 0
% 3.20/1.53  #Sup     : 181
% 3.20/1.53  #Fact    : 0
% 3.20/1.53  #Define  : 0
% 3.20/1.53  #Split   : 3
% 3.20/1.53  #Chain   : 0
% 3.20/1.53  #Close   : 0
% 3.20/1.53  
% 3.20/1.53  Ordering : KBO
% 3.20/1.53  
% 3.20/1.53  Simplification rules
% 3.20/1.53  ----------------------
% 3.20/1.53  #Subsume      : 13
% 3.20/1.53  #Demod        : 40
% 3.20/1.53  #Tautology    : 105
% 3.20/1.53  #SimpNegUnit  : 7
% 3.20/1.53  #BackRed      : 5
% 3.20/1.53  
% 3.20/1.53  #Partial instantiations: 0
% 3.20/1.53  #Strategies tried      : 1
% 3.20/1.53  
% 3.20/1.53  Timing (in seconds)
% 3.20/1.53  ----------------------
% 3.20/1.54  Preprocessing        : 0.35
% 3.20/1.54  Parsing              : 0.19
% 3.20/1.54  CNF conversion       : 0.02
% 3.20/1.54  Main loop            : 0.33
% 3.20/1.54  Inferencing          : 0.12
% 3.20/1.54  Reduction            : 0.11
% 3.24/1.54  Demodulation         : 0.08
% 3.24/1.54  BG Simplification    : 0.02
% 3.24/1.54  Subsumption          : 0.06
% 3.24/1.54  Abstraction          : 0.02
% 3.24/1.54  MUC search           : 0.00
% 3.24/1.54  Cooper               : 0.00
% 3.24/1.54  Total                : 0.72
% 3.24/1.54  Index Insertion      : 0.00
% 3.24/1.54  Index Deletion       : 0.00
% 3.24/1.54  Index Matching       : 0.00
% 3.24/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
