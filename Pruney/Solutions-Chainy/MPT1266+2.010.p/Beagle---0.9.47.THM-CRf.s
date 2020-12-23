%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:44 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  143 (1187 expanded)
%              Number of leaves         :   33 ( 408 expanded)
%              Depth                    :   17
%              Number of atoms          :  268 (2577 expanded)
%              Number of equality atoms :   68 ( 688 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_48,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_76,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_82,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_42])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_61,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_70,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_71,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_38])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_261,plain,(
    ! [B_56,A_57] :
      ( v1_tops_1(B_56,A_57)
      | k2_pre_topc(A_57,B_56) != k2_struct_0(A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_274,plain,(
    ! [B_56] :
      ( v1_tops_1(B_56,'#skF_1')
      | k2_pre_topc('#skF_1',B_56) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_261])).

tff(c_280,plain,(
    ! [B_58] :
      ( v1_tops_1(B_58,'#skF_1')
      | k2_pre_topc('#skF_1',B_58) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_274])).

tff(c_305,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_280])).

tff(c_306,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_343,plain,(
    ! [A_61,B_62] :
      ( k2_pre_topc(A_61,B_62) = k2_struct_0(A_61)
      | ~ v1_tops_1(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_356,plain,(
    ! [B_62] :
      ( k2_pre_topc('#skF_1',B_62) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_62,'#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_343])).

tff(c_362,plain,(
    ! [B_63] :
      ( k2_pre_topc('#skF_1',B_63) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_63,'#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_356])).

tff(c_381,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_362])).

tff(c_393,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_381])).

tff(c_133,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_71,c_133])).

tff(c_443,plain,(
    ! [A_66,B_67] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_66),B_67),A_66)
      | ~ v2_tops_1(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_450,plain,(
    ! [B_67] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_67),'#skF_1')
      | ~ v2_tops_1(B_67,'#skF_1')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_443])).

tff(c_453,plain,(
    ! [B_68] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_68),'#skF_1')
      | ~ v2_tops_1(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_450])).

tff(c_466,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_453])).

tff(c_473,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_466])).

tff(c_512,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_515,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16,c_512])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_515])).

tff(c_521,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_361,plain,(
    ! [B_62] :
      ( k2_pre_topc('#skF_1',B_62) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_62,'#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_356])).

tff(c_535,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_521,c_361])).

tff(c_543,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_279,plain,(
    ! [B_56] :
      ( v1_tops_1(B_56,'#skF_1')
      | k2_pre_topc('#skF_1',B_56) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_274])).

tff(c_538,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_521,c_279])).

tff(c_591,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_538])).

tff(c_12,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k1_tops_1(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_181,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_173])).

tff(c_188,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_71,c_70,c_70,c_181])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k3_subset_1(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_193,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k1_xboole_0) = k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_188,c_14])).

tff(c_197,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_193])).

tff(c_26,plain,(
    ! [A_16,B_18] :
      ( k3_subset_1(u1_struct_0(A_16),k2_pre_topc(A_16,k3_subset_1(u1_struct_0(A_16),B_18))) = k1_tops_1(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_240,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k2_pre_topc(A_53,B_54),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k3_subset_1(A_10,k3_subset_1(A_10,B_11)) = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_908,plain,(
    ! [A_81,B_82] :
      ( k3_subset_1(u1_struct_0(A_81),k3_subset_1(u1_struct_0(A_81),k2_pre_topc(A_81,B_82))) = k2_pre_topc(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_240,c_18])).

tff(c_5492,plain,(
    ! [A_184,B_185] :
      ( k3_subset_1(u1_struct_0(A_184),k1_tops_1(A_184,B_185)) = k2_pre_topc(A_184,k3_subset_1(u1_struct_0(A_184),B_185))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_184),B_185),k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_908])).

tff(c_5521,plain,(
    ! [A_186,B_187] :
      ( k3_subset_1(u1_struct_0(A_186),k1_tops_1(A_186,B_187)) = k2_pre_topc(A_186,k3_subset_1(u1_struct_0(A_186),B_187))
      | ~ l1_pre_topc(A_186)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_186))) ) ),
    inference(resolution,[status(thm)],[c_16,c_5492])).

tff(c_5530,plain,(
    ! [B_187] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_187)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_187))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_5521])).

tff(c_5536,plain,(
    ! [B_188] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_188)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_188))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_70,c_5530])).

tff(c_5600,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_5536])).

tff(c_5639,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_76,c_5600])).

tff(c_5641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_5639])).

tff(c_5643,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_474,plain,(
    ! [B_69,A_70] :
      ( v2_tops_1(B_69,A_70)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_70),B_69),A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_484,plain,(
    ! [B_69] :
      ( v2_tops_1(B_69,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_69),'#skF_1')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_474])).

tff(c_487,plain,(
    ! [B_69] :
      ( v2_tops_1(B_69,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_69),'#skF_1')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_484])).

tff(c_5646,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_5643,c_487])).

tff(c_5649,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_5646])).

tff(c_5651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5649])).

tff(c_5653,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5656,plain,(
    ! [A_189,B_190] :
      ( k4_xboole_0(A_189,B_190) = k1_xboole_0
      | ~ r1_tarski(A_189,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5660,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_5656])).

tff(c_5872,plain,(
    ! [A_217,B_218] :
      ( k2_pre_topc(A_217,B_218) = k2_struct_0(A_217)
      | ~ v1_tops_1(B_218,A_217)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5885,plain,(
    ! [B_218] :
      ( k2_pre_topc('#skF_1',B_218) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_218,'#skF_1')
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_5872])).

tff(c_5891,plain,(
    ! [B_219] :
      ( k2_pre_topc('#skF_1',B_219) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_219,'#skF_1')
      | ~ m1_subset_1(B_219,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5885])).

tff(c_5908,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_5891])).

tff(c_5909,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5908])).

tff(c_5714,plain,(
    ! [A_200,B_201] :
      ( k3_subset_1(A_200,k3_subset_1(A_200,B_201)) = B_201
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5717,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_71,c_5714])).

tff(c_5950,plain,(
    ! [A_223,B_224] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_223),B_224),A_223)
      | ~ v2_tops_1(B_224,A_223)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5957,plain,(
    ! [B_224] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_224),'#skF_1')
      | ~ v2_tops_1(B_224,'#skF_1')
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_5950])).

tff(c_5974,plain,(
    ! [B_227] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_227),'#skF_1')
      | ~ v2_tops_1(B_227,'#skF_1')
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_5957])).

tff(c_5984,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5717,c_5974])).

tff(c_5985,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5909,c_5984])).

tff(c_6001,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5985])).

tff(c_6022,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16,c_6001])).

tff(c_6026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_6022])).

tff(c_6028,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_5985])).

tff(c_5652,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5959,plain,(
    ! [B_224] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_224),'#skF_1')
      | ~ v2_tops_1(B_224,'#skF_1')
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_5957])).

tff(c_5911,plain,(
    ! [B_220,A_221] :
      ( v1_tops_1(B_220,A_221)
      | k2_pre_topc(A_221,B_220) != k2_struct_0(A_221)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5924,plain,(
    ! [B_220] :
      ( v1_tops_1(B_220,'#skF_1')
      | k2_pre_topc('#skF_1',B_220) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_5911])).

tff(c_5929,plain,(
    ! [B_220] :
      ( v1_tops_1(B_220,'#skF_1')
      | k2_pre_topc('#skF_1',B_220) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5924])).

tff(c_6042,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6028,c_5929])).

tff(c_6050,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6042])).

tff(c_5890,plain,(
    ! [B_218] :
      ( k2_pre_topc('#skF_1',B_218) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_218,'#skF_1')
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5885])).

tff(c_6043,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6028,c_5890])).

tff(c_6092,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_6050,c_6043])).

tff(c_6095,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_5959,c_6092])).

tff(c_6099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_5652,c_6095])).

tff(c_6101,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_6042])).

tff(c_5779,plain,(
    ! [A_210,B_211] :
      ( m1_subset_1(k2_pre_topc(A_210,B_211),k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5787,plain,(
    ! [B_211] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_211),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_5779])).

tff(c_5791,plain,(
    ! [B_211] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_211),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_5787])).

tff(c_6111,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6101,c_5791])).

tff(c_6118,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6028,c_6111])).

tff(c_6136,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6118,c_14])).

tff(c_6142,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5660,c_6136])).

tff(c_6211,plain,(
    ! [A_232,B_233] :
      ( k3_subset_1(u1_struct_0(A_232),k2_pre_topc(A_232,k3_subset_1(u1_struct_0(A_232),B_233))) = k1_tops_1(A_232,B_233)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6242,plain,(
    ! [B_233] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_233))) = k1_tops_1('#skF_1',B_233)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6211])).

tff(c_6254,plain,(
    ! [B_234] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_234))) = k1_tops_1('#skF_1',B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_70,c_6242])).

tff(c_6287,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6101,c_6254])).

tff(c_6305,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_6142,c_6287])).

tff(c_6307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5653,c_6305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.20/2.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/2.50  
% 7.43/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/2.50  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.43/2.50  
% 7.43/2.50  %Foreground sorts:
% 7.43/2.50  
% 7.43/2.50  
% 7.43/2.50  %Background operators:
% 7.43/2.50  
% 7.43/2.50  
% 7.43/2.50  %Foreground operators:
% 7.43/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.43/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.43/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.43/2.50  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 7.43/2.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.43/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.43/2.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.43/2.50  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.43/2.50  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.43/2.50  tff('#skF_2', type, '#skF_2': $i).
% 7.43/2.50  tff('#skF_1', type, '#skF_1': $i).
% 7.43/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.43/2.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.43/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.43/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.43/2.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.43/2.50  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.43/2.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.43/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.43/2.50  
% 7.43/2.53  tff(f_104, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 7.43/2.53  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.43/2.53  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.43/2.53  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.43/2.53  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 7.43/2.53  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.43/2.53  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 7.43/2.53  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.43/2.53  tff(f_94, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 7.43/2.53  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.43/2.53  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 7.43/2.53  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.43/2.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.43/2.53  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.43/2.53  tff(c_48, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.43/2.53  tff(c_76, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 7.43/2.53  tff(c_42, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.43/2.53  tff(c_82, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_42])).
% 7.43/2.53  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.43/2.53  tff(c_24, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.43/2.53  tff(c_61, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.43/2.53  tff(c_66, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_24, c_61])).
% 7.43/2.53  tff(c_70, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_66])).
% 7.43/2.53  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.43/2.53  tff(c_71, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_38])).
% 7.43/2.53  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.43/2.53  tff(c_261, plain, (![B_56, A_57]: (v1_tops_1(B_56, A_57) | k2_pre_topc(A_57, B_56)!=k2_struct_0(A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.43/2.53  tff(c_274, plain, (![B_56]: (v1_tops_1(B_56, '#skF_1') | k2_pre_topc('#skF_1', B_56)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_261])).
% 7.43/2.53  tff(c_280, plain, (![B_58]: (v1_tops_1(B_58, '#skF_1') | k2_pre_topc('#skF_1', B_58)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_274])).
% 7.43/2.53  tff(c_305, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_71, c_280])).
% 7.43/2.53  tff(c_306, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_305])).
% 7.43/2.53  tff(c_343, plain, (![A_61, B_62]: (k2_pre_topc(A_61, B_62)=k2_struct_0(A_61) | ~v1_tops_1(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.43/2.53  tff(c_356, plain, (![B_62]: (k2_pre_topc('#skF_1', B_62)=k2_struct_0('#skF_1') | ~v1_tops_1(B_62, '#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_343])).
% 7.43/2.53  tff(c_362, plain, (![B_63]: (k2_pre_topc('#skF_1', B_63)=k2_struct_0('#skF_1') | ~v1_tops_1(B_63, '#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_356])).
% 7.43/2.53  tff(c_381, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_71, c_362])).
% 7.43/2.53  tff(c_393, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_306, c_381])).
% 7.43/2.53  tff(c_133, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.43/2.53  tff(c_139, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_71, c_133])).
% 7.43/2.53  tff(c_443, plain, (![A_66, B_67]: (v1_tops_1(k3_subset_1(u1_struct_0(A_66), B_67), A_66) | ~v2_tops_1(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.43/2.53  tff(c_450, plain, (![B_67]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_67), '#skF_1') | ~v2_tops_1(B_67, '#skF_1') | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_443])).
% 7.43/2.53  tff(c_453, plain, (![B_68]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_68), '#skF_1') | ~v2_tops_1(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_450])).
% 7.43/2.53  tff(c_466, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_139, c_453])).
% 7.43/2.53  tff(c_473, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_393, c_466])).
% 7.43/2.53  tff(c_512, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_473])).
% 7.43/2.53  tff(c_515, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_512])).
% 7.43/2.53  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_515])).
% 7.43/2.53  tff(c_521, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_473])).
% 7.43/2.53  tff(c_361, plain, (![B_62]: (k2_pre_topc('#skF_1', B_62)=k2_struct_0('#skF_1') | ~v1_tops_1(B_62, '#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_356])).
% 7.43/2.53  tff(c_535, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_521, c_361])).
% 7.43/2.53  tff(c_543, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_535])).
% 7.43/2.53  tff(c_279, plain, (![B_56]: (v1_tops_1(B_56, '#skF_1') | k2_pre_topc('#skF_1', B_56)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_274])).
% 7.43/2.53  tff(c_538, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_521, c_279])).
% 7.43/2.53  tff(c_591, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_543, c_538])).
% 7.43/2.53  tff(c_12, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.43/2.53  tff(c_173, plain, (![A_50, B_51]: (m1_subset_1(k1_tops_1(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.43/2.53  tff(c_181, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_173])).
% 7.43/2.53  tff(c_188, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_71, c_70, c_70, c_181])).
% 7.43/2.53  tff(c_14, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k3_subset_1(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.43/2.53  tff(c_193, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k1_xboole_0)=k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)), inference(resolution, [status(thm)], [c_188, c_14])).
% 7.43/2.53  tff(c_197, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_193])).
% 7.43/2.53  tff(c_26, plain, (![A_16, B_18]: (k3_subset_1(u1_struct_0(A_16), k2_pre_topc(A_16, k3_subset_1(u1_struct_0(A_16), B_18)))=k1_tops_1(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.43/2.53  tff(c_240, plain, (![A_53, B_54]: (m1_subset_1(k2_pre_topc(A_53, B_54), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.43/2.53  tff(c_18, plain, (![A_10, B_11]: (k3_subset_1(A_10, k3_subset_1(A_10, B_11))=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.43/2.53  tff(c_908, plain, (![A_81, B_82]: (k3_subset_1(u1_struct_0(A_81), k3_subset_1(u1_struct_0(A_81), k2_pre_topc(A_81, B_82)))=k2_pre_topc(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_240, c_18])).
% 7.43/2.53  tff(c_5492, plain, (![A_184, B_185]: (k3_subset_1(u1_struct_0(A_184), k1_tops_1(A_184, B_185))=k2_pre_topc(A_184, k3_subset_1(u1_struct_0(A_184), B_185)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_184), B_185), k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184))), inference(superposition, [status(thm), theory('equality')], [c_26, c_908])).
% 7.43/2.53  tff(c_5521, plain, (![A_186, B_187]: (k3_subset_1(u1_struct_0(A_186), k1_tops_1(A_186, B_187))=k2_pre_topc(A_186, k3_subset_1(u1_struct_0(A_186), B_187)) | ~l1_pre_topc(A_186) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_186))))), inference(resolution, [status(thm)], [c_16, c_5492])).
% 7.43/2.53  tff(c_5530, plain, (![B_187]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_187))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_187)) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_187, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_70, c_5521])).
% 7.43/2.53  tff(c_5536, plain, (![B_188]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_188))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_188)) | ~m1_subset_1(B_188, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_70, c_5530])).
% 7.43/2.53  tff(c_5600, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_5536])).
% 7.43/2.53  tff(c_5639, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_76, c_5600])).
% 7.43/2.53  tff(c_5641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_591, c_5639])).
% 7.43/2.53  tff(c_5643, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_535])).
% 7.43/2.53  tff(c_474, plain, (![B_69, A_70]: (v2_tops_1(B_69, A_70) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_70), B_69), A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.43/2.53  tff(c_484, plain, (![B_69]: (v2_tops_1(B_69, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_69), '#skF_1') | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_474])).
% 7.43/2.53  tff(c_487, plain, (![B_69]: (v2_tops_1(B_69, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_69), '#skF_1') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_484])).
% 7.43/2.53  tff(c_5646, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_5643, c_487])).
% 7.43/2.53  tff(c_5649, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_5646])).
% 7.43/2.53  tff(c_5651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_5649])).
% 7.43/2.53  tff(c_5653, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 7.43/2.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.43/2.53  tff(c_5656, plain, (![A_189, B_190]: (k4_xboole_0(A_189, B_190)=k1_xboole_0 | ~r1_tarski(A_189, B_190))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.43/2.53  tff(c_5660, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_5656])).
% 7.43/2.53  tff(c_5872, plain, (![A_217, B_218]: (k2_pre_topc(A_217, B_218)=k2_struct_0(A_217) | ~v1_tops_1(B_218, A_217) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.43/2.53  tff(c_5885, plain, (![B_218]: (k2_pre_topc('#skF_1', B_218)=k2_struct_0('#skF_1') | ~v1_tops_1(B_218, '#skF_1') | ~m1_subset_1(B_218, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_5872])).
% 7.43/2.53  tff(c_5891, plain, (![B_219]: (k2_pre_topc('#skF_1', B_219)=k2_struct_0('#skF_1') | ~v1_tops_1(B_219, '#skF_1') | ~m1_subset_1(B_219, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5885])).
% 7.43/2.53  tff(c_5908, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_71, c_5891])).
% 7.43/2.53  tff(c_5909, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_5908])).
% 7.43/2.53  tff(c_5714, plain, (![A_200, B_201]: (k3_subset_1(A_200, k3_subset_1(A_200, B_201))=B_201 | ~m1_subset_1(B_201, k1_zfmisc_1(A_200)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.43/2.53  tff(c_5717, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_71, c_5714])).
% 7.43/2.53  tff(c_5950, plain, (![A_223, B_224]: (v1_tops_1(k3_subset_1(u1_struct_0(A_223), B_224), A_223) | ~v2_tops_1(B_224, A_223) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.43/2.53  tff(c_5957, plain, (![B_224]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_224), '#skF_1') | ~v2_tops_1(B_224, '#skF_1') | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_5950])).
% 7.43/2.53  tff(c_5974, plain, (![B_227]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_227), '#skF_1') | ~v2_tops_1(B_227, '#skF_1') | ~m1_subset_1(B_227, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_5957])).
% 7.43/2.53  tff(c_5984, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_5717, c_5974])).
% 7.43/2.53  tff(c_5985, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_5909, c_5984])).
% 7.43/2.53  tff(c_6001, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_5985])).
% 7.43/2.53  tff(c_6022, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_6001])).
% 7.43/2.53  tff(c_6026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_6022])).
% 7.43/2.53  tff(c_6028, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_5985])).
% 7.43/2.53  tff(c_5652, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 7.43/2.53  tff(c_5959, plain, (![B_224]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_224), '#skF_1') | ~v2_tops_1(B_224, '#skF_1') | ~m1_subset_1(B_224, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_5957])).
% 7.43/2.53  tff(c_5911, plain, (![B_220, A_221]: (v1_tops_1(B_220, A_221) | k2_pre_topc(A_221, B_220)!=k2_struct_0(A_221) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.43/2.53  tff(c_5924, plain, (![B_220]: (v1_tops_1(B_220, '#skF_1') | k2_pre_topc('#skF_1', B_220)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_220, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_5911])).
% 7.43/2.53  tff(c_5929, plain, (![B_220]: (v1_tops_1(B_220, '#skF_1') | k2_pre_topc('#skF_1', B_220)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_220, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5924])).
% 7.43/2.53  tff(c_6042, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6028, c_5929])).
% 7.43/2.53  tff(c_6050, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_6042])).
% 7.43/2.53  tff(c_5890, plain, (![B_218]: (k2_pre_topc('#skF_1', B_218)=k2_struct_0('#skF_1') | ~v1_tops_1(B_218, '#skF_1') | ~m1_subset_1(B_218, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5885])).
% 7.43/2.53  tff(c_6043, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_6028, c_5890])).
% 7.43/2.53  tff(c_6092, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_6050, c_6043])).
% 7.43/2.53  tff(c_6095, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_5959, c_6092])).
% 7.43/2.53  tff(c_6099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_5652, c_6095])).
% 7.43/2.53  tff(c_6101, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_6042])).
% 7.43/2.53  tff(c_5779, plain, (![A_210, B_211]: (m1_subset_1(k2_pre_topc(A_210, B_211), k1_zfmisc_1(u1_struct_0(A_210))) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.43/2.53  tff(c_5787, plain, (![B_211]: (m1_subset_1(k2_pre_topc('#skF_1', B_211), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_5779])).
% 7.43/2.53  tff(c_5791, plain, (![B_211]: (m1_subset_1(k2_pre_topc('#skF_1', B_211), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_211, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_5787])).
% 7.43/2.53  tff(c_6111, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6101, c_5791])).
% 7.43/2.53  tff(c_6118, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6028, c_6111])).
% 7.43/2.53  tff(c_6136, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6118, c_14])).
% 7.43/2.53  tff(c_6142, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5660, c_6136])).
% 7.43/2.53  tff(c_6211, plain, (![A_232, B_233]: (k3_subset_1(u1_struct_0(A_232), k2_pre_topc(A_232, k3_subset_1(u1_struct_0(A_232), B_233)))=k1_tops_1(A_232, B_233) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.43/2.53  tff(c_6242, plain, (![B_233]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_233)))=k1_tops_1('#skF_1', B_233) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6211])).
% 7.43/2.53  tff(c_6254, plain, (![B_234]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_234)))=k1_tops_1('#skF_1', B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_70, c_6242])).
% 7.43/2.53  tff(c_6287, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6101, c_6254])).
% 7.43/2.53  tff(c_6305, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71, c_6142, c_6287])).
% 7.43/2.53  tff(c_6307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5653, c_6305])).
% 7.43/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/2.53  
% 7.43/2.53  Inference rules
% 7.43/2.53  ----------------------
% 7.43/2.53  #Ref     : 0
% 7.43/2.53  #Sup     : 1427
% 7.43/2.53  #Fact    : 0
% 7.43/2.53  #Define  : 0
% 7.43/2.53  #Split   : 64
% 7.43/2.53  #Chain   : 0
% 7.43/2.53  #Close   : 0
% 7.43/2.53  
% 7.43/2.53  Ordering : KBO
% 7.43/2.53  
% 7.43/2.53  Simplification rules
% 7.43/2.53  ----------------------
% 7.43/2.53  #Subsume      : 275
% 7.43/2.53  #Demod        : 1351
% 7.43/2.53  #Tautology    : 431
% 7.43/2.53  #SimpNegUnit  : 234
% 7.43/2.53  #BackRed      : 5
% 7.43/2.53  
% 7.43/2.53  #Partial instantiations: 0
% 7.43/2.53  #Strategies tried      : 1
% 7.43/2.53  
% 7.43/2.53  Timing (in seconds)
% 7.43/2.53  ----------------------
% 7.43/2.53  Preprocessing        : 0.30
% 7.43/2.53  Parsing              : 0.16
% 7.43/2.53  CNF conversion       : 0.02
% 7.43/2.53  Main loop            : 1.45
% 7.43/2.53  Inferencing          : 0.41
% 7.43/2.53  Reduction            : 0.56
% 7.43/2.53  Demodulation         : 0.39
% 7.43/2.53  BG Simplification    : 0.05
% 7.43/2.53  Subsumption          : 0.32
% 7.43/2.53  Abstraction          : 0.07
% 7.43/2.53  MUC search           : 0.00
% 7.43/2.53  Cooper               : 0.00
% 7.43/2.53  Total                : 1.80
% 7.43/2.53  Index Insertion      : 0.00
% 7.43/2.53  Index Deletion       : 0.00
% 7.43/2.53  Index Matching       : 0.00
% 7.43/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
