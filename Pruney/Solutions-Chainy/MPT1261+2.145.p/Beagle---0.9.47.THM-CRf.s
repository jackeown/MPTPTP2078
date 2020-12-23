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
% DateTime   : Thu Dec  3 10:21:32 EST 2020

% Result     : Theorem 7.72s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 212 expanded)
%              Number of leaves         :   38 (  86 expanded)
%              Depth                    :   17
%              Number of atoms          :  139 ( 337 expanded)
%              Number of equality atoms :   66 ( 145 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_13337,plain,(
    ! [A_311,B_312,C_313] :
      ( k7_subset_1(A_311,B_312,C_313) = k4_xboole_0(B_312,C_313)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(A_311)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13340,plain,(
    ! [C_313] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_313) = k4_xboole_0('#skF_2',C_313) ),
    inference(resolution,[status(thm)],[c_32,c_13337])).

tff(c_38,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_124,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1762,plain,(
    ! [A_116,B_117] :
      ( k4_subset_1(u1_struct_0(A_116),B_117,k2_tops_1(A_116,B_117)) = k2_pre_topc(A_116,B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1766,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1762])).

tff(c_1770,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1766])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_44,B_45] : k2_xboole_0(k4_xboole_0(A_44,B_45),A_44) = A_44 ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_100,plain,(
    ! [B_45] : k4_xboole_0(k1_xboole_0,B_45) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_6])).

tff(c_264,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k4_xboole_0(B_56,A_55)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_276,plain,(
    ! [B_45] : k5_xboole_0(B_45,k1_xboole_0) = k2_xboole_0(B_45,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_264])).

tff(c_280,plain,(
    ! [B_45] : k5_xboole_0(B_45,k1_xboole_0) = B_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_276])).

tff(c_44,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_201,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_44])).

tff(c_471,plain,(
    ! [A_69,B_70,C_71] :
      ( k7_subset_1(A_69,B_70,C_71) = k4_xboole_0(B_70,C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_509,plain,(
    ! [C_74] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_74) = k4_xboole_0('#skF_2',C_74) ),
    inference(resolution,[status(thm)],[c_32,c_471])).

tff(c_521,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_509])).

tff(c_92,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_794,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_92])).

tff(c_144,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [B_51] : k3_xboole_0(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_183,plain,(
    ! [B_51] : k3_xboole_0(B_51,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_2])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_273,plain,(
    ! [A_13,B_14] : k5_xboole_0(k4_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k2_xboole_0(k4_xboole_0(A_13,B_14),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_264])).

tff(c_477,plain,(
    ! [A_72,B_73] : k5_xboole_0(k4_xboole_0(A_72,B_73),k3_xboole_0(A_72,B_73)) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_273])).

tff(c_524,plain,(
    ! [B_75] : k5_xboole_0(k4_xboole_0(B_75,k1_xboole_0),k1_xboole_0) = B_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_477])).

tff(c_551,plain,(
    ! [B_76] : k4_xboole_0(B_76,k1_xboole_0) = B_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_280])).

tff(c_570,plain,(
    ! [B_76] : k4_xboole_0(B_76,B_76) = k3_xboole_0(B_76,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_14])).

tff(c_674,plain,(
    ! [B_82] : k4_xboole_0(B_82,B_82) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_570])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_686,plain,(
    ! [B_82,C_12] : k4_xboole_0(B_82,k2_xboole_0(B_82,C_12)) = k4_xboole_0(k1_xboole_0,C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_12])).

tff(c_825,plain,(
    ! [B_86,C_87] : k4_xboole_0(B_86,k2_xboole_0(B_86,C_87)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_686])).

tff(c_857,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_825])).

tff(c_16,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1242,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_16])).

tff(c_1257,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_1242])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k2_tops_1(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1558,plain,(
    ! [A_108,B_109,C_110] :
      ( k4_subset_1(A_108,B_109,C_110) = k2_xboole_0(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(A_108))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12319,plain,(
    ! [A_281,B_282,B_283] :
      ( k4_subset_1(u1_struct_0(A_281),B_282,k2_tops_1(A_281,B_283)) = k2_xboole_0(B_282,k2_tops_1(A_281,B_283))
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_22,c_1558])).

tff(c_12323,plain,(
    ! [B_283] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_283)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_283))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_12319])).

tff(c_12978,plain,(
    ! [B_288] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_288)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_288))
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12323])).

tff(c_12985,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_12978])).

tff(c_12990,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1770,c_1257,c_12985])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_816,plain,(
    ! [A_84,B_85] :
      ( v4_pre_topc(k2_pre_topc(A_84,B_85),A_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_820,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_816])).

tff(c_824,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_820])).

tff(c_12992,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12990,c_824])).

tff(c_12994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_12992])).

tff(c_12995,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_13534,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13340,c_12995])).

tff(c_12996,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_13870,plain,(
    ! [A_336,B_337] :
      ( r1_tarski(k2_tops_1(A_336,B_337),B_337)
      | ~ v4_pre_topc(B_337,A_336)
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ l1_pre_topc(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_13874,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_13870])).

tff(c_13878,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12996,c_13874])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13886,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13878,c_8])).

tff(c_15259,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13886])).

tff(c_14879,plain,(
    ! [A_368,B_369] :
      ( k7_subset_1(u1_struct_0(A_368),B_369,k2_tops_1(A_368,B_369)) = k1_tops_1(A_368,B_369)
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0(A_368)))
      | ~ l1_pre_topc(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14883,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_14879])).

tff(c_14887,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_13340,c_14883])).

tff(c_14912,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14887,c_14])).

tff(c_16485,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15259,c_14912])).

tff(c_16486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13534,c_16485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.72/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.86  
% 7.72/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.87  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.72/2.87  
% 7.72/2.87  %Foreground sorts:
% 7.72/2.87  
% 7.72/2.87  
% 7.72/2.87  %Background operators:
% 7.72/2.87  
% 7.72/2.87  
% 7.72/2.87  %Foreground operators:
% 7.72/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.72/2.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.72/2.87  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.72/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.72/2.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.72/2.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.72/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.72/2.87  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.72/2.87  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.72/2.87  tff('#skF_2', type, '#skF_2': $i).
% 7.72/2.87  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.72/2.87  tff('#skF_1', type, '#skF_1': $i).
% 7.72/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.72/2.87  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.72/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.72/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.72/2.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.72/2.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.72/2.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.72/2.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.72/2.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.72/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.72/2.87  
% 7.72/2.88  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 7.72/2.88  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.72/2.88  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 7.72/2.88  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.72/2.88  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.72/2.88  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.72/2.88  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.72/2.88  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.72/2.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.72/2.88  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.72/2.88  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 7.72/2.88  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.72/2.88  tff(f_69, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 7.72/2.88  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 7.72/2.88  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.72/2.88  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 7.72/2.88  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.72/2.88  tff(c_13337, plain, (![A_311, B_312, C_313]: (k7_subset_1(A_311, B_312, C_313)=k4_xboole_0(B_312, C_313) | ~m1_subset_1(B_312, k1_zfmisc_1(A_311)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.72/2.88  tff(c_13340, plain, (![C_313]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_313)=k4_xboole_0('#skF_2', C_313))), inference(resolution, [status(thm)], [c_32, c_13337])).
% 7.72/2.88  tff(c_38, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.72/2.88  tff(c_124, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 7.72/2.88  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.72/2.88  tff(c_1762, plain, (![A_116, B_117]: (k4_subset_1(u1_struct_0(A_116), B_117, k2_tops_1(A_116, B_117))=k2_pre_topc(A_116, B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.72/2.88  tff(c_1766, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1762])).
% 7.72/2.88  tff(c_1770, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1766])).
% 7.72/2.88  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.72/2.88  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.72/2.88  tff(c_88, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.72/2.88  tff(c_93, plain, (![A_44, B_45]: (k2_xboole_0(k4_xboole_0(A_44, B_45), A_44)=A_44)), inference(resolution, [status(thm)], [c_10, c_88])).
% 7.72/2.88  tff(c_100, plain, (![B_45]: (k4_xboole_0(k1_xboole_0, B_45)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_93, c_6])).
% 7.72/2.88  tff(c_264, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k4_xboole_0(B_56, A_55))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.72/2.88  tff(c_276, plain, (![B_45]: (k5_xboole_0(B_45, k1_xboole_0)=k2_xboole_0(B_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_100, c_264])).
% 7.72/2.88  tff(c_280, plain, (![B_45]: (k5_xboole_0(B_45, k1_xboole_0)=B_45)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_276])).
% 7.72/2.88  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.72/2.88  tff(c_201, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_124, c_44])).
% 7.72/2.88  tff(c_471, plain, (![A_69, B_70, C_71]: (k7_subset_1(A_69, B_70, C_71)=k4_xboole_0(B_70, C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.72/2.88  tff(c_509, plain, (![C_74]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_74)=k4_xboole_0('#skF_2', C_74))), inference(resolution, [status(thm)], [c_32, c_471])).
% 7.72/2.88  tff(c_521, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_201, c_509])).
% 7.72/2.88  tff(c_92, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_10, c_88])).
% 7.72/2.88  tff(c_794, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_521, c_92])).
% 7.72/2.88  tff(c_144, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.72/2.88  tff(c_178, plain, (![B_51]: (k3_xboole_0(k1_xboole_0, B_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_144, c_100])).
% 7.72/2.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.72/2.88  tff(c_183, plain, (![B_51]: (k3_xboole_0(B_51, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_2])).
% 7.72/2.88  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.72/2.88  tff(c_273, plain, (![A_13, B_14]: (k5_xboole_0(k4_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k2_xboole_0(k4_xboole_0(A_13, B_14), A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_264])).
% 7.72/2.88  tff(c_477, plain, (![A_72, B_73]: (k5_xboole_0(k4_xboole_0(A_72, B_73), k3_xboole_0(A_72, B_73))=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_273])).
% 7.72/2.88  tff(c_524, plain, (![B_75]: (k5_xboole_0(k4_xboole_0(B_75, k1_xboole_0), k1_xboole_0)=B_75)), inference(superposition, [status(thm), theory('equality')], [c_183, c_477])).
% 7.72/2.88  tff(c_551, plain, (![B_76]: (k4_xboole_0(B_76, k1_xboole_0)=B_76)), inference(superposition, [status(thm), theory('equality')], [c_524, c_280])).
% 7.72/2.88  tff(c_570, plain, (![B_76]: (k4_xboole_0(B_76, B_76)=k3_xboole_0(B_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_551, c_14])).
% 7.72/2.88  tff(c_674, plain, (![B_82]: (k4_xboole_0(B_82, B_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_570])).
% 7.72/2.88  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.72/2.88  tff(c_686, plain, (![B_82, C_12]: (k4_xboole_0(B_82, k2_xboole_0(B_82, C_12))=k4_xboole_0(k1_xboole_0, C_12))), inference(superposition, [status(thm), theory('equality')], [c_674, c_12])).
% 7.72/2.88  tff(c_825, plain, (![B_86, C_87]: (k4_xboole_0(B_86, k2_xboole_0(B_86, C_87))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_686])).
% 7.72/2.88  tff(c_857, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_794, c_825])).
% 7.72/2.88  tff(c_16, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.72/2.88  tff(c_1242, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_857, c_16])).
% 7.72/2.88  tff(c_1257, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_280, c_1242])).
% 7.72/2.88  tff(c_22, plain, (![A_23, B_24]: (m1_subset_1(k2_tops_1(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.72/2.88  tff(c_1558, plain, (![A_108, B_109, C_110]: (k4_subset_1(A_108, B_109, C_110)=k2_xboole_0(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(A_108)) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.72/2.88  tff(c_12319, plain, (![A_281, B_282, B_283]: (k4_subset_1(u1_struct_0(A_281), B_282, k2_tops_1(A_281, B_283))=k2_xboole_0(B_282, k2_tops_1(A_281, B_283)) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_281))) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281))), inference(resolution, [status(thm)], [c_22, c_1558])).
% 7.72/2.88  tff(c_12323, plain, (![B_283]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_283))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_283)) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_12319])).
% 7.72/2.88  tff(c_12978, plain, (![B_288]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_288))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_288)) | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12323])).
% 7.72/2.88  tff(c_12985, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_12978])).
% 7.72/2.88  tff(c_12990, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1770, c_1257, c_12985])).
% 7.72/2.88  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.72/2.88  tff(c_816, plain, (![A_84, B_85]: (v4_pre_topc(k2_pre_topc(A_84, B_85), A_84) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.72/2.88  tff(c_820, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_816])).
% 7.72/2.88  tff(c_824, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_820])).
% 7.72/2.88  tff(c_12992, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12990, c_824])).
% 7.72/2.88  tff(c_12994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_12992])).
% 7.72/2.88  tff(c_12995, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 7.72/2.88  tff(c_13534, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13340, c_12995])).
% 7.72/2.88  tff(c_12996, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 7.72/2.88  tff(c_13870, plain, (![A_336, B_337]: (r1_tarski(k2_tops_1(A_336, B_337), B_337) | ~v4_pre_topc(B_337, A_336) | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0(A_336))) | ~l1_pre_topc(A_336))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.72/2.88  tff(c_13874, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_13870])).
% 7.72/2.88  tff(c_13878, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12996, c_13874])).
% 7.72/2.88  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.72/2.88  tff(c_13886, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13878, c_8])).
% 7.72/2.88  tff(c_15259, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2, c_13886])).
% 7.72/2.88  tff(c_14879, plain, (![A_368, B_369]: (k7_subset_1(u1_struct_0(A_368), B_369, k2_tops_1(A_368, B_369))=k1_tops_1(A_368, B_369) | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0(A_368))) | ~l1_pre_topc(A_368))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.72/2.88  tff(c_14883, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_14879])).
% 7.72/2.88  tff(c_14887, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_13340, c_14883])).
% 7.72/2.88  tff(c_14912, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14887, c_14])).
% 7.72/2.88  tff(c_16485, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15259, c_14912])).
% 7.72/2.88  tff(c_16486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13534, c_16485])).
% 7.72/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/2.88  
% 7.72/2.88  Inference rules
% 7.72/2.88  ----------------------
% 7.72/2.88  #Ref     : 0
% 7.72/2.88  #Sup     : 4086
% 7.72/2.88  #Fact    : 0
% 7.72/2.88  #Define  : 0
% 7.72/2.88  #Split   : 1
% 7.72/2.88  #Chain   : 0
% 7.72/2.88  #Close   : 0
% 7.72/2.88  
% 7.72/2.88  Ordering : KBO
% 7.72/2.88  
% 7.72/2.88  Simplification rules
% 7.72/2.88  ----------------------
% 7.72/2.88  #Subsume      : 15
% 7.72/2.88  #Demod        : 3867
% 7.72/2.88  #Tautology    : 3003
% 7.72/2.88  #SimpNegUnit  : 3
% 7.72/2.88  #BackRed      : 7
% 7.72/2.88  
% 7.72/2.88  #Partial instantiations: 0
% 7.72/2.88  #Strategies tried      : 1
% 7.72/2.88  
% 7.72/2.88  Timing (in seconds)
% 7.72/2.88  ----------------------
% 7.72/2.89  Preprocessing        : 0.34
% 7.72/2.89  Parsing              : 0.19
% 7.72/2.89  CNF conversion       : 0.02
% 7.72/2.89  Main loop            : 1.73
% 7.72/2.89  Inferencing          : 0.47
% 7.72/2.89  Reduction            : 0.85
% 7.72/2.89  Demodulation         : 0.72
% 7.72/2.89  BG Simplification    : 0.05
% 7.72/2.89  Subsumption          : 0.25
% 7.72/2.89  Abstraction          : 0.09
% 7.72/2.89  MUC search           : 0.00
% 7.72/2.89  Cooper               : 0.00
% 7.72/2.89  Total                : 2.10
% 7.72/2.89  Index Insertion      : 0.00
% 7.72/2.89  Index Deletion       : 0.00
% 7.72/2.89  Index Matching       : 0.00
% 7.72/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
