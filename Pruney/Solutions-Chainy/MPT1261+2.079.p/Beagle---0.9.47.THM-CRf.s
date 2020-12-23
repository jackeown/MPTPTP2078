%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:23 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 162 expanded)
%              Number of leaves         :   38 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  127 ( 279 expanded)
%              Number of equality atoms :   66 ( 118 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4884,plain,(
    ! [A_187,B_188,C_189] :
      ( k7_subset_1(A_187,B_188,C_189) = k4_xboole_0(B_188,C_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4887,plain,(
    ! [C_189] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_189) = k4_xboole_0('#skF_2',C_189) ),
    inference(resolution,[status(thm)],[c_32,c_4884])).

tff(c_38,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_117,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_932,plain,(
    ! [B_89,A_90] :
      ( v4_pre_topc(B_89,A_90)
      | k2_pre_topc(A_90,B_89) != B_89
      | ~ v2_pre_topc(A_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_938,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_932])).

tff(c_942,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_938])).

tff(c_943,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_942])).

tff(c_44,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_257,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_44])).

tff(c_482,plain,(
    ! [A_63,B_64,C_65] :
      ( k7_subset_1(A_63,B_64,C_65) = k4_xboole_0(B_64,C_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_552,plain,(
    ! [C_69] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_69) = k4_xboole_0('#skF_2',C_69) ),
    inference(resolution,[status(thm)],[c_32,c_482])).

tff(c_564,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_552])).

tff(c_12,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_148,plain,(
    ! [B_46,A_47] : k1_setfam_1(k2_tarski(B_46,A_47)) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_20,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_154,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_20])).

tff(c_396,plain,(
    ! [A_59,B_60] : k2_xboole_0(k3_xboole_0(A_59,B_60),k4_xboole_0(A_59,B_60)) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_411,plain,(
    ! [A_47,B_46] : k2_xboole_0(k3_xboole_0(A_47,B_46),k4_xboole_0(B_46,A_47)) = B_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_396])).

tff(c_133,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,(
    ! [B_54,A_55] : k3_tarski(k2_tarski(B_54,A_55)) = k2_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_133])).

tff(c_14,plain,(
    ! [A_12,B_13] : k3_tarski(k2_tarski(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_268,plain,(
    ! [B_54,A_55] : k2_xboole_0(B_54,A_55) = k2_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_14])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1106,plain,(
    ! [A_96,B_97] : k2_xboole_0(k3_xboole_0(A_96,k2_xboole_0(A_96,B_97)),k1_xboole_0) = A_96 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_396])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1186,plain,(
    ! [A_98,B_99] : k3_xboole_0(A_98,k2_xboole_0(A_98,B_99)) = A_98 ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_4])).

tff(c_1262,plain,(
    ! [B_100,A_101] : k3_xboole_0(B_100,k2_xboole_0(A_101,B_100)) = B_100 ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_1186])).

tff(c_171,plain,(
    ! [B_48,A_49] : k3_xboole_0(B_48,A_49) = k3_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_20])).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k3_xboole_0(A_4,B_5)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [A_49,B_48] : k2_xboole_0(A_49,k3_xboole_0(B_48,A_49)) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_6])).

tff(c_2153,plain,(
    ! [A_126,B_127] : k2_xboole_0(k2_xboole_0(A_126,B_127),B_127) = k2_xboole_0(A_126,B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_1262,c_186])).

tff(c_2193,plain,(
    ! [A_47,B_46] : k2_xboole_0(k3_xboole_0(A_47,B_46),k4_xboole_0(B_46,A_47)) = k2_xboole_0(B_46,k4_xboole_0(B_46,A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_2153])).

tff(c_2248,plain,(
    ! [B_128,A_129] : k2_xboole_0(B_128,k4_xboole_0(B_128,A_129)) = B_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_2193])).

tff(c_2297,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_2248])).

tff(c_1097,plain,(
    ! [A_94,B_95] :
      ( k4_subset_1(u1_struct_0(A_94),B_95,k2_tops_1(A_94,B_95)) = k2_pre_topc(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1101,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1097])).

tff(c_1105,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1101])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_tops_1(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_838,plain,(
    ! [A_82,B_83,C_84] :
      ( k4_subset_1(A_82,B_83,C_84) = k2_xboole_0(B_83,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3842,plain,(
    ! [A_153,B_154,B_155] :
      ( k4_subset_1(u1_struct_0(A_153),B_154,k2_tops_1(A_153,B_155)) = k2_xboole_0(B_154,k2_tops_1(A_153,B_155))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(resolution,[status(thm)],[c_26,c_838])).

tff(c_3846,plain,(
    ! [B_155] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_155)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_155))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_3842])).

tff(c_4455,plain,(
    ! [B_164] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_164)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_164))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3846])).

tff(c_4462,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_4455])).

tff(c_4467,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2297,c_1105,c_4462])).

tff(c_4469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_943,c_4467])).

tff(c_4470,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4915,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4887,c_4470])).

tff(c_4471,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_5160,plain,(
    ! [A_203,B_204] :
      ( k2_pre_topc(A_203,B_204) = B_204
      | ~ v4_pre_topc(B_204,A_203)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5166,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_5160])).

tff(c_5170,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4471,c_5166])).

tff(c_5932,plain,(
    ! [A_231,B_232] :
      ( k7_subset_1(u1_struct_0(A_231),k2_pre_topc(A_231,B_232),k1_tops_1(A_231,B_232)) = k2_tops_1(A_231,B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5941,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5170,c_5932])).

tff(c_5945,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_4887,c_5941])).

tff(c_5947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4915,c_5945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/2.07  
% 4.78/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/2.07  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.78/2.07  
% 4.78/2.07  %Foreground sorts:
% 4.78/2.07  
% 4.78/2.07  
% 4.78/2.07  %Background operators:
% 4.78/2.07  
% 4.78/2.07  
% 4.78/2.07  %Foreground operators:
% 4.78/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.78/2.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.78/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.78/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.78/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.78/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.78/2.07  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.78/2.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.78/2.07  tff('#skF_2', type, '#skF_2': $i).
% 4.78/2.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.78/2.07  tff('#skF_1', type, '#skF_1': $i).
% 4.78/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.78/2.07  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.78/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.78/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/2.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.78/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.78/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.78/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.78/2.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.78/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/2.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.78/2.07  
% 5.10/2.09  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.10/2.09  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.10/2.09  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.10/2.09  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.10/2.09  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.10/2.09  tff(f_35, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.10/2.09  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.10/2.09  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.10/2.09  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.10/2.09  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.10/2.09  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.10/2.09  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.10/2.09  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.10/2.09  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.10/2.09  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.10/2.09  tff(c_4884, plain, (![A_187, B_188, C_189]: (k7_subset_1(A_187, B_188, C_189)=k4_xboole_0(B_188, C_189) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.10/2.09  tff(c_4887, plain, (![C_189]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_189)=k4_xboole_0('#skF_2', C_189))), inference(resolution, [status(thm)], [c_32, c_4884])).
% 5.10/2.09  tff(c_38, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.10/2.09  tff(c_117, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 5.10/2.09  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.10/2.09  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.10/2.09  tff(c_932, plain, (![B_89, A_90]: (v4_pre_topc(B_89, A_90) | k2_pre_topc(A_90, B_89)!=B_89 | ~v2_pre_topc(A_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.10/2.09  tff(c_938, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_932])).
% 5.10/2.09  tff(c_942, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_938])).
% 5.10/2.09  tff(c_943, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_117, c_942])).
% 5.10/2.09  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.10/2.09  tff(c_257, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_117, c_44])).
% 5.10/2.09  tff(c_482, plain, (![A_63, B_64, C_65]: (k7_subset_1(A_63, B_64, C_65)=k4_xboole_0(B_64, C_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.10/2.09  tff(c_552, plain, (![C_69]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_69)=k4_xboole_0('#skF_2', C_69))), inference(resolution, [status(thm)], [c_32, c_482])).
% 5.10/2.09  tff(c_564, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_257, c_552])).
% 5.10/2.09  tff(c_12, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.10/2.09  tff(c_118, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.10/2.09  tff(c_148, plain, (![B_46, A_47]: (k1_setfam_1(k2_tarski(B_46, A_47))=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_12, c_118])).
% 5.10/2.09  tff(c_20, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.10/2.09  tff(c_154, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_148, c_20])).
% 5.10/2.09  tff(c_396, plain, (![A_59, B_60]: (k2_xboole_0(k3_xboole_0(A_59, B_60), k4_xboole_0(A_59, B_60))=A_59)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.10/2.09  tff(c_411, plain, (![A_47, B_46]: (k2_xboole_0(k3_xboole_0(A_47, B_46), k4_xboole_0(B_46, A_47))=B_46)), inference(superposition, [status(thm), theory('equality')], [c_154, c_396])).
% 5.10/2.09  tff(c_133, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.10/2.09  tff(c_262, plain, (![B_54, A_55]: (k3_tarski(k2_tarski(B_54, A_55))=k2_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_12, c_133])).
% 5.10/2.09  tff(c_14, plain, (![A_12, B_13]: (k3_tarski(k2_tarski(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.10/2.09  tff(c_268, plain, (![B_54, A_55]: (k2_xboole_0(B_54, A_55)=k2_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_262, c_14])).
% 5.10/2.09  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.10/2.09  tff(c_1106, plain, (![A_96, B_97]: (k2_xboole_0(k3_xboole_0(A_96, k2_xboole_0(A_96, B_97)), k1_xboole_0)=A_96)), inference(superposition, [status(thm), theory('equality')], [c_8, c_396])).
% 5.10/2.09  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.10/2.09  tff(c_1186, plain, (![A_98, B_99]: (k3_xboole_0(A_98, k2_xboole_0(A_98, B_99))=A_98)), inference(superposition, [status(thm), theory('equality')], [c_1106, c_4])).
% 5.10/2.09  tff(c_1262, plain, (![B_100, A_101]: (k3_xboole_0(B_100, k2_xboole_0(A_101, B_100))=B_100)), inference(superposition, [status(thm), theory('equality')], [c_268, c_1186])).
% 5.10/2.09  tff(c_171, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k3_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_148, c_20])).
% 5.10/2.09  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k3_xboole_0(A_4, B_5))=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/2.09  tff(c_186, plain, (![A_49, B_48]: (k2_xboole_0(A_49, k3_xboole_0(B_48, A_49))=A_49)), inference(superposition, [status(thm), theory('equality')], [c_171, c_6])).
% 5.10/2.09  tff(c_2153, plain, (![A_126, B_127]: (k2_xboole_0(k2_xboole_0(A_126, B_127), B_127)=k2_xboole_0(A_126, B_127))), inference(superposition, [status(thm), theory('equality')], [c_1262, c_186])).
% 5.10/2.09  tff(c_2193, plain, (![A_47, B_46]: (k2_xboole_0(k3_xboole_0(A_47, B_46), k4_xboole_0(B_46, A_47))=k2_xboole_0(B_46, k4_xboole_0(B_46, A_47)))), inference(superposition, [status(thm), theory('equality')], [c_411, c_2153])).
% 5.10/2.09  tff(c_2248, plain, (![B_128, A_129]: (k2_xboole_0(B_128, k4_xboole_0(B_128, A_129))=B_128)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_2193])).
% 5.10/2.09  tff(c_2297, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_564, c_2248])).
% 5.10/2.09  tff(c_1097, plain, (![A_94, B_95]: (k4_subset_1(u1_struct_0(A_94), B_95, k2_tops_1(A_94, B_95))=k2_pre_topc(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.10/2.09  tff(c_1101, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1097])).
% 5.10/2.09  tff(c_1105, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1101])).
% 5.10/2.09  tff(c_26, plain, (![A_25, B_26]: (m1_subset_1(k2_tops_1(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.10/2.09  tff(c_838, plain, (![A_82, B_83, C_84]: (k4_subset_1(A_82, B_83, C_84)=k2_xboole_0(B_83, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.10/2.09  tff(c_3842, plain, (![A_153, B_154, B_155]: (k4_subset_1(u1_struct_0(A_153), B_154, k2_tops_1(A_153, B_155))=k2_xboole_0(B_154, k2_tops_1(A_153, B_155)) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(resolution, [status(thm)], [c_26, c_838])).
% 5.10/2.09  tff(c_3846, plain, (![B_155]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_155))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_155)) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_3842])).
% 5.10/2.09  tff(c_4455, plain, (![B_164]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_164))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_164)) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3846])).
% 5.10/2.09  tff(c_4462, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_4455])).
% 5.10/2.09  tff(c_4467, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2297, c_1105, c_4462])).
% 5.10/2.09  tff(c_4469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_943, c_4467])).
% 5.10/2.09  tff(c_4470, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 5.10/2.09  tff(c_4915, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4887, c_4470])).
% 5.10/2.09  tff(c_4471, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 5.10/2.09  tff(c_5160, plain, (![A_203, B_204]: (k2_pre_topc(A_203, B_204)=B_204 | ~v4_pre_topc(B_204, A_203) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.10/2.09  tff(c_5166, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_5160])).
% 5.10/2.09  tff(c_5170, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4471, c_5166])).
% 5.10/2.09  tff(c_5932, plain, (![A_231, B_232]: (k7_subset_1(u1_struct_0(A_231), k2_pre_topc(A_231, B_232), k1_tops_1(A_231, B_232))=k2_tops_1(A_231, B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.10/2.09  tff(c_5941, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5170, c_5932])).
% 5.10/2.09  tff(c_5945, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_4887, c_5941])).
% 5.10/2.09  tff(c_5947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4915, c_5945])).
% 5.10/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/2.09  
% 5.10/2.09  Inference rules
% 5.10/2.09  ----------------------
% 5.10/2.09  #Ref     : 0
% 5.10/2.09  #Sup     : 1455
% 5.10/2.09  #Fact    : 0
% 5.10/2.09  #Define  : 0
% 5.10/2.09  #Split   : 2
% 5.10/2.09  #Chain   : 0
% 5.10/2.09  #Close   : 0
% 5.10/2.09  
% 5.10/2.09  Ordering : KBO
% 5.10/2.09  
% 5.10/2.09  Simplification rules
% 5.10/2.09  ----------------------
% 5.10/2.09  #Subsume      : 26
% 5.10/2.09  #Demod        : 1424
% 5.10/2.09  #Tautology    : 1172
% 5.10/2.09  #SimpNegUnit  : 4
% 5.10/2.09  #BackRed      : 9
% 5.10/2.09  
% 5.10/2.09  #Partial instantiations: 0
% 5.10/2.09  #Strategies tried      : 1
% 5.10/2.09  
% 5.10/2.09  Timing (in seconds)
% 5.10/2.09  ----------------------
% 5.10/2.09  Preprocessing        : 0.31
% 5.10/2.09  Parsing              : 0.16
% 5.10/2.09  CNF conversion       : 0.02
% 5.10/2.09  Main loop            : 0.94
% 5.10/2.09  Inferencing          : 0.31
% 5.10/2.09  Reduction            : 0.40
% 5.10/2.09  Demodulation         : 0.34
% 5.10/2.09  BG Simplification    : 0.03
% 5.10/2.09  Subsumption          : 0.13
% 5.10/2.09  Abstraction          : 0.05
% 5.10/2.09  MUC search           : 0.00
% 5.10/2.09  Cooper               : 0.00
% 5.10/2.09  Total                : 1.29
% 5.10/2.09  Index Insertion      : 0.00
% 5.10/2.09  Index Deletion       : 0.00
% 5.10/2.09  Index Matching       : 0.00
% 5.10/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
