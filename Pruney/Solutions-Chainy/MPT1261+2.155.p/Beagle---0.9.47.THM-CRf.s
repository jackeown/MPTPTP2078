%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:33 EST 2020

% Result     : Theorem 9.17s
% Output     : CNFRefutation 9.17s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 187 expanded)
%              Number of leaves         :   41 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 348 expanded)
%              Number of equality atoms :   67 ( 115 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_92,axiom,(
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

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_19385,plain,(
    ! [A_498,B_499,C_500] :
      ( k7_subset_1(A_498,B_499,C_500) = k4_xboole_0(B_499,C_500)
      | ~ m1_subset_1(B_499,k1_zfmisc_1(A_498)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_19393,plain,(
    ! [C_500] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_500) = k4_xboole_0('#skF_2',C_500) ),
    inference(resolution,[status(thm)],[c_52,c_19385])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_101,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2403,plain,(
    ! [B_147,A_148] :
      ( v4_pre_topc(B_147,A_148)
      | k2_pre_topc(A_148,B_147) != B_147
      | ~ v2_pre_topc(A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2413,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2403])).

tff(c_2422,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_2413])).

tff(c_2423,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_2422])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_424,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski(A_78,k2_xboole_0(B_79,C_80))
      | ~ r1_tarski(k4_xboole_0(A_78,B_79),C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_450,plain,(
    ! [A_81,B_82] : r1_tarski(A_81,k2_xboole_0(B_82,A_81)) ),
    inference(resolution,[status(thm)],[c_14,c_424])).

tff(c_471,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_450])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_953,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k3_subset_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2048,plain,(
    ! [B_139,A_140] :
      ( k4_xboole_0(B_139,A_140) = k3_subset_1(B_139,A_140)
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(resolution,[status(thm)],[c_38,c_953])).

tff(c_2087,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = k3_subset_1(A_5,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_471,c_2048])).

tff(c_2118,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2087])).

tff(c_732,plain,(
    ! [A_92,B_93] :
      ( k3_subset_1(A_92,k3_subset_1(A_92,B_93)) = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2466,plain,(
    ! [B_149,A_150] :
      ( k3_subset_1(B_149,k3_subset_1(B_149,A_150)) = A_150
      | ~ r1_tarski(A_150,B_149) ) ),
    inference(resolution,[status(thm)],[c_38,c_732])).

tff(c_2491,plain,(
    ! [A_5] :
      ( k3_subset_1(A_5,A_5) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2118,c_2466])).

tff(c_2523,plain,(
    ! [A_5] : k3_subset_1(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_2491])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_180,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_64])).

tff(c_1140,plain,(
    ! [A_108,B_109,C_110] :
      ( k7_subset_1(A_108,B_109,C_110) = k4_xboole_0(B_109,C_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1216,plain,(
    ! [C_113] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_113) = k4_xboole_0('#skF_2',C_113) ),
    inference(resolution,[status(thm)],[c_52,c_1140])).

tff(c_1228,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_1216])).

tff(c_102,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [A_8,B_9] : k3_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k4_xboole_0(A_8,B_9) ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_1407,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_109])).

tff(c_1419,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1407])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2099,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_subset_1(A_8,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_14,c_2048])).

tff(c_2124,plain,(
    ! [A_8,B_9] : k3_subset_1(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2099])).

tff(c_2488,plain,(
    ! [A_8,B_9] :
      ( k3_subset_1(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9)
      | ~ r1_tarski(k4_xboole_0(A_8,B_9),A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2124,c_2466])).

tff(c_3493,plain,(
    ! [A_180,B_181] : k3_subset_1(A_180,k3_xboole_0(A_180,B_181)) = k4_xboole_0(A_180,B_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2488])).

tff(c_3520,plain,(
    k3_subset_1(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1419,c_3493])).

tff(c_3548,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_3520])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3895,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3548,c_16])).

tff(c_3909,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3895])).

tff(c_2660,plain,(
    ! [A_153,B_154] :
      ( k4_subset_1(u1_struct_0(A_153),B_154,k2_tops_1(A_153,B_154)) = k2_pre_topc(A_153,B_154)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2667,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2660])).

tff(c_2675,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2667])).

tff(c_44,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k2_tops_1(A_35,B_36),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1980,plain,(
    ! [A_134,B_135,C_136] :
      ( k4_subset_1(A_134,B_135,C_136) = k2_xboole_0(B_135,C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_134))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16037,plain,(
    ! [A_413,B_414,B_415] :
      ( k4_subset_1(u1_struct_0(A_413),B_414,k2_tops_1(A_413,B_415)) = k2_xboole_0(B_414,k2_tops_1(A_413,B_415))
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_pre_topc(A_413) ) ),
    inference(resolution,[status(thm)],[c_44,c_1980])).

tff(c_16044,plain,(
    ! [B_415] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_415)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_415))
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_16037])).

tff(c_18409,plain,(
    ! [B_445] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_445)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_445))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16044])).

tff(c_18420,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_18409])).

tff(c_18430,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3909,c_2675,c_18420])).

tff(c_18432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2423,c_18430])).

tff(c_18433,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_19513,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19393,c_18433])).

tff(c_18434,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_19602,plain,(
    ! [A_508,B_509] :
      ( k2_pre_topc(A_508,B_509) = B_509
      | ~ v4_pre_topc(B_509,A_508)
      | ~ m1_subset_1(B_509,k1_zfmisc_1(u1_struct_0(A_508)))
      | ~ l1_pre_topc(A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_19609,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_19602])).

tff(c_19617,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18434,c_19609])).

tff(c_21290,plain,(
    ! [A_562,B_563] :
      ( k7_subset_1(u1_struct_0(A_562),k2_pre_topc(A_562,B_563),k1_tops_1(A_562,B_563)) = k2_tops_1(A_562,B_563)
      | ~ m1_subset_1(B_563,k1_zfmisc_1(u1_struct_0(A_562)))
      | ~ l1_pre_topc(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_21299,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19617,c_21290])).

tff(c_21303,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_19393,c_21299])).

tff(c_21305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19513,c_21303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.17/3.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.17/3.53  
% 9.17/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.17/3.53  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.17/3.53  
% 9.17/3.53  %Foreground sorts:
% 9.17/3.53  
% 9.17/3.53  
% 9.17/3.53  %Background operators:
% 9.17/3.53  
% 9.17/3.53  
% 9.17/3.53  %Foreground operators:
% 9.17/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.17/3.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.17/3.53  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.17/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.17/3.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.17/3.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.17/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.17/3.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.17/3.53  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.17/3.53  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.17/3.53  tff('#skF_2', type, '#skF_2': $i).
% 9.17/3.53  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.17/3.53  tff('#skF_1', type, '#skF_1': $i).
% 9.17/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.17/3.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.17/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.17/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.17/3.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.17/3.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.17/3.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.17/3.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.17/3.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.17/3.53  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.17/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.17/3.53  
% 9.17/3.55  tff(f_132, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 9.17/3.55  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.17/3.55  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.17/3.55  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 9.17/3.55  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.17/3.55  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 9.17/3.55  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.17/3.55  tff(f_77, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.17/3.55  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 9.17/3.55  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.17/3.55  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.17/3.55  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.17/3.55  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.17/3.55  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 9.17/3.55  tff(f_98, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.17/3.55  tff(f_69, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.17/3.55  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 9.17/3.55  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.17/3.55  tff(c_19385, plain, (![A_498, B_499, C_500]: (k7_subset_1(A_498, B_499, C_500)=k4_xboole_0(B_499, C_500) | ~m1_subset_1(B_499, k1_zfmisc_1(A_498)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.17/3.55  tff(c_19393, plain, (![C_500]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_500)=k4_xboole_0('#skF_2', C_500))), inference(resolution, [status(thm)], [c_52, c_19385])).
% 9.17/3.55  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.17/3.55  tff(c_101, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 9.17/3.55  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.17/3.55  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.17/3.55  tff(c_2403, plain, (![B_147, A_148]: (v4_pre_topc(B_147, A_148) | k2_pre_topc(A_148, B_147)!=B_147 | ~v2_pre_topc(A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.17/3.55  tff(c_2413, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2403])).
% 9.17/3.55  tff(c_2422, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_2413])).
% 9.17/3.55  tff(c_2423, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_101, c_2422])).
% 9.17/3.55  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.17/3.55  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.17/3.55  tff(c_424, plain, (![A_78, B_79, C_80]: (r1_tarski(A_78, k2_xboole_0(B_79, C_80)) | ~r1_tarski(k4_xboole_0(A_78, B_79), C_80))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.17/3.55  tff(c_450, plain, (![A_81, B_82]: (r1_tarski(A_81, k2_xboole_0(B_82, A_81)))), inference(resolution, [status(thm)], [c_14, c_424])).
% 9.17/3.55  tff(c_471, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_10, c_450])).
% 9.17/3.55  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.17/3.55  tff(c_38, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.17/3.55  tff(c_953, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k3_subset_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.17/3.55  tff(c_2048, plain, (![B_139, A_140]: (k4_xboole_0(B_139, A_140)=k3_subset_1(B_139, A_140) | ~r1_tarski(A_140, B_139))), inference(resolution, [status(thm)], [c_38, c_953])).
% 9.17/3.55  tff(c_2087, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=k3_subset_1(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_471, c_2048])).
% 9.17/3.55  tff(c_2118, plain, (![A_5]: (k3_subset_1(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2087])).
% 9.17/3.55  tff(c_732, plain, (![A_92, B_93]: (k3_subset_1(A_92, k3_subset_1(A_92, B_93))=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.17/3.55  tff(c_2466, plain, (![B_149, A_150]: (k3_subset_1(B_149, k3_subset_1(B_149, A_150))=A_150 | ~r1_tarski(A_150, B_149))), inference(resolution, [status(thm)], [c_38, c_732])).
% 9.17/3.55  tff(c_2491, plain, (![A_5]: (k3_subset_1(A_5, A_5)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_2118, c_2466])).
% 9.17/3.55  tff(c_2523, plain, (![A_5]: (k3_subset_1(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_471, c_2491])).
% 9.17/3.55  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.17/3.55  tff(c_180, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_101, c_64])).
% 9.17/3.55  tff(c_1140, plain, (![A_108, B_109, C_110]: (k7_subset_1(A_108, B_109, C_110)=k4_xboole_0(B_109, C_110) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.17/3.55  tff(c_1216, plain, (![C_113]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_113)=k4_xboole_0('#skF_2', C_113))), inference(resolution, [status(thm)], [c_52, c_1140])).
% 9.17/3.55  tff(c_1228, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_180, c_1216])).
% 9.17/3.55  tff(c_102, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.17/3.55  tff(c_109, plain, (![A_8, B_9]: (k3_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k4_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_14, c_102])).
% 9.17/3.55  tff(c_1407, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1228, c_109])).
% 9.17/3.55  tff(c_1419, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_1407])).
% 9.17/3.55  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.17/3.55  tff(c_2099, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_subset_1(A_8, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_14, c_2048])).
% 9.17/3.55  tff(c_2124, plain, (![A_8, B_9]: (k3_subset_1(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2099])).
% 9.17/3.55  tff(c_2488, plain, (![A_8, B_9]: (k3_subset_1(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9) | ~r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_2124, c_2466])).
% 9.17/3.55  tff(c_3493, plain, (![A_180, B_181]: (k3_subset_1(A_180, k3_xboole_0(A_180, B_181))=k4_xboole_0(A_180, B_181))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2488])).
% 9.17/3.55  tff(c_3520, plain, (k3_subset_1(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1419, c_3493])).
% 9.17/3.55  tff(c_3548, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_3520])).
% 9.17/3.55  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.17/3.55  tff(c_3895, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3548, c_16])).
% 9.17/3.55  tff(c_3909, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3895])).
% 9.17/3.55  tff(c_2660, plain, (![A_153, B_154]: (k4_subset_1(u1_struct_0(A_153), B_154, k2_tops_1(A_153, B_154))=k2_pre_topc(A_153, B_154) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.17/3.55  tff(c_2667, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2660])).
% 9.17/3.55  tff(c_2675, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2667])).
% 9.17/3.55  tff(c_44, plain, (![A_35, B_36]: (m1_subset_1(k2_tops_1(A_35, B_36), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.17/3.55  tff(c_1980, plain, (![A_134, B_135, C_136]: (k4_subset_1(A_134, B_135, C_136)=k2_xboole_0(B_135, C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(A_134)) | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.17/3.55  tff(c_16037, plain, (![A_413, B_414, B_415]: (k4_subset_1(u1_struct_0(A_413), B_414, k2_tops_1(A_413, B_415))=k2_xboole_0(B_414, k2_tops_1(A_413, B_415)) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0(A_413))) | ~m1_subset_1(B_415, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_pre_topc(A_413))), inference(resolution, [status(thm)], [c_44, c_1980])).
% 9.17/3.55  tff(c_16044, plain, (![B_415]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_415))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_415)) | ~m1_subset_1(B_415, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_16037])).
% 9.17/3.55  tff(c_18409, plain, (![B_445]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_445))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_445)) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16044])).
% 9.17/3.55  tff(c_18420, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_18409])).
% 9.17/3.55  tff(c_18430, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3909, c_2675, c_18420])).
% 9.17/3.55  tff(c_18432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2423, c_18430])).
% 9.17/3.55  tff(c_18433, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 9.17/3.55  tff(c_19513, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19393, c_18433])).
% 9.17/3.55  tff(c_18434, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 9.17/3.55  tff(c_19602, plain, (![A_508, B_509]: (k2_pre_topc(A_508, B_509)=B_509 | ~v4_pre_topc(B_509, A_508) | ~m1_subset_1(B_509, k1_zfmisc_1(u1_struct_0(A_508))) | ~l1_pre_topc(A_508))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.17/3.55  tff(c_19609, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_19602])).
% 9.17/3.55  tff(c_19617, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18434, c_19609])).
% 9.17/3.55  tff(c_21290, plain, (![A_562, B_563]: (k7_subset_1(u1_struct_0(A_562), k2_pre_topc(A_562, B_563), k1_tops_1(A_562, B_563))=k2_tops_1(A_562, B_563) | ~m1_subset_1(B_563, k1_zfmisc_1(u1_struct_0(A_562))) | ~l1_pre_topc(A_562))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.17/3.55  tff(c_21299, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19617, c_21290])).
% 9.17/3.55  tff(c_21303, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_19393, c_21299])).
% 9.17/3.55  tff(c_21305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19513, c_21303])).
% 9.17/3.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.17/3.55  
% 9.17/3.55  Inference rules
% 9.17/3.55  ----------------------
% 9.17/3.55  #Ref     : 0
% 9.17/3.55  #Sup     : 5143
% 9.17/3.55  #Fact    : 0
% 9.17/3.55  #Define  : 0
% 9.17/3.55  #Split   : 5
% 9.17/3.55  #Chain   : 0
% 9.17/3.55  #Close   : 0
% 9.17/3.55  
% 9.17/3.55  Ordering : KBO
% 9.17/3.55  
% 9.17/3.55  Simplification rules
% 9.17/3.55  ----------------------
% 9.17/3.55  #Subsume      : 133
% 9.17/3.55  #Demod        : 4815
% 9.17/3.55  #Tautology    : 3706
% 9.17/3.55  #SimpNegUnit  : 6
% 9.17/3.55  #BackRed      : 59
% 9.17/3.55  
% 9.17/3.55  #Partial instantiations: 0
% 9.17/3.55  #Strategies tried      : 1
% 9.17/3.55  
% 9.17/3.55  Timing (in seconds)
% 9.17/3.55  ----------------------
% 9.17/3.55  Preprocessing        : 0.38
% 9.17/3.55  Parsing              : 0.21
% 9.17/3.55  CNF conversion       : 0.02
% 9.17/3.55  Main loop            : 2.33
% 9.17/3.55  Inferencing          : 0.57
% 9.17/3.55  Reduction            : 1.12
% 9.17/3.55  Demodulation         : 0.93
% 9.17/3.55  BG Simplification    : 0.06
% 9.17/3.55  Subsumption          : 0.43
% 9.17/3.55  Abstraction          : 0.10
% 9.17/3.55  MUC search           : 0.00
% 9.17/3.55  Cooper               : 0.00
% 9.17/3.55  Total                : 2.75
% 9.17/3.55  Index Insertion      : 0.00
% 9.17/3.55  Index Deletion       : 0.00
% 9.17/3.55  Index Matching       : 0.00
% 9.17/3.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
