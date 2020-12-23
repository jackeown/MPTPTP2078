%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:48 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 272 expanded)
%              Number of leaves         :   24 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  170 ( 883 expanded)
%              Number of equality atoms :   40 ( 183 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( v3_pre_topc(D,B)
                       => k1_tops_1(B,D) = D )
                      & ( k1_tops_1(A,C) = C
                       => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_35,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_43,plain,(
    ! [A_29,B_30] :
      ( k3_subset_1(A_29,k3_subset_1(A_29,B_30)) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_185,plain,(
    ! [A_41,B_42] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_41),B_42),A_41)
      | ~ v4_pre_topc(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_195,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_185])).

tff(c_201,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_195])).

tff(c_202,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_201])).

tff(c_205,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_208,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_205])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_208])).

tff(c_213,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_214,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_8,plain,(
    ! [B_9,A_7] :
      ( v4_pre_topc(B_9,A_7)
      | k2_pre_topc(A_7,B_9) != B_9
      | ~ v2_pre_topc(A_7)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_217,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_214,c_8])).

tff(c_225,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_217])).

tff(c_226,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_225])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( k3_subset_1(u1_struct_0(A_10),k2_pre_topc(A_10,k3_subset_1(u1_struct_0(A_10),B_12))) = k1_tops_1(A_10,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_61,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_pre_topc(A_31,B_32),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_subset_1(A_3,k3_subset_1(A_3,B_4)) = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_370,plain,(
    ! [A_47,B_48] :
      ( k3_subset_1(u1_struct_0(A_47),k3_subset_1(u1_struct_0(A_47),k2_pre_topc(A_47,B_48))) = k2_pre_topc(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_61,c_4])).

tff(c_3199,plain,(
    ! [A_81,B_82] :
      ( k3_subset_1(u1_struct_0(A_81),k1_tops_1(A_81,B_82)) = k2_pre_topc(A_81,k3_subset_1(u1_struct_0(A_81),B_82))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_81),B_82),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_370])).

tff(c_3280,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_3')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_214,c_3199])).

tff(c_3344,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_36,c_3280])).

tff(c_3346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_3344])).

tff(c_3348,plain,(
    k1_tops_1('#skF_1','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3349,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3348,c_32])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3351,plain,(
    ! [A_85,B_86] :
      ( k3_subset_1(A_85,k3_subset_1(A_85,B_86)) = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3359,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_3351])).

tff(c_3347,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3522,plain,(
    ! [B_97,A_98] :
      ( v4_pre_topc(B_97,A_98)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_98),B_97),A_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3535,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3359,c_3522])).

tff(c_3541,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3347,c_3535])).

tff(c_3542,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3541])).

tff(c_3545,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2,c_3542])).

tff(c_3549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3545])).

tff(c_3550,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3541])).

tff(c_3551,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3541])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( k2_pre_topc(A_7,B_9) = B_9
      | ~ v4_pre_topc(B_9,A_7)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3598,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3551,c_10])).

tff(c_3606,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3550,c_3598])).

tff(c_3612,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3606,c_12])).

tff(c_3619,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_3359,c_3612])).

tff(c_3621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3349,c_3619])).

tff(c_3623,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3624,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_3626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3623,c_3624])).

tff(c_3627,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3632,plain,(
    ! [A_103,B_104] :
      ( k3_subset_1(A_103,k3_subset_1(A_103,B_104)) = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3640,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_3632])).

tff(c_3622,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_3774,plain,(
    ! [B_115,A_116] :
      ( v4_pre_topc(B_115,A_116)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_116),B_115),A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3787,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3640,c_3774])).

tff(c_3792,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3622,c_3787])).

tff(c_3860,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3792])).

tff(c_3863,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2,c_3860])).

tff(c_3867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3863])).

tff(c_3868,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3792])).

tff(c_3869,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3792])).

tff(c_3875,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3869,c_10])).

tff(c_3883,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3868,c_3875])).

tff(c_3904,plain,(
    ! [A_119,B_120] :
      ( k3_subset_1(u1_struct_0(A_119),k2_pre_topc(A_119,k3_subset_1(u1_struct_0(A_119),B_120))) = k1_tops_1(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3931,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3883,c_3904])).

tff(c_3948,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_3640,c_3931])).

tff(c_3950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3627,c_3948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:20:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/2.03  
% 5.29/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/2.04  %$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.29/2.04  
% 5.29/2.04  %Foreground sorts:
% 5.29/2.04  
% 5.29/2.04  
% 5.29/2.04  %Background operators:
% 5.29/2.04  
% 5.29/2.04  
% 5.29/2.04  %Foreground operators:
% 5.29/2.04  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.29/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.29/2.04  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.29/2.04  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.29/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.29/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.29/2.04  tff('#skF_1', type, '#skF_1': $i).
% 5.29/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/2.04  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.29/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.29/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.29/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.29/2.04  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.29/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/2.04  
% 5.65/2.05  tff(f_92, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 5.65/2.05  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.65/2.05  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.65/2.05  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 5.65/2.05  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.65/2.05  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 5.65/2.05  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.65/2.05  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.65/2.05  tff(c_30, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_35, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 5.65/2.05  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_43, plain, (![A_29, B_30]: (k3_subset_1(A_29, k3_subset_1(A_29, B_30))=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.65/2.05  tff(c_52, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_20, c_43])).
% 5.65/2.05  tff(c_185, plain, (![A_41, B_42]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_41), B_42), A_41) | ~v4_pre_topc(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.65/2.05  tff(c_195, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_52, c_185])).
% 5.65/2.05  tff(c_201, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_195])).
% 5.65/2.05  tff(c_202, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_35, c_201])).
% 5.65/2.05  tff(c_205, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_202])).
% 5.65/2.05  tff(c_208, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_205])).
% 5.65/2.05  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_208])).
% 5.65/2.05  tff(c_213, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_202])).
% 5.65/2.05  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_214, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_202])).
% 5.65/2.05  tff(c_8, plain, (![B_9, A_7]: (v4_pre_topc(B_9, A_7) | k2_pre_topc(A_7, B_9)!=B_9 | ~v2_pre_topc(A_7) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.65/2.05  tff(c_217, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_214, c_8])).
% 5.65/2.05  tff(c_225, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_217])).
% 5.65/2.05  tff(c_226, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_213, c_225])).
% 5.65/2.05  tff(c_34, plain, (v3_pre_topc('#skF_4', '#skF_2') | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_36, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 5.65/2.05  tff(c_12, plain, (![A_10, B_12]: (k3_subset_1(u1_struct_0(A_10), k2_pre_topc(A_10, k3_subset_1(u1_struct_0(A_10), B_12)))=k1_tops_1(A_10, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.65/2.05  tff(c_61, plain, (![A_31, B_32]: (m1_subset_1(k2_pre_topc(A_31, B_32), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.65/2.05  tff(c_4, plain, (![A_3, B_4]: (k3_subset_1(A_3, k3_subset_1(A_3, B_4))=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.65/2.05  tff(c_370, plain, (![A_47, B_48]: (k3_subset_1(u1_struct_0(A_47), k3_subset_1(u1_struct_0(A_47), k2_pre_topc(A_47, B_48)))=k2_pre_topc(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_61, c_4])).
% 5.65/2.05  tff(c_3199, plain, (![A_81, B_82]: (k3_subset_1(u1_struct_0(A_81), k1_tops_1(A_81, B_82))=k2_pre_topc(A_81, k3_subset_1(u1_struct_0(A_81), B_82)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_81), B_82), k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(superposition, [status(thm), theory('equality')], [c_12, c_370])).
% 5.65/2.05  tff(c_3280, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_3'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_214, c_3199])).
% 5.65/2.05  tff(c_3344, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_36, c_3280])).
% 5.65/2.05  tff(c_3346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_3344])).
% 5.65/2.05  tff(c_3348, plain, (k1_tops_1('#skF_1', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 5.65/2.05  tff(c_32, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_3349, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3348, c_32])).
% 5.65/2.05  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_3351, plain, (![A_85, B_86]: (k3_subset_1(A_85, k3_subset_1(A_85, B_86))=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.65/2.05  tff(c_3359, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_18, c_3351])).
% 5.65/2.05  tff(c_3347, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 5.65/2.05  tff(c_3522, plain, (![B_97, A_98]: (v4_pre_topc(B_97, A_98) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_98), B_97), A_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.65/2.05  tff(c_3535, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3359, c_3522])).
% 5.65/2.05  tff(c_3541, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3347, c_3535])).
% 5.65/2.05  tff(c_3542, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3541])).
% 5.65/2.05  tff(c_3545, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2, c_3542])).
% 5.65/2.05  tff(c_3549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_3545])).
% 5.65/2.05  tff(c_3550, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_3541])).
% 5.65/2.05  tff(c_3551, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3541])).
% 5.65/2.05  tff(c_10, plain, (![A_7, B_9]: (k2_pre_topc(A_7, B_9)=B_9 | ~v4_pre_topc(B_9, A_7) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.65/2.05  tff(c_3598, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3551, c_10])).
% 5.65/2.05  tff(c_3606, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3550, c_3598])).
% 5.65/2.05  tff(c_3612, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3606, c_12])).
% 5.65/2.05  tff(c_3619, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_3359, c_3612])).
% 5.65/2.05  tff(c_3621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3349, c_3619])).
% 5.65/2.05  tff(c_3623, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 5.65/2.05  tff(c_28, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.65/2.05  tff(c_3624, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 5.65/2.05  tff(c_3626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3623, c_3624])).
% 5.65/2.05  tff(c_3627, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 5.65/2.05  tff(c_3632, plain, (![A_103, B_104]: (k3_subset_1(A_103, k3_subset_1(A_103, B_104))=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.65/2.05  tff(c_3640, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_18, c_3632])).
% 5.65/2.05  tff(c_3622, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 5.65/2.05  tff(c_3774, plain, (![B_115, A_116]: (v4_pre_topc(B_115, A_116) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_116), B_115), A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.65/2.05  tff(c_3787, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3640, c_3774])).
% 5.65/2.05  tff(c_3792, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3622, c_3787])).
% 5.65/2.05  tff(c_3860, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3792])).
% 5.65/2.05  tff(c_3863, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2, c_3860])).
% 5.65/2.05  tff(c_3867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_3863])).
% 5.65/2.05  tff(c_3868, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_3792])).
% 5.65/2.05  tff(c_3869, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3792])).
% 5.65/2.05  tff(c_3875, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3869, c_10])).
% 5.65/2.05  tff(c_3883, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3868, c_3875])).
% 5.65/2.05  tff(c_3904, plain, (![A_119, B_120]: (k3_subset_1(u1_struct_0(A_119), k2_pre_topc(A_119, k3_subset_1(u1_struct_0(A_119), B_120)))=k1_tops_1(A_119, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.65/2.05  tff(c_3931, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3883, c_3904])).
% 5.65/2.05  tff(c_3948, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_3640, c_3931])).
% 5.65/2.05  tff(c_3950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3627, c_3948])).
% 5.65/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.65/2.05  
% 5.65/2.05  Inference rules
% 5.65/2.05  ----------------------
% 5.65/2.05  #Ref     : 0
% 5.65/2.05  #Sup     : 840
% 5.65/2.05  #Fact    : 0
% 5.65/2.05  #Define  : 0
% 5.65/2.05  #Split   : 44
% 5.65/2.05  #Chain   : 0
% 5.65/2.05  #Close   : 0
% 5.65/2.05  
% 5.65/2.05  Ordering : KBO
% 5.65/2.05  
% 5.65/2.05  Simplification rules
% 5.65/2.05  ----------------------
% 5.65/2.05  #Subsume      : 106
% 5.65/2.05  #Demod        : 1321
% 5.65/2.05  #Tautology    : 223
% 5.65/2.05  #SimpNegUnit  : 76
% 5.65/2.05  #BackRed      : 1
% 5.65/2.05  
% 5.65/2.05  #Partial instantiations: 0
% 5.65/2.05  #Strategies tried      : 1
% 5.65/2.05  
% 5.65/2.05  Timing (in seconds)
% 5.65/2.05  ----------------------
% 5.65/2.06  Preprocessing        : 0.31
% 5.65/2.06  Parsing              : 0.17
% 5.65/2.06  CNF conversion       : 0.02
% 5.65/2.06  Main loop            : 0.98
% 5.65/2.06  Inferencing          : 0.29
% 5.65/2.06  Reduction            : 0.41
% 5.65/2.06  Demodulation         : 0.30
% 5.65/2.06  BG Simplification    : 0.04
% 5.65/2.06  Subsumption          : 0.18
% 5.65/2.06  Abstraction          : 0.05
% 5.65/2.06  MUC search           : 0.00
% 5.65/2.06  Cooper               : 0.00
% 5.65/2.06  Total                : 1.33
% 5.65/2.06  Index Insertion      : 0.00
% 5.65/2.06  Index Deletion       : 0.00
% 5.65/2.06  Index Matching       : 0.00
% 5.65/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
