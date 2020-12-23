%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:02 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 250 expanded)
%              Number of leaves         :   34 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 630 expanded)
%              Number of equality atoms :   44 ( 137 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_58,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_42,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_84,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_471,plain,(
    ! [B_65,A_66] :
      ( v2_tops_1(B_65,A_66)
      | k1_tops_1(A_66,B_65) != k1_xboole_0
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_474,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_471])).

tff(c_477,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_474])).

tff(c_478,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_479,plain,(
    ! [A_67,B_68] :
      ( k1_tops_1(A_67,B_68) = k1_xboole_0
      | ~ v2_tops_1(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_482,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_479])).

tff(c_485,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_482])).

tff(c_486,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_485])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_85,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_48])).

tff(c_487,plain,(
    ! [B_69,A_70] :
      ( v2_tops_1(B_69,A_70)
      | ~ r1_tarski(B_69,k2_tops_1(A_70,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_489,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_487])).

tff(c_491,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_8,c_489])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_491])).

tff(c_494,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_36,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_804,plain,(
    ! [B_81,A_82] :
      ( v3_tops_1(B_81,A_82)
      | ~ v4_pre_topc(B_81,A_82)
      | ~ v2_tops_1(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_807,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_804])).

tff(c_810,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_494,c_36,c_807])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_810])).

tff(c_813,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_814,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1028,plain,(
    ! [B_103,A_104] :
      ( v2_tops_1(B_103,A_104)
      | ~ v3_tops_1(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1031,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1028])).

tff(c_1034,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_814,c_1031])).

tff(c_1314,plain,(
    ! [B_117,A_118] :
      ( r1_tarski(B_117,k2_tops_1(A_118,B_117))
      | ~ v2_tops_1(B_117,A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1316,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1314])).

tff(c_1319,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1034,c_1316])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1333,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1319,c_10])).

tff(c_874,plain,(
    ! [A_92,B_93,C_94] :
      ( k7_subset_1(A_92,B_93,C_94) = k4_xboole_0(B_93,C_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_877,plain,(
    ! [C_94] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_94) = k4_xboole_0('#skF_2',C_94) ),
    inference(resolution,[status(thm)],[c_38,c_874])).

tff(c_1194,plain,(
    ! [A_111,B_112] :
      ( k2_pre_topc(A_111,B_112) = B_112
      | ~ v4_pre_topc(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1197,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1194])).

tff(c_1200,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1197])).

tff(c_1205,plain,(
    ! [A_113,B_114] :
      ( k1_tops_1(A_113,B_114) = k1_xboole_0
      | ~ v2_tops_1(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1208,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1205])).

tff(c_1211,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1034,c_1208])).

tff(c_1931,plain,(
    ! [A_134,B_135] :
      ( k7_subset_1(u1_struct_0(A_134),k2_pre_topc(A_134,B_135),k1_tops_1(A_134,B_135)) = k2_tops_1(A_134,B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1940,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_1931])).

tff(c_1947,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_877,c_1200,c_1940])).

tff(c_939,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(k1_tops_1(A_99,B_100),B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_941,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_939])).

tff(c_944,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_941])).

tff(c_951,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_944,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_822,plain,(
    ! [A_85,B_86] : k4_xboole_0(A_85,k4_xboole_0(A_85,B_86)) = k3_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_853,plain,(
    ! [A_90,B_91] : k4_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,k4_xboole_0(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_822])).

tff(c_871,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_853])).

tff(c_955,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_871])).

tff(c_1213,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_xboole_0)) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1211,c_1211,c_955])).

tff(c_1950,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1947,c_1947,c_1213])).

tff(c_1951,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1333,c_1950])).

tff(c_1953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_813,c_1951])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.69  
% 4.13/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.69  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.13/1.69  
% 4.13/1.69  %Foreground sorts:
% 4.13/1.69  
% 4.13/1.69  
% 4.13/1.69  %Background operators:
% 4.13/1.69  
% 4.13/1.69  
% 4.13/1.69  %Foreground operators:
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.13/1.69  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.13/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.69  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.13/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.13/1.69  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.13/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.69  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.13/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.69  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.13/1.69  tff('#skF_1', type, '#skF_1': $i).
% 4.13/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.69  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.13/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.13/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.13/1.70  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.13/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.70  
% 4.13/1.71  tff(f_122, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 4.13/1.71  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.13/1.71  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.13/1.71  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 4.13/1.71  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 4.13/1.71  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 4.13/1.71  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.13/1.71  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.13/1.71  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.13/1.71  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.13/1.71  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.13/1.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.13/1.71  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.13/1.71  tff(c_42, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.13/1.71  tff(c_84, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.13/1.71  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.13/1.71  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.13/1.71  tff(c_471, plain, (![B_65, A_66]: (v2_tops_1(B_65, A_66) | k1_tops_1(A_66, B_65)!=k1_xboole_0 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.13/1.71  tff(c_474, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_471])).
% 4.13/1.71  tff(c_477, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_474])).
% 4.13/1.71  tff(c_478, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_477])).
% 4.13/1.71  tff(c_479, plain, (![A_67, B_68]: (k1_tops_1(A_67, B_68)=k1_xboole_0 | ~v2_tops_1(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.13/1.71  tff(c_482, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_479])).
% 4.13/1.71  tff(c_485, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_482])).
% 4.13/1.71  tff(c_486, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_478, c_485])).
% 4.13/1.71  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.13/1.71  tff(c_48, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.13/1.71  tff(c_85, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_84, c_48])).
% 4.13/1.71  tff(c_487, plain, (![B_69, A_70]: (v2_tops_1(B_69, A_70) | ~r1_tarski(B_69, k2_tops_1(A_70, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.13/1.71  tff(c_489, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_85, c_487])).
% 4.13/1.71  tff(c_491, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_8, c_489])).
% 4.13/1.71  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_486, c_491])).
% 4.13/1.71  tff(c_494, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_477])).
% 4.13/1.71  tff(c_36, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.13/1.71  tff(c_804, plain, (![B_81, A_82]: (v3_tops_1(B_81, A_82) | ~v4_pre_topc(B_81, A_82) | ~v2_tops_1(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.13/1.71  tff(c_807, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_804])).
% 4.13/1.71  tff(c_810, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_494, c_36, c_807])).
% 4.13/1.71  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_810])).
% 4.13/1.71  tff(c_813, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 4.13/1.71  tff(c_814, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.13/1.71  tff(c_1028, plain, (![B_103, A_104]: (v2_tops_1(B_103, A_104) | ~v3_tops_1(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.71  tff(c_1031, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1028])).
% 4.13/1.71  tff(c_1034, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_814, c_1031])).
% 4.13/1.71  tff(c_1314, plain, (![B_117, A_118]: (r1_tarski(B_117, k2_tops_1(A_118, B_117)) | ~v2_tops_1(B_117, A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.13/1.71  tff(c_1316, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1314])).
% 4.13/1.71  tff(c_1319, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1034, c_1316])).
% 4.13/1.71  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.13/1.71  tff(c_1333, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_1319, c_10])).
% 4.13/1.71  tff(c_874, plain, (![A_92, B_93, C_94]: (k7_subset_1(A_92, B_93, C_94)=k4_xboole_0(B_93, C_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.71  tff(c_877, plain, (![C_94]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_94)=k4_xboole_0('#skF_2', C_94))), inference(resolution, [status(thm)], [c_38, c_874])).
% 4.13/1.71  tff(c_1194, plain, (![A_111, B_112]: (k2_pre_topc(A_111, B_112)=B_112 | ~v4_pre_topc(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.13/1.71  tff(c_1197, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1194])).
% 4.13/1.71  tff(c_1200, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1197])).
% 4.13/1.71  tff(c_1205, plain, (![A_113, B_114]: (k1_tops_1(A_113, B_114)=k1_xboole_0 | ~v2_tops_1(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.13/1.71  tff(c_1208, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1205])).
% 4.13/1.71  tff(c_1211, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1034, c_1208])).
% 4.13/1.71  tff(c_1931, plain, (![A_134, B_135]: (k7_subset_1(u1_struct_0(A_134), k2_pre_topc(A_134, B_135), k1_tops_1(A_134, B_135))=k2_tops_1(A_134, B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.13/1.71  tff(c_1940, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1211, c_1931])).
% 4.13/1.71  tff(c_1947, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_877, c_1200, c_1940])).
% 4.13/1.71  tff(c_939, plain, (![A_99, B_100]: (r1_tarski(k1_tops_1(A_99, B_100), B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.13/1.71  tff(c_941, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_939])).
% 4.13/1.71  tff(c_944, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_941])).
% 4.13/1.71  tff(c_951, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_944, c_10])).
% 4.13/1.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.13/1.71  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.13/1.71  tff(c_822, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k4_xboole_0(A_85, B_86))=k3_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.13/1.71  tff(c_853, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k3_xboole_0(A_90, k4_xboole_0(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_822])).
% 4.13/1.71  tff(c_871, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_853])).
% 4.13/1.71  tff(c_955, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_951, c_871])).
% 4.13/1.71  tff(c_1213, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_xboole_0))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1211, c_1211, c_955])).
% 4.13/1.71  tff(c_1950, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1947, c_1947, c_1213])).
% 4.13/1.71  tff(c_1951, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1333, c_1950])).
% 4.13/1.71  tff(c_1953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_813, c_1951])).
% 4.13/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.71  
% 4.13/1.71  Inference rules
% 4.13/1.71  ----------------------
% 4.13/1.71  #Ref     : 0
% 4.13/1.71  #Sup     : 487
% 4.13/1.71  #Fact    : 0
% 4.13/1.71  #Define  : 0
% 4.13/1.71  #Split   : 4
% 4.13/1.71  #Chain   : 0
% 4.13/1.71  #Close   : 0
% 4.13/1.71  
% 4.13/1.71  Ordering : KBO
% 4.13/1.71  
% 4.13/1.71  Simplification rules
% 4.13/1.71  ----------------------
% 4.13/1.71  #Subsume      : 12
% 4.13/1.71  #Demod        : 662
% 4.13/1.71  #Tautology    : 327
% 4.13/1.71  #SimpNegUnit  : 7
% 4.13/1.71  #BackRed      : 13
% 4.13/1.71  
% 4.13/1.71  #Partial instantiations: 0
% 4.13/1.71  #Strategies tried      : 1
% 4.13/1.71  
% 4.13/1.71  Timing (in seconds)
% 4.13/1.71  ----------------------
% 4.13/1.71  Preprocessing        : 0.33
% 4.13/1.71  Parsing              : 0.17
% 4.13/1.71  CNF conversion       : 0.02
% 4.13/1.72  Main loop            : 0.62
% 4.13/1.72  Inferencing          : 0.20
% 4.13/1.72  Reduction            : 0.28
% 4.13/1.72  Demodulation         : 0.24
% 4.13/1.72  BG Simplification    : 0.03
% 4.13/1.72  Subsumption          : 0.08
% 4.13/1.72  Abstraction          : 0.03
% 4.13/1.72  MUC search           : 0.00
% 4.13/1.72  Cooper               : 0.00
% 4.13/1.72  Total                : 0.98
% 4.13/1.72  Index Insertion      : 0.00
% 4.13/1.72  Index Deletion       : 0.00
% 4.13/1.72  Index Matching       : 0.00
% 4.13/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
