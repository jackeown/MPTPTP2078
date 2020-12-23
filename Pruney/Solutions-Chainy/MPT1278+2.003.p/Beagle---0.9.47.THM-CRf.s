%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:08 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 726 expanded)
%              Number of leaves         :   38 ( 256 expanded)
%              Depth                    :   18
%              Number of atoms          :  232 (1731 expanded)
%              Number of equality atoms :   50 ( 345 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tops_1)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_67,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_287,plain,(
    ! [B_70,A_71] :
      ( v3_pre_topc(B_70,A_71)
      | ~ v1_xboole_0(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_298,plain,(
    ! [A_71] :
      ( v3_pre_topc(k1_xboole_0,A_71)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_16,c_287])).

tff(c_309,plain,(
    ! [A_71] :
      ( v3_pre_topc(k1_xboole_0,A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_298])).

tff(c_222,plain,(
    ! [B_59,A_60] :
      ( v3_tops_1(B_59,A_60)
      | ~ v1_xboole_0(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_233,plain,(
    ! [A_60] :
      ( v3_tops_1(k1_xboole_0,A_60)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_16,c_222])).

tff(c_244,plain,(
    ! [A_60] :
      ( v3_tops_1(k1_xboole_0,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_233])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_127,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k3_subset_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = k3_subset_1(A_10,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_127])).

tff(c_139,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_133])).

tff(c_747,plain,(
    ! [A_109,B_110] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_109),B_110),A_109)
      | ~ v3_tops_1(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_759,plain,(
    ! [A_109] :
      ( v1_tops_1(u1_struct_0(A_109),A_109)
      | ~ v3_tops_1(k1_xboole_0,A_109)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_747])).

tff(c_775,plain,(
    ! [A_112] :
      ( v1_tops_1(u1_struct_0(A_112),A_112)
      | ~ v3_tops_1(k1_xboole_0,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_759])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_335,plain,(
    ! [A_75,B_76] :
      ( k2_pre_topc(A_75,B_76) = k2_struct_0(A_75)
      | ~ v1_tops_1(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_357,plain,(
    ! [A_75] :
      ( k2_pre_topc(A_75,u1_struct_0(A_75)) = k2_struct_0(A_75)
      | ~ v1_tops_1(u1_struct_0(A_75),A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_53,c_335])).

tff(c_809,plain,(
    ! [A_116] :
      ( k2_pre_topc(A_116,u1_struct_0(A_116)) = k2_struct_0(A_116)
      | ~ v3_tops_1(k1_xboole_0,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_775,c_357])).

tff(c_494,plain,(
    ! [A_93,B_94] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_93),B_94),A_93)
      | ~ v3_pre_topc(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_509,plain,(
    ! [A_93] :
      ( v4_pre_topc(u1_struct_0(A_93),A_93)
      | ~ v3_pre_topc(k1_xboole_0,A_93)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_494])).

tff(c_530,plain,(
    ! [A_96] :
      ( v4_pre_topc(u1_struct_0(A_96),A_96)
      | ~ v3_pre_topc(k1_xboole_0,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_509])).

tff(c_262,plain,(
    ! [A_66,B_67] :
      ( k2_pre_topc(A_66,B_67) = B_67
      | ~ v4_pre_topc(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_283,plain,(
    ! [A_66] :
      ( k2_pre_topc(A_66,u1_struct_0(A_66)) = u1_struct_0(A_66)
      | ~ v4_pre_topc(u1_struct_0(A_66),A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_53,c_262])).

tff(c_538,plain,(
    ! [A_96] :
      ( k2_pre_topc(A_96,u1_struct_0(A_96)) = u1_struct_0(A_96)
      | ~ v3_pre_topc(k1_xboole_0,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_530,c_283])).

tff(c_824,plain,(
    ! [A_117] :
      ( u1_struct_0(A_117) = k2_struct_0(A_117)
      | ~ v3_pre_topc(k1_xboole_0,A_117)
      | ~ l1_pre_topc(A_117)
      | ~ v3_tops_1(k1_xboole_0,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_538])).

tff(c_829,plain,(
    ! [A_118] :
      ( u1_struct_0(A_118) = k2_struct_0(A_118)
      | ~ v3_pre_topc(k1_xboole_0,A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_244,c_824])).

tff(c_835,plain,(
    ! [A_119] :
      ( u1_struct_0(A_119) = k2_struct_0(A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_309,c_829])).

tff(c_838,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_835])).

tff(c_841,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_838])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_269,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_262])).

tff(c_281,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_269])).

tff(c_284,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_74,plain,(
    ! [A_40,B_41] :
      ( k3_subset_1(A_40,k3_subset_1(A_40,B_41)) = B_41
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_74])).

tff(c_512,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_494])).

tff(c_519,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_512])).

tff(c_520,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_519])).

tff(c_540,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_543,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_540])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_543])).

tff(c_549,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_46,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_709,plain,(
    ! [B_107,A_108] :
      ( v4_pre_topc(B_107,A_108)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_108),B_107),A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_727,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_709])).

tff(c_734,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_549,c_46,c_727])).

tff(c_845,plain,(
    v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_734])).

tff(c_44,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_684,plain,(
    ! [A_105,B_106] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_105),B_106),A_105)
      | ~ v3_tops_1(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    ! [A_23,B_25] :
      ( k2_pre_topc(A_23,B_25) = k2_struct_0(A_23)
      | ~ v1_tops_1(B_25,A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_557,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_549,c_30])).

tff(c_584,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_557])).

tff(c_650,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_584])).

tff(c_687,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_684,c_650])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_687])).

tff(c_707,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_584])).

tff(c_843,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_707])).

tff(c_848,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_841,c_549])).

tff(c_22,plain,(
    ! [A_14,B_16] :
      ( k2_pre_topc(A_14,B_16) = B_16
      | ~ v4_pre_topc(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_933,plain,(
    ! [B_16] :
      ( k2_pre_topc('#skF_1',B_16) = B_16
      | ~ v4_pre_topc(B_16,'#skF_1')
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_22])).

tff(c_1386,plain,(
    ! [B_138] :
      ( k2_pre_topc('#skF_1',B_138) = B_138
      | ~ v4_pre_topc(B_138,'#skF_1')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_933])).

tff(c_1389,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_848,c_1386])).

tff(c_1407,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_843,c_1389])).

tff(c_197,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k3_subset_1(A_57,B_58),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k3_subset_1(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_474,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(A_91,k3_subset_1(A_91,B_92)) = k3_subset_1(A_91,k3_subset_1(A_91,B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_197,c_8])).

tff(c_478,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_474])).

tff(c_485,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_478])).

tff(c_850,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_841,c_485])).

tff(c_1417,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_850])).

tff(c_82,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_141,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_82])).

tff(c_140,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_subset_1(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_53,c_127])).

tff(c_175,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_140])).

tff(c_1452,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_175])).

tff(c_1458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.54  
% 3.63/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.55  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.63/1.55  
% 3.63/1.55  %Foreground sorts:
% 3.63/1.55  
% 3.63/1.55  
% 3.63/1.55  %Background operators:
% 3.63/1.55  
% 3.63/1.55  
% 3.63/1.55  %Foreground operators:
% 3.63/1.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.63/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.63/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.63/1.55  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.63/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.63/1.55  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.63/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.63/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.55  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.63/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.63/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.63/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.63/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.63/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.63/1.55  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.63/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.55  
% 3.63/1.57  tff(f_139, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 3.63/1.57  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.63/1.57  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.63/1.57  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 3.63/1.57  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_tops_1)).
% 3.63/1.57  tff(f_28, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.63/1.57  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.63/1.57  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 3.63/1.57  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.63/1.57  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.63/1.57  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.63/1.57  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 3.63/1.57  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.63/1.57  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.63/1.57  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.63/1.57  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 3.63/1.57  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.57  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.57  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.57  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.63/1.57  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.63/1.57  tff(c_287, plain, (![B_70, A_71]: (v3_pre_topc(B_70, A_71) | ~v1_xboole_0(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.63/1.57  tff(c_298, plain, (![A_71]: (v3_pre_topc(k1_xboole_0, A_71) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(resolution, [status(thm)], [c_16, c_287])).
% 3.63/1.57  tff(c_309, plain, (![A_71]: (v3_pre_topc(k1_xboole_0, A_71) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_298])).
% 3.63/1.57  tff(c_222, plain, (![B_59, A_60]: (v3_tops_1(B_59, A_60) | ~v1_xboole_0(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.63/1.57  tff(c_233, plain, (![A_60]: (v3_tops_1(k1_xboole_0, A_60) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(resolution, [status(thm)], [c_16, c_222])).
% 3.63/1.57  tff(c_244, plain, (![A_60]: (v3_tops_1(k1_xboole_0, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_233])).
% 3.63/1.57  tff(c_4, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.63/1.57  tff(c_127, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k3_subset_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.63/1.57  tff(c_133, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=k3_subset_1(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_127])).
% 3.63/1.57  tff(c_139, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_133])).
% 3.63/1.57  tff(c_747, plain, (![A_109, B_110]: (v1_tops_1(k3_subset_1(u1_struct_0(A_109), B_110), A_109) | ~v3_tops_1(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.63/1.57  tff(c_759, plain, (![A_109]: (v1_tops_1(u1_struct_0(A_109), A_109) | ~v3_tops_1(k1_xboole_0, A_109) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(superposition, [status(thm), theory('equality')], [c_139, c_747])).
% 3.63/1.57  tff(c_775, plain, (![A_112]: (v1_tops_1(u1_struct_0(A_112), A_112) | ~v3_tops_1(k1_xboole_0, A_112) | ~l1_pre_topc(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_759])).
% 3.63/1.57  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.63/1.57  tff(c_10, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.63/1.57  tff(c_53, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 3.63/1.57  tff(c_335, plain, (![A_75, B_76]: (k2_pre_topc(A_75, B_76)=k2_struct_0(A_75) | ~v1_tops_1(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.63/1.57  tff(c_357, plain, (![A_75]: (k2_pre_topc(A_75, u1_struct_0(A_75))=k2_struct_0(A_75) | ~v1_tops_1(u1_struct_0(A_75), A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_53, c_335])).
% 3.63/1.57  tff(c_809, plain, (![A_116]: (k2_pre_topc(A_116, u1_struct_0(A_116))=k2_struct_0(A_116) | ~v3_tops_1(k1_xboole_0, A_116) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_775, c_357])).
% 3.63/1.57  tff(c_494, plain, (![A_93, B_94]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_93), B_94), A_93) | ~v3_pre_topc(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.63/1.57  tff(c_509, plain, (![A_93]: (v4_pre_topc(u1_struct_0(A_93), A_93) | ~v3_pre_topc(k1_xboole_0, A_93) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(superposition, [status(thm), theory('equality')], [c_139, c_494])).
% 3.63/1.57  tff(c_530, plain, (![A_96]: (v4_pre_topc(u1_struct_0(A_96), A_96) | ~v3_pre_topc(k1_xboole_0, A_96) | ~l1_pre_topc(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_509])).
% 3.63/1.57  tff(c_262, plain, (![A_66, B_67]: (k2_pre_topc(A_66, B_67)=B_67 | ~v4_pre_topc(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.63/1.57  tff(c_283, plain, (![A_66]: (k2_pre_topc(A_66, u1_struct_0(A_66))=u1_struct_0(A_66) | ~v4_pre_topc(u1_struct_0(A_66), A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_53, c_262])).
% 3.63/1.57  tff(c_538, plain, (![A_96]: (k2_pre_topc(A_96, u1_struct_0(A_96))=u1_struct_0(A_96) | ~v3_pre_topc(k1_xboole_0, A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_530, c_283])).
% 3.63/1.57  tff(c_824, plain, (![A_117]: (u1_struct_0(A_117)=k2_struct_0(A_117) | ~v3_pre_topc(k1_xboole_0, A_117) | ~l1_pre_topc(A_117) | ~v3_tops_1(k1_xboole_0, A_117) | ~l1_pre_topc(A_117))), inference(superposition, [status(thm), theory('equality')], [c_809, c_538])).
% 3.63/1.57  tff(c_829, plain, (![A_118]: (u1_struct_0(A_118)=k2_struct_0(A_118) | ~v3_pre_topc(k1_xboole_0, A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(resolution, [status(thm)], [c_244, c_824])).
% 3.63/1.57  tff(c_835, plain, (![A_119]: (u1_struct_0(A_119)=k2_struct_0(A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(resolution, [status(thm)], [c_309, c_829])).
% 3.63/1.57  tff(c_838, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_835])).
% 3.63/1.57  tff(c_841, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_838])).
% 3.63/1.57  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.57  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.63/1.57  tff(c_269, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_262])).
% 3.63/1.57  tff(c_281, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_269])).
% 3.63/1.57  tff(c_284, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_281])).
% 3.63/1.57  tff(c_74, plain, (![A_40, B_41]: (k3_subset_1(A_40, k3_subset_1(A_40, B_41))=B_41 | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.63/1.57  tff(c_81, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_48, c_74])).
% 3.63/1.57  tff(c_512, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_81, c_494])).
% 3.63/1.57  tff(c_519, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_512])).
% 3.63/1.57  tff(c_520, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_284, c_519])).
% 3.63/1.57  tff(c_540, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_520])).
% 3.63/1.57  tff(c_543, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_540])).
% 3.63/1.57  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_543])).
% 3.63/1.57  tff(c_549, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_520])).
% 3.63/1.57  tff(c_46, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.57  tff(c_709, plain, (![B_107, A_108]: (v4_pre_topc(B_107, A_108) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_108), B_107), A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.63/1.57  tff(c_727, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_81, c_709])).
% 3.63/1.57  tff(c_734, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_549, c_46, c_727])).
% 3.63/1.57  tff(c_845, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_841, c_734])).
% 3.63/1.57  tff(c_44, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.63/1.57  tff(c_684, plain, (![A_105, B_106]: (v1_tops_1(k3_subset_1(u1_struct_0(A_105), B_106), A_105) | ~v3_tops_1(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.63/1.57  tff(c_30, plain, (![A_23, B_25]: (k2_pre_topc(A_23, B_25)=k2_struct_0(A_23) | ~v1_tops_1(B_25, A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.63/1.57  tff(c_557, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_549, c_30])).
% 3.63/1.57  tff(c_584, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_557])).
% 3.63/1.57  tff(c_650, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_584])).
% 3.63/1.57  tff(c_687, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_684, c_650])).
% 3.63/1.57  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_687])).
% 3.63/1.57  tff(c_707, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_584])).
% 3.63/1.57  tff(c_843, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_841, c_707])).
% 3.63/1.57  tff(c_848, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_841, c_841, c_549])).
% 3.63/1.57  tff(c_22, plain, (![A_14, B_16]: (k2_pre_topc(A_14, B_16)=B_16 | ~v4_pre_topc(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.63/1.57  tff(c_933, plain, (![B_16]: (k2_pre_topc('#skF_1', B_16)=B_16 | ~v4_pre_topc(B_16, '#skF_1') | ~m1_subset_1(B_16, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_841, c_22])).
% 3.63/1.57  tff(c_1386, plain, (![B_138]: (k2_pre_topc('#skF_1', B_138)=B_138 | ~v4_pre_topc(B_138, '#skF_1') | ~m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_933])).
% 3.63/1.57  tff(c_1389, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_848, c_1386])).
% 3.63/1.57  tff(c_1407, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_843, c_1389])).
% 3.63/1.57  tff(c_197, plain, (![A_57, B_58]: (m1_subset_1(k3_subset_1(A_57, B_58), k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.63/1.57  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k3_subset_1(A_3, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.63/1.57  tff(c_474, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k3_subset_1(A_91, B_92))=k3_subset_1(A_91, k3_subset_1(A_91, B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_197, c_8])).
% 3.63/1.57  tff(c_478, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_474])).
% 3.63/1.57  tff(c_485, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_478])).
% 3.63/1.57  tff(c_850, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_841, c_841, c_485])).
% 3.63/1.57  tff(c_1417, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1407, c_850])).
% 3.63/1.57  tff(c_82, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_74])).
% 3.63/1.57  tff(c_141, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_82])).
% 3.63/1.57  tff(c_140, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_subset_1(A_5, A_5))), inference(resolution, [status(thm)], [c_53, c_127])).
% 3.63/1.57  tff(c_175, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_140])).
% 3.63/1.57  tff(c_1452, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1417, c_175])).
% 3.63/1.57  tff(c_1458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1452])).
% 3.63/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.57  
% 3.63/1.57  Inference rules
% 3.63/1.57  ----------------------
% 3.63/1.57  #Ref     : 0
% 3.63/1.57  #Sup     : 280
% 3.63/1.57  #Fact    : 0
% 3.63/1.57  #Define  : 0
% 3.63/1.57  #Split   : 9
% 3.63/1.57  #Chain   : 0
% 3.63/1.57  #Close   : 0
% 3.63/1.57  
% 3.63/1.57  Ordering : KBO
% 3.63/1.57  
% 3.63/1.57  Simplification rules
% 3.63/1.57  ----------------------
% 3.63/1.57  #Subsume      : 51
% 3.63/1.57  #Demod        : 311
% 3.63/1.57  #Tautology    : 121
% 3.63/1.57  #SimpNegUnit  : 16
% 3.63/1.57  #BackRed      : 26
% 3.63/1.57  
% 3.63/1.57  #Partial instantiations: 0
% 3.63/1.57  #Strategies tried      : 1
% 3.63/1.57  
% 3.63/1.57  Timing (in seconds)
% 3.63/1.57  ----------------------
% 3.63/1.57  Preprocessing        : 0.33
% 3.63/1.57  Parsing              : 0.18
% 3.63/1.57  CNF conversion       : 0.02
% 3.63/1.57  Main loop            : 0.51
% 3.63/1.57  Inferencing          : 0.19
% 3.63/1.57  Reduction            : 0.17
% 3.63/1.57  Demodulation         : 0.12
% 3.63/1.57  BG Simplification    : 0.02
% 3.63/1.57  Subsumption          : 0.08
% 3.63/1.57  Abstraction          : 0.02
% 3.63/1.57  MUC search           : 0.00
% 3.63/1.57  Cooper               : 0.00
% 3.63/1.57  Total                : 0.88
% 3.63/1.57  Index Insertion      : 0.00
% 3.63/1.57  Index Deletion       : 0.00
% 3.63/1.57  Index Matching       : 0.00
% 3.63/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
