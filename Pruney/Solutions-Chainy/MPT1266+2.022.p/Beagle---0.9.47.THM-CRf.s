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
% DateTime   : Thu Dec  3 10:21:46 EST 2020

% Result     : Theorem 9.95s
% Output     : CNFRefutation 10.11s
% Verified   : 
% Statistics : Number of formulae       :  153 (1717 expanded)
%              Number of leaves         :   35 ( 591 expanded)
%              Depth                    :   14
%              Number of atoms          :  272 (2847 expanded)
%              Number of equality atoms :   78 (1332 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_38,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_75,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_81,plain,(
    ! [A_35,B_36] :
      ( k3_subset_1(A_35,k3_subset_1(A_35,B_36)) = B_36
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_443,plain,(
    ! [A_81,B_82] :
      ( k4_subset_1(u1_struct_0(A_81),B_82,k3_subset_1(u1_struct_0(A_81),B_82)) = k2_struct_0(A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_462,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_443])).

tff(c_486,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_489,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_486])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_489])).

tff(c_495,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_47,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_subset_1(A_8,B_9,k3_subset_1(A_8,B_9)) = k2_subset_1(A_8)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_155,plain,(
    ! [A_51,B_52] :
      ( k4_subset_1(A_51,B_52,k3_subset_1(A_51,B_52)) = A_51
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_165,plain,(
    ! [A_10] : k4_subset_1(A_10,k1_xboole_0,k3_subset_1(A_10,k1_xboole_0)) = A_10 ),
    inference(resolution,[status(thm)],[c_14,c_155])).

tff(c_172,plain,(
    ! [A_10] : k4_subset_1(A_10,k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_165])).

tff(c_470,plain,(
    ! [A_81] :
      ( k4_subset_1(u1_struct_0(A_81),k1_xboole_0,u1_struct_0(A_81)) = k2_struct_0(A_81)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_struct_0(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_443])).

tff(c_480,plain,(
    ! [A_81] :
      ( u1_struct_0(A_81) = k2_struct_0(A_81)
      | ~ l1_struct_0(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_172,c_470])).

tff(c_499,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_495,c_480])).

tff(c_503,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_219,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,B_59) = k2_struct_0(A_58)
      | ~ v1_tops_1(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_233,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_219])).

tff(c_243,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_233])).

tff(c_245,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_365,plain,(
    ! [A_73,B_74] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_73),B_74),A_73)
      | ~ v2_tops_1(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_375,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_365])).

tff(c_386,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_375])).

tff(c_387,plain,
    ( ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_386])).

tff(c_983,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_499,c_499,c_387])).

tff(c_984,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_983])).

tff(c_987,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_984])).

tff(c_991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_987])).

tff(c_993,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_983])).

tff(c_28,plain,(
    ! [A_23,B_25] :
      ( k2_pre_topc(A_23,B_25) = k2_struct_0(A_23)
      | ~ v1_tops_1(B_25,A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_549,plain,(
    ! [B_25] :
      ( k2_pre_topc('#skF_1',B_25) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_25,'#skF_1')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_28])).

tff(c_584,plain,(
    ! [B_25] :
      ( k2_pre_topc('#skF_1',B_25) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_25,'#skF_1')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_549])).

tff(c_1006,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_993,c_584])).

tff(c_1086,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1006])).

tff(c_26,plain,(
    ! [B_25,A_23] :
      ( v1_tops_1(B_25,A_23)
      | k2_pre_topc(A_23,B_25) != k2_struct_0(A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_546,plain,(
    ! [B_25] :
      ( v1_tops_1(B_25,'#skF_1')
      | k2_pre_topc('#skF_1',B_25) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_26])).

tff(c_582,plain,(
    ! [B_25] :
      ( v1_tops_1(B_25,'#skF_1')
      | k2_pre_topc('#skF_1',B_25) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_546])).

tff(c_1007,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_993,c_582])).

tff(c_1363,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1086,c_1007])).

tff(c_44,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_76,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_44])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( k3_subset_1(u1_struct_0(A_20),k2_pre_topc(A_20,k3_subset_1(u1_struct_0(A_20),B_22))) = k1_tops_1(A_20,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_148,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k2_pre_topc(A_49,B_50),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,B_6)) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1087,plain,(
    ! [A_103,B_104] :
      ( k3_subset_1(u1_struct_0(A_103),k3_subset_1(u1_struct_0(A_103),k2_pre_topc(A_103,B_104))) = k2_pre_topc(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_148,c_8])).

tff(c_11154,plain,(
    ! [A_301,B_302] :
      ( k3_subset_1(u1_struct_0(A_301),k1_tops_1(A_301,B_302)) = k2_pre_topc(A_301,k3_subset_1(u1_struct_0(A_301),B_302))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_301),B_302),k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301)
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1087])).

tff(c_11234,plain,(
    ! [A_303,B_304] :
      ( k3_subset_1(u1_struct_0(A_303),k1_tops_1(A_303,B_304)) = k2_pre_topc(A_303,k3_subset_1(u1_struct_0(A_303),B_304))
      | ~ l1_pre_topc(A_303)
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0(A_303))) ) ),
    inference(resolution,[status(thm)],[c_6,c_11154])).

tff(c_11246,plain,(
    ! [B_304] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_304)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_304))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_11234])).

tff(c_11274,plain,(
    ! [B_305] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_305)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_305))
      | ~ m1_subset_1(B_305,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_499,c_499,c_11246])).

tff(c_11337,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_503,c_11274])).

tff(c_11384,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_76,c_11337])).

tff(c_11386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1363,c_11384])).

tff(c_11388,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1006])).

tff(c_30,plain,(
    ! [B_28,A_26] :
      ( v2_tops_1(B_28,A_26)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_26),B_28),A_26)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_537,plain,(
    ! [B_28] :
      ( v2_tops_1(B_28,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_28),'#skF_1')
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_30])).

tff(c_576,plain,(
    ! [B_28] :
      ( v2_tops_1(B_28,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_28),'#skF_1')
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_499,c_537])).

tff(c_11454,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_11388,c_576])).

tff(c_11457,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_11454])).

tff(c_11459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_11457])).

tff(c_11460,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_11532,plain,(
    ! [A_321,B_322] :
      ( k4_subset_1(A_321,B_322,k3_subset_1(A_321,B_322)) = A_321
      | ~ m1_subset_1(B_322,k1_zfmisc_1(A_321)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_12])).

tff(c_11540,plain,(
    ! [A_10] : k4_subset_1(A_10,k1_xboole_0,k3_subset_1(A_10,k1_xboole_0)) = A_10 ),
    inference(resolution,[status(thm)],[c_14,c_11532])).

tff(c_11546,plain,(
    ! [A_10] : k4_subset_1(A_10,k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_11540])).

tff(c_11897,plain,(
    ! [A_353,B_354] :
      ( k4_subset_1(u1_struct_0(A_353),B_354,k3_subset_1(u1_struct_0(A_353),B_354)) = k2_struct_0(A_353)
      | ~ m1_subset_1(B_354,k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ l1_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11932,plain,(
    ! [A_353] :
      ( k4_subset_1(u1_struct_0(A_353),k1_xboole_0,u1_struct_0(A_353)) = k2_struct_0(A_353)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ l1_struct_0(A_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_11897])).

tff(c_11945,plain,(
    ! [A_355] :
      ( u1_struct_0(A_355) = k2_struct_0(A_355)
      | ~ l1_struct_0(A_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11546,c_11932])).

tff(c_11950,plain,(
    ! [A_356] :
      ( u1_struct_0(A_356) = k2_struct_0(A_356)
      | ~ l1_pre_topc(A_356) ) ),
    inference(resolution,[status(thm)],[c_20,c_11945])).

tff(c_11954,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_11950])).

tff(c_11962,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11954,c_34])).

tff(c_11487,plain,(
    ! [A_318,B_319] :
      ( k3_subset_1(A_318,k3_subset_1(A_318,B_319)) = B_319
      | ~ m1_subset_1(B_319,k1_zfmisc_1(A_318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11495,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_11487])).

tff(c_11500,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_11495])).

tff(c_11461,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_32,plain,(
    ! [A_26,B_28] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_26),B_28),A_26)
      | ~ v2_tops_1(B_28,A_26)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11981,plain,(
    ! [B_28] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_28),'#skF_1')
      | ~ v2_tops_1(B_28,'#skF_1')
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11954,c_32])).

tff(c_12648,plain,(
    ! [B_378] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_378),'#skF_1')
      | ~ v2_tops_1(B_378,'#skF_1')
      | ~ m1_subset_1(B_378,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11954,c_11981])).

tff(c_11589,plain,(
    ! [B_327,A_328] :
      ( v1_tops_1(B_327,A_328)
      | k2_pre_topc(A_328,B_327) != k2_struct_0(A_328)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11603,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_11589])).

tff(c_11613,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11603])).

tff(c_11615,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_11613])).

tff(c_11632,plain,(
    ! [A_334,B_335] :
      ( k2_pre_topc(A_334,B_335) = k2_struct_0(A_334)
      | ~ v1_tops_1(B_335,A_334)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ l1_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11646,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_11632])).

tff(c_11656,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11646])).

tff(c_11657,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_11615,c_11656])).

tff(c_11498,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_11487])).

tff(c_11800,plain,(
    ! [A_347,B_348] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_347),B_348),A_347)
      | ~ v2_tops_1(B_348,A_347)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ l1_pre_topc(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11810,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11498,c_11800])).

tff(c_11821,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11810])).

tff(c_11822,plain,
    ( ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_11657,c_11821])).

tff(c_11845,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11822])).

tff(c_11848,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_11845])).

tff(c_11852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_11848])).

tff(c_11854,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_11822])).

tff(c_11857,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_11854,c_28])).

tff(c_11869,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11857])).

tff(c_12439,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11954,c_11954,c_11869])).

tff(c_12440,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12439])).

tff(c_12651,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12648,c_12440])).

tff(c_12682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11962,c_11461,c_12651])).

tff(c_12683,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_12439])).

tff(c_12049,plain,(
    ! [A_357,B_358] :
      ( k3_subset_1(u1_struct_0(A_357),k2_pre_topc(A_357,k3_subset_1(u1_struct_0(A_357),B_358))) = k1_tops_1(A_357,B_358)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ l1_pre_topc(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12091,plain,(
    ! [B_358] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_358))) = k1_tops_1('#skF_1',B_358)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11954,c_12049])).

tff(c_13035,plain,(
    ! [B_388] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_388))) = k1_tops_1('#skF_1',B_388)
      | ~ m1_subset_1(B_388,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11954,c_11954,c_12091])).

tff(c_13077,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12683,c_13035])).

tff(c_13102,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11962,c_11500,c_13077])).

tff(c_13104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11460,c_13102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.95/3.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.95/3.74  
% 9.95/3.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.95/3.74  %$ v2_tops_1 > v1_tops_1 > r2_hidden > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.95/3.74  
% 9.95/3.74  %Foreground sorts:
% 9.95/3.74  
% 9.95/3.74  
% 9.95/3.74  %Background operators:
% 9.95/3.74  
% 9.95/3.74  
% 9.95/3.74  %Foreground operators:
% 9.95/3.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.95/3.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.95/3.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.95/3.74  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 9.95/3.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.95/3.74  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.95/3.74  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.95/3.74  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 9.95/3.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.95/3.74  tff('#skF_2', type, '#skF_2': $i).
% 9.95/3.74  tff('#skF_1', type, '#skF_1': $i).
% 9.95/3.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.95/3.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.95/3.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.95/3.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.95/3.74  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 9.95/3.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.95/3.74  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.95/3.74  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.95/3.74  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.95/3.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.95/3.74  
% 10.11/3.76  tff(f_103, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 10.11/3.76  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.11/3.76  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.11/3.76  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_pre_topc)).
% 10.11/3.76  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.11/3.76  tff(f_27, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 10.11/3.76  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 10.11/3.76  tff(f_39, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 10.11/3.76  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 10.11/3.76  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.11/3.76  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 10.11/3.76  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 10.11/3.76  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 10.11/3.76  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.11/3.76  tff(c_38, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.11/3.76  tff(c_75, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 10.11/3.76  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.11/3.76  tff(c_20, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.11/3.76  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.11/3.76  tff(c_81, plain, (![A_35, B_36]: (k3_subset_1(A_35, k3_subset_1(A_35, B_36))=B_36 | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.11/3.76  tff(c_86, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_81])).
% 10.11/3.76  tff(c_443, plain, (![A_81, B_82]: (k4_subset_1(u1_struct_0(A_81), B_82, k3_subset_1(u1_struct_0(A_81), B_82))=k2_struct_0(A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.11/3.76  tff(c_462, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k2_struct_0('#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_86, c_443])).
% 10.11/3.76  tff(c_486, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_462])).
% 10.11/3.76  tff(c_489, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_486])).
% 10.11/3.76  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_489])).
% 10.11/3.76  tff(c_495, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_462])).
% 10.11/3.76  tff(c_14, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.11/3.76  tff(c_2, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.11/3.76  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.11/3.76  tff(c_10, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.11/3.76  tff(c_45, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 10.11/3.76  tff(c_47, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_45])).
% 10.11/3.76  tff(c_12, plain, (![A_8, B_9]: (k4_subset_1(A_8, B_9, k3_subset_1(A_8, B_9))=k2_subset_1(A_8) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.11/3.76  tff(c_155, plain, (![A_51, B_52]: (k4_subset_1(A_51, B_52, k3_subset_1(A_51, B_52))=A_51 | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 10.11/3.76  tff(c_165, plain, (![A_10]: (k4_subset_1(A_10, k1_xboole_0, k3_subset_1(A_10, k1_xboole_0))=A_10)), inference(resolution, [status(thm)], [c_14, c_155])).
% 10.11/3.76  tff(c_172, plain, (![A_10]: (k4_subset_1(A_10, k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_47, c_165])).
% 10.11/3.76  tff(c_470, plain, (![A_81]: (k4_subset_1(u1_struct_0(A_81), k1_xboole_0, u1_struct_0(A_81))=k2_struct_0(A_81) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_struct_0(A_81))), inference(superposition, [status(thm), theory('equality')], [c_47, c_443])).
% 10.11/3.76  tff(c_480, plain, (![A_81]: (u1_struct_0(A_81)=k2_struct_0(A_81) | ~l1_struct_0(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_172, c_470])).
% 10.11/3.76  tff(c_499, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_495, c_480])).
% 10.11/3.76  tff(c_503, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_34])).
% 10.11/3.76  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.11/3.76  tff(c_219, plain, (![A_58, B_59]: (k2_pre_topc(A_58, B_59)=k2_struct_0(A_58) | ~v1_tops_1(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.11/3.76  tff(c_233, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_219])).
% 10.11/3.76  tff(c_243, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_233])).
% 10.11/3.76  tff(c_245, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_243])).
% 10.11/3.76  tff(c_365, plain, (![A_73, B_74]: (v1_tops_1(k3_subset_1(u1_struct_0(A_73), B_74), A_73) | ~v2_tops_1(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.11/3.76  tff(c_375, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_86, c_365])).
% 10.11/3.76  tff(c_386, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_375])).
% 10.11/3.76  tff(c_387, plain, (~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_245, c_386])).
% 10.11/3.76  tff(c_983, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_499, c_499, c_387])).
% 10.11/3.76  tff(c_984, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_983])).
% 10.11/3.76  tff(c_987, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_984])).
% 10.11/3.76  tff(c_991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_503, c_987])).
% 10.11/3.76  tff(c_993, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_983])).
% 10.11/3.76  tff(c_28, plain, (![A_23, B_25]: (k2_pre_topc(A_23, B_25)=k2_struct_0(A_23) | ~v1_tops_1(B_25, A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.11/3.76  tff(c_549, plain, (![B_25]: (k2_pre_topc('#skF_1', B_25)=k2_struct_0('#skF_1') | ~v1_tops_1(B_25, '#skF_1') | ~m1_subset_1(B_25, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_499, c_28])).
% 10.11/3.76  tff(c_584, plain, (![B_25]: (k2_pre_topc('#skF_1', B_25)=k2_struct_0('#skF_1') | ~v1_tops_1(B_25, '#skF_1') | ~m1_subset_1(B_25, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_549])).
% 10.11/3.76  tff(c_1006, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_993, c_584])).
% 10.11/3.76  tff(c_1086, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1006])).
% 10.11/3.76  tff(c_26, plain, (![B_25, A_23]: (v1_tops_1(B_25, A_23) | k2_pre_topc(A_23, B_25)!=k2_struct_0(A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.11/3.76  tff(c_546, plain, (![B_25]: (v1_tops_1(B_25, '#skF_1') | k2_pre_topc('#skF_1', B_25)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_25, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_499, c_26])).
% 10.11/3.76  tff(c_582, plain, (![B_25]: (v1_tops_1(B_25, '#skF_1') | k2_pre_topc('#skF_1', B_25)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_25, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_546])).
% 10.11/3.76  tff(c_1007, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_993, c_582])).
% 10.11/3.76  tff(c_1363, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1086, c_1007])).
% 10.11/3.76  tff(c_44, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.11/3.76  tff(c_76, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_75, c_44])).
% 10.11/3.76  tff(c_24, plain, (![A_20, B_22]: (k3_subset_1(u1_struct_0(A_20), k2_pre_topc(A_20, k3_subset_1(u1_struct_0(A_20), B_22)))=k1_tops_1(A_20, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.11/3.76  tff(c_148, plain, (![A_49, B_50]: (m1_subset_1(k2_pre_topc(A_49, B_50), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.11/3.76  tff(c_8, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, B_6))=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.11/3.76  tff(c_1087, plain, (![A_103, B_104]: (k3_subset_1(u1_struct_0(A_103), k3_subset_1(u1_struct_0(A_103), k2_pre_topc(A_103, B_104)))=k2_pre_topc(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_148, c_8])).
% 10.11/3.76  tff(c_11154, plain, (![A_301, B_302]: (k3_subset_1(u1_struct_0(A_301), k1_tops_1(A_301, B_302))=k2_pre_topc(A_301, k3_subset_1(u1_struct_0(A_301), B_302)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_301), B_302), k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301) | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1087])).
% 10.11/3.76  tff(c_11234, plain, (![A_303, B_304]: (k3_subset_1(u1_struct_0(A_303), k1_tops_1(A_303, B_304))=k2_pre_topc(A_303, k3_subset_1(u1_struct_0(A_303), B_304)) | ~l1_pre_topc(A_303) | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0(A_303))))), inference(resolution, [status(thm)], [c_6, c_11154])).
% 10.11/3.76  tff(c_11246, plain, (![B_304]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_304))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_304)) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_304, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_499, c_11234])).
% 10.11/3.76  tff(c_11274, plain, (![B_305]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_305))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_305)) | ~m1_subset_1(B_305, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_499, c_499, c_11246])).
% 10.11/3.76  tff(c_11337, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_503, c_11274])).
% 10.11/3.76  tff(c_11384, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_76, c_11337])).
% 10.11/3.76  tff(c_11386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1363, c_11384])).
% 10.11/3.76  tff(c_11388, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_1006])).
% 10.11/3.76  tff(c_30, plain, (![B_28, A_26]: (v2_tops_1(B_28, A_26) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_26), B_28), A_26) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.11/3.76  tff(c_537, plain, (![B_28]: (v2_tops_1(B_28, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_28), '#skF_1') | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_499, c_30])).
% 10.11/3.76  tff(c_576, plain, (![B_28]: (v2_tops_1(B_28, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_28), '#skF_1') | ~m1_subset_1(B_28, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_499, c_537])).
% 10.11/3.76  tff(c_11454, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_11388, c_576])).
% 10.11/3.76  tff(c_11457, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_11454])).
% 10.11/3.76  tff(c_11459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_11457])).
% 10.11/3.76  tff(c_11460, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 10.11/3.76  tff(c_11532, plain, (![A_321, B_322]: (k4_subset_1(A_321, B_322, k3_subset_1(A_321, B_322))=A_321 | ~m1_subset_1(B_322, k1_zfmisc_1(A_321)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_12])).
% 10.11/3.76  tff(c_11540, plain, (![A_10]: (k4_subset_1(A_10, k1_xboole_0, k3_subset_1(A_10, k1_xboole_0))=A_10)), inference(resolution, [status(thm)], [c_14, c_11532])).
% 10.11/3.76  tff(c_11546, plain, (![A_10]: (k4_subset_1(A_10, k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_47, c_11540])).
% 10.11/3.76  tff(c_11897, plain, (![A_353, B_354]: (k4_subset_1(u1_struct_0(A_353), B_354, k3_subset_1(u1_struct_0(A_353), B_354))=k2_struct_0(A_353) | ~m1_subset_1(B_354, k1_zfmisc_1(u1_struct_0(A_353))) | ~l1_struct_0(A_353))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.11/3.76  tff(c_11932, plain, (![A_353]: (k4_subset_1(u1_struct_0(A_353), k1_xboole_0, u1_struct_0(A_353))=k2_struct_0(A_353) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_353))) | ~l1_struct_0(A_353))), inference(superposition, [status(thm), theory('equality')], [c_47, c_11897])).
% 10.11/3.76  tff(c_11945, plain, (![A_355]: (u1_struct_0(A_355)=k2_struct_0(A_355) | ~l1_struct_0(A_355))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_11546, c_11932])).
% 10.11/3.76  tff(c_11950, plain, (![A_356]: (u1_struct_0(A_356)=k2_struct_0(A_356) | ~l1_pre_topc(A_356))), inference(resolution, [status(thm)], [c_20, c_11945])).
% 10.11/3.76  tff(c_11954, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_11950])).
% 10.11/3.76  tff(c_11962, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11954, c_34])).
% 10.11/3.76  tff(c_11487, plain, (![A_318, B_319]: (k3_subset_1(A_318, k3_subset_1(A_318, B_319))=B_319 | ~m1_subset_1(B_319, k1_zfmisc_1(A_318)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.11/3.76  tff(c_11495, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_11487])).
% 10.11/3.76  tff(c_11500, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_47, c_11495])).
% 10.11/3.76  tff(c_11461, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 10.11/3.76  tff(c_32, plain, (![A_26, B_28]: (v1_tops_1(k3_subset_1(u1_struct_0(A_26), B_28), A_26) | ~v2_tops_1(B_28, A_26) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.11/3.76  tff(c_11981, plain, (![B_28]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_28), '#skF_1') | ~v2_tops_1(B_28, '#skF_1') | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11954, c_32])).
% 10.11/3.76  tff(c_12648, plain, (![B_378]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_378), '#skF_1') | ~v2_tops_1(B_378, '#skF_1') | ~m1_subset_1(B_378, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_11954, c_11981])).
% 10.11/3.76  tff(c_11589, plain, (![B_327, A_328]: (v1_tops_1(B_327, A_328) | k2_pre_topc(A_328, B_327)!=k2_struct_0(A_328) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.11/3.76  tff(c_11603, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_11589])).
% 10.11/3.76  tff(c_11613, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_11603])).
% 10.11/3.76  tff(c_11615, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_11613])).
% 10.11/3.76  tff(c_11632, plain, (![A_334, B_335]: (k2_pre_topc(A_334, B_335)=k2_struct_0(A_334) | ~v1_tops_1(B_335, A_334) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_334))) | ~l1_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.11/3.76  tff(c_11646, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_11632])).
% 10.11/3.76  tff(c_11656, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_11646])).
% 10.11/3.76  tff(c_11657, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_11615, c_11656])).
% 10.11/3.76  tff(c_11498, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_11487])).
% 10.11/3.76  tff(c_11800, plain, (![A_347, B_348]: (v1_tops_1(k3_subset_1(u1_struct_0(A_347), B_348), A_347) | ~v2_tops_1(B_348, A_347) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0(A_347))) | ~l1_pre_topc(A_347))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.11/3.76  tff(c_11810, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11498, c_11800])).
% 10.11/3.76  tff(c_11821, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_11810])).
% 10.11/3.76  tff(c_11822, plain, (~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_11657, c_11821])).
% 10.11/3.76  tff(c_11845, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_11822])).
% 10.11/3.76  tff(c_11848, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_11845])).
% 10.11/3.76  tff(c_11852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_11848])).
% 10.11/3.76  tff(c_11854, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_11822])).
% 10.11/3.76  tff(c_11857, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_11854, c_28])).
% 10.11/3.76  tff(c_11869, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_11857])).
% 10.11/3.76  tff(c_12439, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11954, c_11954, c_11869])).
% 10.11/3.76  tff(c_12440, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_12439])).
% 10.11/3.76  tff(c_12651, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12648, c_12440])).
% 10.11/3.76  tff(c_12682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11962, c_11461, c_12651])).
% 10.11/3.76  tff(c_12683, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_12439])).
% 10.11/3.76  tff(c_12049, plain, (![A_357, B_358]: (k3_subset_1(u1_struct_0(A_357), k2_pre_topc(A_357, k3_subset_1(u1_struct_0(A_357), B_358)))=k1_tops_1(A_357, B_358) | ~m1_subset_1(B_358, k1_zfmisc_1(u1_struct_0(A_357))) | ~l1_pre_topc(A_357))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.11/3.76  tff(c_12091, plain, (![B_358]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_358)))=k1_tops_1('#skF_1', B_358) | ~m1_subset_1(B_358, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11954, c_12049])).
% 10.11/3.76  tff(c_13035, plain, (![B_388]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_388)))=k1_tops_1('#skF_1', B_388) | ~m1_subset_1(B_388, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_11954, c_11954, c_12091])).
% 10.11/3.76  tff(c_13077, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12683, c_13035])).
% 10.11/3.76  tff(c_13102, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11962, c_11500, c_13077])).
% 10.11/3.76  tff(c_13104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11460, c_13102])).
% 10.11/3.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.11/3.76  
% 10.11/3.76  Inference rules
% 10.11/3.76  ----------------------
% 10.11/3.76  #Ref     : 0
% 10.11/3.76  #Sup     : 3156
% 10.11/3.76  #Fact    : 0
% 10.11/3.76  #Define  : 0
% 10.11/3.76  #Split   : 41
% 10.11/3.76  #Chain   : 0
% 10.11/3.76  #Close   : 0
% 10.11/3.76  
% 10.11/3.76  Ordering : KBO
% 10.11/3.76  
% 10.11/3.76  Simplification rules
% 10.11/3.76  ----------------------
% 10.11/3.76  #Subsume      : 626
% 10.11/3.76  #Demod        : 3805
% 10.11/3.76  #Tautology    : 720
% 10.11/3.76  #SimpNegUnit  : 312
% 10.11/3.76  #BackRed      : 12
% 10.11/3.76  
% 10.11/3.76  #Partial instantiations: 0
% 10.11/3.76  #Strategies tried      : 1
% 10.11/3.76  
% 10.11/3.77  Timing (in seconds)
% 10.11/3.77  ----------------------
% 10.11/3.77  Preprocessing        : 0.29
% 10.11/3.77  Parsing              : 0.15
% 10.11/3.77  CNF conversion       : 0.02
% 10.11/3.77  Main loop            : 2.59
% 10.11/3.77  Inferencing          : 0.69
% 10.11/3.77  Reduction            : 1.10
% 10.11/3.77  Demodulation         : 0.81
% 10.11/3.77  BG Simplification    : 0.08
% 10.11/3.77  Subsumption          : 0.56
% 10.11/3.77  Abstraction          : 0.11
% 10.11/3.77  MUC search           : 0.00
% 10.11/3.77  Cooper               : 0.00
% 10.11/3.77  Total                : 2.92
% 10.11/3.77  Index Insertion      : 0.00
% 10.11/3.77  Index Deletion       : 0.00
% 10.11/3.77  Index Matching       : 0.00
% 10.11/3.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
