%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:34 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 127 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 250 expanded)
%              Number of equality atoms :   50 (  81 expanded)
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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
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

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1117,plain,(
    ! [A_146,B_147,C_148] :
      ( k7_subset_1(A_146,B_147,C_148) = k4_xboole_0(B_147,C_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1120,plain,(
    ! [C_148] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_148) = k4_xboole_0('#skF_2',C_148) ),
    inference(resolution,[status(thm)],[c_40,c_1117])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_90,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_660,plain,(
    ! [B_91,A_92] :
      ( v4_pre_topc(B_91,A_92)
      | k2_pre_topc(A_92,B_91) != B_91
      | ~ v2_pre_topc(A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_666,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_660])).

tff(c_670,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_666])).

tff(c_671,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_670])).

tff(c_672,plain,(
    ! [A_93,B_94] :
      ( k4_subset_1(u1_struct_0(A_93),B_94,k2_tops_1(A_93,B_94)) = k2_pre_topc(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_676,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_672])).

tff(c_680,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_676])).

tff(c_14,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_66])).

tff(c_215,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k4_xboole_0(B_56,A_55)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_227,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k2_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_215])).

tff(c_233,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_227])).

tff(c_289,plain,(
    ! [A_61,B_62,C_63] :
      ( k7_subset_1(A_61,B_62,C_63) = k4_xboole_0(B_62,C_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_336,plain,(
    ! [C_66] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_66) = k4_xboole_0('#skF_2',C_66) ),
    inference(resolution,[status(thm)],[c_40,c_289])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_209,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_52])).

tff(c_342,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_209])).

tff(c_20,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_11,B_12] : k4_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_357,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_76])).

tff(c_22,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_378,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_22])).

tff(c_387,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_378])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_636,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_subset_1(A_87,B_88,C_89) = k2_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_767,plain,(
    ! [A_114,B_115,B_116] :
      ( k4_subset_1(u1_struct_0(A_114),B_115,k2_tops_1(A_114,B_116)) = k2_xboole_0(B_115,k2_tops_1(A_114,B_116))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_32,c_636])).

tff(c_771,plain,(
    ! [B_116] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_116)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_116))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_767])).

tff(c_776,plain,(
    ! [B_117] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_117)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_117))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_771])).

tff(c_783,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_776])).

tff(c_788,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_387,c_783])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_788])).

tff(c_791,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1121,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1120,c_791])).

tff(c_792,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1193,plain,(
    ! [A_158,B_159] :
      ( k2_pre_topc(A_158,B_159) = B_159
      | ~ v4_pre_topc(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1199,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1193])).

tff(c_1203,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_792,c_1199])).

tff(c_1282,plain,(
    ! [A_173,B_174] :
      ( k7_subset_1(u1_struct_0(A_173),k2_pre_topc(A_173,B_174),k1_tops_1(A_173,B_174)) = k2_tops_1(A_173,B_174)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1291,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1203,c_1282])).

tff(c_1295,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1120,c_1291])).

tff(c_1297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1121,c_1295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.51  
% 3.11/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.52  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.11/1.52  
% 3.11/1.52  %Foreground sorts:
% 3.11/1.52  
% 3.11/1.52  
% 3.11/1.52  %Background operators:
% 3.11/1.52  
% 3.11/1.52  
% 3.11/1.52  %Foreground operators:
% 3.11/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.52  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.11/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.52  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.11/1.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.11/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.52  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.11/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.52  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.11/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.11/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.52  
% 3.11/1.53  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 3.11/1.53  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.11/1.53  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.11/1.53  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 3.11/1.53  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.11/1.53  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.11/1.53  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.11/1.53  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.11/1.53  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.11/1.53  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.11/1.53  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.11/1.53  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.11/1.53  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.53  tff(c_1117, plain, (![A_146, B_147, C_148]: (k7_subset_1(A_146, B_147, C_148)=k4_xboole_0(B_147, C_148) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.11/1.53  tff(c_1120, plain, (![C_148]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_148)=k4_xboole_0('#skF_2', C_148))), inference(resolution, [status(thm)], [c_40, c_1117])).
% 3.11/1.53  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.53  tff(c_90, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 3.11/1.53  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.53  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.53  tff(c_660, plain, (![B_91, A_92]: (v4_pre_topc(B_91, A_92) | k2_pre_topc(A_92, B_91)!=B_91 | ~v2_pre_topc(A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.11/1.53  tff(c_666, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_660])).
% 3.11/1.53  tff(c_670, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_666])).
% 3.11/1.53  tff(c_671, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_90, c_670])).
% 3.11/1.53  tff(c_672, plain, (![A_93, B_94]: (k4_subset_1(u1_struct_0(A_93), B_94, k2_tops_1(A_93, B_94))=k2_pre_topc(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.53  tff(c_676, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_672])).
% 3.11/1.53  tff(c_680, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_676])).
% 3.11/1.53  tff(c_14, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.11/1.53  tff(c_18, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.11/1.53  tff(c_66, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.53  tff(c_78, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_66])).
% 3.11/1.53  tff(c_215, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k4_xboole_0(B_56, A_55))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.11/1.53  tff(c_227, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k2_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_215])).
% 3.11/1.53  tff(c_233, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_227])).
% 3.11/1.53  tff(c_289, plain, (![A_61, B_62, C_63]: (k7_subset_1(A_61, B_62, C_63)=k4_xboole_0(B_62, C_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.11/1.53  tff(c_336, plain, (![C_66]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_66)=k4_xboole_0('#skF_2', C_66))), inference(resolution, [status(thm)], [c_40, c_289])).
% 3.11/1.53  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.53  tff(c_209, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_90, c_52])).
% 3.11/1.53  tff(c_342, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_336, c_209])).
% 3.11/1.53  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.11/1.53  tff(c_76, plain, (![A_11, B_12]: (k4_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_66])).
% 3.11/1.53  tff(c_357, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_342, c_76])).
% 3.11/1.53  tff(c_22, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.11/1.53  tff(c_378, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_357, c_22])).
% 3.11/1.53  tff(c_387, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_233, c_378])).
% 3.11/1.53  tff(c_32, plain, (![A_24, B_25]: (m1_subset_1(k2_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.11/1.53  tff(c_636, plain, (![A_87, B_88, C_89]: (k4_subset_1(A_87, B_88, C_89)=k2_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.11/1.53  tff(c_767, plain, (![A_114, B_115, B_116]: (k4_subset_1(u1_struct_0(A_114), B_115, k2_tops_1(A_114, B_116))=k2_xboole_0(B_115, k2_tops_1(A_114, B_116)) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_32, c_636])).
% 3.11/1.53  tff(c_771, plain, (![B_116]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_116))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_116)) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_767])).
% 3.11/1.53  tff(c_776, plain, (![B_117]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_117))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_117)) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_771])).
% 3.11/1.53  tff(c_783, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_776])).
% 3.11/1.53  tff(c_788, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_680, c_387, c_783])).
% 3.11/1.53  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_671, c_788])).
% 3.11/1.53  tff(c_791, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.11/1.53  tff(c_1121, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1120, c_791])).
% 3.11/1.53  tff(c_792, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 3.11/1.53  tff(c_1193, plain, (![A_158, B_159]: (k2_pre_topc(A_158, B_159)=B_159 | ~v4_pre_topc(B_159, A_158) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.11/1.53  tff(c_1199, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1193])).
% 3.11/1.53  tff(c_1203, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_792, c_1199])).
% 3.11/1.53  tff(c_1282, plain, (![A_173, B_174]: (k7_subset_1(u1_struct_0(A_173), k2_pre_topc(A_173, B_174), k1_tops_1(A_173, B_174))=k2_tops_1(A_173, B_174) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.11/1.53  tff(c_1291, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1203, c_1282])).
% 3.11/1.53  tff(c_1295, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1120, c_1291])).
% 3.11/1.53  tff(c_1297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1121, c_1295])).
% 3.11/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.53  
% 3.11/1.53  Inference rules
% 3.11/1.53  ----------------------
% 3.11/1.53  #Ref     : 0
% 3.11/1.53  #Sup     : 286
% 3.11/1.53  #Fact    : 0
% 3.11/1.53  #Define  : 0
% 3.11/1.53  #Split   : 4
% 3.11/1.53  #Chain   : 0
% 3.11/1.53  #Close   : 0
% 3.11/1.53  
% 3.11/1.53  Ordering : KBO
% 3.11/1.53  
% 3.11/1.53  Simplification rules
% 3.11/1.53  ----------------------
% 3.11/1.53  #Subsume      : 23
% 3.11/1.53  #Demod        : 138
% 3.11/1.53  #Tautology    : 187
% 3.11/1.53  #SimpNegUnit  : 6
% 3.11/1.53  #BackRed      : 1
% 3.11/1.53  
% 3.11/1.53  #Partial instantiations: 0
% 3.11/1.53  #Strategies tried      : 1
% 3.11/1.53  
% 3.11/1.53  Timing (in seconds)
% 3.11/1.53  ----------------------
% 3.11/1.53  Preprocessing        : 0.34
% 3.11/1.53  Parsing              : 0.18
% 3.11/1.54  CNF conversion       : 0.02
% 3.11/1.54  Main loop            : 0.41
% 3.11/1.54  Inferencing          : 0.15
% 3.11/1.54  Reduction            : 0.14
% 3.11/1.54  Demodulation         : 0.10
% 3.11/1.54  BG Simplification    : 0.02
% 3.11/1.54  Subsumption          : 0.07
% 3.11/1.54  Abstraction          : 0.02
% 3.11/1.54  MUC search           : 0.00
% 3.11/1.54  Cooper               : 0.00
% 3.11/1.54  Total                : 0.78
% 3.11/1.54  Index Insertion      : 0.00
% 3.11/1.54  Index Deletion       : 0.00
% 3.11/1.54  Index Matching       : 0.00
% 3.11/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
