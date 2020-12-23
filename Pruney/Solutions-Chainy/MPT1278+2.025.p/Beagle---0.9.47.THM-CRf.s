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
% DateTime   : Thu Dec  3 10:22:11 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 816 expanded)
%              Number of leaves         :   35 ( 287 expanded)
%              Depth                    :   16
%              Number of atoms          :  170 (1955 expanded)
%              Number of equality atoms :   51 ( 480 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_70,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_84,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_80])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_85,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_42])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1257,plain,(
    ! [B_108,A_109] :
      ( v1_tops_1(B_108,A_109)
      | k2_pre_topc(A_109,B_108) != k2_struct_0(A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1268,plain,(
    ! [B_108] :
      ( v1_tops_1(B_108,'#skF_1')
      | k2_pre_topc('#skF_1',B_108) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1257])).

tff(c_1309,plain,(
    ! [B_113] :
      ( v1_tops_1(B_113,'#skF_1')
      | k2_pre_topc('#skF_1',B_113) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1268])).

tff(c_1327,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_1309])).

tff(c_1353,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1327])).

tff(c_1331,plain,(
    ! [A_114,B_115] :
      ( k2_pre_topc(A_114,B_115) = k2_struct_0(A_114)
      | ~ v1_tops_1(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1342,plain,(
    ! [B_115] :
      ( k2_pre_topc('#skF_1',B_115) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_115,'#skF_1')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1331])).

tff(c_1369,plain,(
    ! [B_118] :
      ( k2_pre_topc('#skF_1',B_118) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_118,'#skF_1')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1342])).

tff(c_1380,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_1369])).

tff(c_1391,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1353,c_1380])).

tff(c_150,plain,(
    ! [A_41,B_42] :
      ( k3_subset_1(A_41,k3_subset_1(A_41,B_42)) = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_85,c_150])).

tff(c_1401,plain,(
    ! [A_119,B_120] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_119),B_120),A_119)
      | ~ v3_tops_1(B_120,A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1412,plain,(
    ! [B_120] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_120),'#skF_1')
      | ~ v3_tops_1(B_120,'#skF_1')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1401])).

tff(c_1436,plain,(
    ! [B_123] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_123),'#skF_1')
      | ~ v3_tops_1(B_123,'#skF_1')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_84,c_1412])).

tff(c_1447,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_1436])).

tff(c_1453,plain,
    ( ~ v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1391,c_1447])).

tff(c_1746,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1453])).

tff(c_1749,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14,c_1746])).

tff(c_1753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1749])).

tff(c_1755,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1453])).

tff(c_40,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1785,plain,(
    ! [B_142,A_143] :
      ( v4_pre_topc(B_142,A_143)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_143),B_142),A_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1803,plain,(
    ! [B_142] :
      ( v4_pre_topc(B_142,'#skF_1')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_142),'#skF_1')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1785])).

tff(c_1836,plain,(
    ! [B_146] :
      ( v4_pre_topc(B_146,'#skF_1')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_146),'#skF_1')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_84,c_1803])).

tff(c_1854,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_1836])).

tff(c_1862,plain,(
    v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_40,c_1854])).

tff(c_38,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1418,plain,(
    ! [B_120] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_120),'#skF_1')
      | ~ v3_tops_1(B_120,'#skF_1')
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_84,c_1412])).

tff(c_1276,plain,(
    ! [B_108] :
      ( v1_tops_1(B_108,'#skF_1')
      | k2_pre_topc('#skF_1',B_108) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1268])).

tff(c_1779,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1755,c_1276])).

tff(c_1888,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1779])).

tff(c_1350,plain,(
    ! [B_115] :
      ( k2_pre_topc('#skF_1',B_115) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_115,'#skF_1')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1342])).

tff(c_1778,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1755,c_1350])).

tff(c_1915,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1888,c_1778])).

tff(c_1918,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1418,c_1915])).

tff(c_1922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_38,c_1918])).

tff(c_1924,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1779])).

tff(c_231,plain,(
    ! [A_48,B_49] :
      ( k2_pre_topc(A_48,B_49) = B_49
      | ~ v4_pre_topc(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_238,plain,(
    ! [B_49] :
      ( k2_pre_topc('#skF_1',B_49) = B_49
      | ~ v4_pre_topc(B_49,'#skF_1')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_231])).

tff(c_245,plain,(
    ! [B_49] :
      ( k2_pre_topc('#skF_1',B_49) = B_49
      | ~ v4_pre_topc(B_49,'#skF_1')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_238])).

tff(c_1780,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1755,c_245])).

tff(c_2002,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1862,c_1924,c_1780])).

tff(c_181,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k3_subset_1(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_192,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_181])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_265,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_6])).

tff(c_1468,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(A_125,k3_subset_1(A_125,B_126)) = k3_subset_1(A_125,k3_subset_1(A_125,B_126))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_14,c_181])).

tff(c_1474,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_85,c_1468])).

tff(c_1481,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_265,c_1474])).

tff(c_1484,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1481,c_265])).

tff(c_2009,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2002,c_1484])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_108,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_2078,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2009,c_108])).

tff(c_2089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n008.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 17:16:15 EST 2020
% 0.13/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/2.15  
% 4.56/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/2.16  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.56/2.16  
% 4.56/2.16  %Foreground sorts:
% 4.56/2.16  
% 4.56/2.16  
% 4.56/2.16  %Background operators:
% 4.56/2.16  
% 4.56/2.16  
% 4.56/2.16  %Foreground operators:
% 4.56/2.16  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.56/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.56/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/2.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.56/2.16  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.56/2.16  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.56/2.16  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.56/2.16  tff('#skF_2', type, '#skF_2': $i).
% 4.56/2.16  tff('#skF_1', type, '#skF_1': $i).
% 4.56/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.56/2.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.56/2.16  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.56/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/2.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.56/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.56/2.16  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.56/2.16  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.56/2.16  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.56/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/2.16  
% 4.56/2.17  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 4.56/2.17  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.56/2.17  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.56/2.17  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.56/2.17  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 4.56/2.17  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.56/2.17  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 4.56/2.17  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 4.56/2.17  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.56/2.17  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.56/2.17  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.56/2.17  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.56/2.17  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.56/2.17  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.56/2.17  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.56/2.17  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.56/2.17  tff(c_75, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.56/2.17  tff(c_80, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_20, c_75])).
% 4.56/2.17  tff(c_84, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_80])).
% 4.56/2.17  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.56/2.17  tff(c_85, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_42])).
% 4.56/2.17  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/2.17  tff(c_1257, plain, (![B_108, A_109]: (v1_tops_1(B_108, A_109) | k2_pre_topc(A_109, B_108)!=k2_struct_0(A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.56/2.17  tff(c_1268, plain, (![B_108]: (v1_tops_1(B_108, '#skF_1') | k2_pre_topc('#skF_1', B_108)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_108, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_1257])).
% 4.56/2.17  tff(c_1309, plain, (![B_113]: (v1_tops_1(B_113, '#skF_1') | k2_pre_topc('#skF_1', B_113)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_113, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1268])).
% 4.56/2.17  tff(c_1327, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_85, c_1309])).
% 4.56/2.17  tff(c_1353, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1327])).
% 4.56/2.17  tff(c_1331, plain, (![A_114, B_115]: (k2_pre_topc(A_114, B_115)=k2_struct_0(A_114) | ~v1_tops_1(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.56/2.17  tff(c_1342, plain, (![B_115]: (k2_pre_topc('#skF_1', B_115)=k2_struct_0('#skF_1') | ~v1_tops_1(B_115, '#skF_1') | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_1331])).
% 4.56/2.17  tff(c_1369, plain, (![B_118]: (k2_pre_topc('#skF_1', B_118)=k2_struct_0('#skF_1') | ~v1_tops_1(B_118, '#skF_1') | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1342])).
% 4.56/2.17  tff(c_1380, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_85, c_1369])).
% 4.56/2.17  tff(c_1391, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1353, c_1380])).
% 4.56/2.17  tff(c_150, plain, (![A_41, B_42]: (k3_subset_1(A_41, k3_subset_1(A_41, B_42))=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.56/2.17  tff(c_158, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_85, c_150])).
% 4.56/2.17  tff(c_1401, plain, (![A_119, B_120]: (v1_tops_1(k3_subset_1(u1_struct_0(A_119), B_120), A_119) | ~v3_tops_1(B_120, A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.56/2.17  tff(c_1412, plain, (![B_120]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_120), '#skF_1') | ~v3_tops_1(B_120, '#skF_1') | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_1401])).
% 4.56/2.17  tff(c_1436, plain, (![B_123]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_123), '#skF_1') | ~v3_tops_1(B_123, '#skF_1') | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_84, c_1412])).
% 4.56/2.17  tff(c_1447, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_1436])).
% 4.56/2.17  tff(c_1453, plain, (~v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1391, c_1447])).
% 4.56/2.17  tff(c_1746, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1453])).
% 4.56/2.17  tff(c_1749, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_1746])).
% 4.56/2.17  tff(c_1753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_1749])).
% 4.56/2.17  tff(c_1755, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1453])).
% 4.56/2.17  tff(c_40, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.56/2.17  tff(c_1785, plain, (![B_142, A_143]: (v4_pre_topc(B_142, A_143) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_143), B_142), A_143) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.56/2.17  tff(c_1803, plain, (![B_142]: (v4_pre_topc(B_142, '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_142), '#skF_1') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_1785])).
% 4.56/2.17  tff(c_1836, plain, (![B_146]: (v4_pre_topc(B_146, '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_146), '#skF_1') | ~m1_subset_1(B_146, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_84, c_1803])).
% 4.56/2.17  tff(c_1854, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_1836])).
% 4.56/2.17  tff(c_1862, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_40, c_1854])).
% 4.56/2.17  tff(c_38, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.56/2.17  tff(c_1418, plain, (![B_120]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_120), '#skF_1') | ~v3_tops_1(B_120, '#skF_1') | ~m1_subset_1(B_120, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_84, c_1412])).
% 4.56/2.17  tff(c_1276, plain, (![B_108]: (v1_tops_1(B_108, '#skF_1') | k2_pre_topc('#skF_1', B_108)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_108, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1268])).
% 4.56/2.17  tff(c_1779, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1755, c_1276])).
% 4.56/2.17  tff(c_1888, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1779])).
% 4.56/2.17  tff(c_1350, plain, (![B_115]: (k2_pre_topc('#skF_1', B_115)=k2_struct_0('#skF_1') | ~v1_tops_1(B_115, '#skF_1') | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1342])).
% 4.56/2.17  tff(c_1778, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1755, c_1350])).
% 4.56/2.17  tff(c_1915, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1888, c_1778])).
% 4.56/2.17  tff(c_1918, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1418, c_1915])).
% 4.56/2.17  tff(c_1922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_38, c_1918])).
% 4.56/2.17  tff(c_1924, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1779])).
% 4.56/2.17  tff(c_231, plain, (![A_48, B_49]: (k2_pre_topc(A_48, B_49)=B_49 | ~v4_pre_topc(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.56/2.17  tff(c_238, plain, (![B_49]: (k2_pre_topc('#skF_1', B_49)=B_49 | ~v4_pre_topc(B_49, '#skF_1') | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_231])).
% 4.56/2.17  tff(c_245, plain, (![B_49]: (k2_pre_topc('#skF_1', B_49)=B_49 | ~v4_pre_topc(B_49, '#skF_1') | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_238])).
% 4.56/2.17  tff(c_1780, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1755, c_245])).
% 4.56/2.17  tff(c_2002, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1862, c_1924, c_1780])).
% 4.56/2.17  tff(c_181, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k3_subset_1(A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.56/2.17  tff(c_192, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_85, c_181])).
% 4.56/2.17  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/2.17  tff(c_265, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_192, c_6])).
% 4.56/2.17  tff(c_1468, plain, (![A_125, B_126]: (k4_xboole_0(A_125, k3_subset_1(A_125, B_126))=k3_subset_1(A_125, k3_subset_1(A_125, B_126)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(resolution, [status(thm)], [c_14, c_181])).
% 4.56/2.17  tff(c_1474, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_85, c_1468])).
% 4.56/2.17  tff(c_1481, plain, (k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_265, c_1474])).
% 4.56/2.17  tff(c_1484, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1481, c_265])).
% 4.56/2.17  tff(c_2009, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2002, c_1484])).
% 4.56/2.17  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/2.17  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.56/2.17  tff(c_90, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/2.17  tff(c_105, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_90])).
% 4.56/2.17  tff(c_108, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_105])).
% 4.56/2.17  tff(c_2078, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2009, c_108])).
% 4.56/2.17  tff(c_2089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_2078])).
% 4.56/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/2.17  
% 4.56/2.17  Inference rules
% 4.56/2.17  ----------------------
% 4.56/2.17  #Ref     : 0
% 4.56/2.17  #Sup     : 432
% 4.56/2.17  #Fact    : 0
% 4.56/2.17  #Define  : 0
% 4.56/2.17  #Split   : 14
% 4.56/2.17  #Chain   : 0
% 4.56/2.17  #Close   : 0
% 4.56/2.17  
% 4.56/2.17  Ordering : KBO
% 4.56/2.17  
% 4.56/2.17  Simplification rules
% 4.56/2.17  ----------------------
% 4.56/2.17  #Subsume      : 45
% 4.56/2.17  #Demod        : 453
% 4.56/2.17  #Tautology    : 208
% 4.56/2.17  #SimpNegUnit  : 40
% 4.56/2.17  #BackRed      : 22
% 4.56/2.17  
% 4.56/2.17  #Partial instantiations: 0
% 4.56/2.17  #Strategies tried      : 1
% 4.56/2.17  
% 4.56/2.17  Timing (in seconds)
% 4.56/2.17  ----------------------
% 4.56/2.17  Preprocessing        : 0.49
% 4.56/2.17  Parsing              : 0.26
% 4.56/2.17  CNF conversion       : 0.04
% 4.56/2.17  Main loop            : 0.80
% 4.56/2.18  Inferencing          : 0.29
% 4.56/2.18  Reduction            : 0.28
% 4.56/2.18  Demodulation         : 0.20
% 4.56/2.18  BG Simplification    : 0.04
% 4.56/2.18  Subsumption          : 0.12
% 4.56/2.18  Abstraction          : 0.04
% 4.56/2.18  MUC search           : 0.00
% 4.56/2.18  Cooper               : 0.00
% 4.56/2.18  Total                : 1.33
% 4.56/2.18  Index Insertion      : 0.00
% 4.56/2.18  Index Deletion       : 0.00
% 4.56/2.18  Index Matching       : 0.00
% 4.56/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
