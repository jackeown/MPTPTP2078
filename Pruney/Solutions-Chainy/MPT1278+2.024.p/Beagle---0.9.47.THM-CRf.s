%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:11 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  104 (1007 expanded)
%              Number of leaves         :   35 ( 349 expanded)
%              Depth                    :   17
%              Number of atoms          :  177 (2475 expanded)
%              Number of equality atoms :   48 ( 597 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_33,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

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

tff(f_27,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_79,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_18,c_74])).

tff(c_83,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_84,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_40])).

tff(c_38,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1676,plain,(
    ! [A_150,B_151] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_150),B_151),A_150)
      | ~ v3_pre_topc(B_151,A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1690,plain,(
    ! [B_151] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_151),'#skF_1')
      | ~ v3_pre_topc(B_151,'#skF_1')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1676])).

tff(c_1699,plain,(
    ! [B_151] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_151),'#skF_1')
      | ~ v3_pre_topc(B_151,'#skF_1')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_83,c_1690])).

tff(c_36,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1568,plain,(
    ! [A_143,B_144] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_143),B_144),A_143)
      | ~ v3_tops_1(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1579,plain,(
    ! [B_144] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_144),'#skF_1')
      | ~ v3_tops_1(B_144,'#skF_1')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1568])).

tff(c_1587,plain,(
    ! [B_144] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_144),'#skF_1')
      | ~ v3_tops_1(B_144,'#skF_1')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_83,c_1579])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1283,plain,(
    ! [B_121,A_122] :
      ( v1_tops_1(B_121,A_122)
      | k2_pre_topc(A_122,B_121) != k2_struct_0(A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1294,plain,(
    ! [B_121] :
      ( v1_tops_1(B_121,'#skF_1')
      | k2_pre_topc('#skF_1',B_121) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1283])).

tff(c_1307,plain,(
    ! [B_124] :
      ( v1_tops_1(B_124,'#skF_1')
      | k2_pre_topc('#skF_1',B_124) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1294])).

tff(c_1327,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_1307])).

tff(c_1329,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1327])).

tff(c_1331,plain,(
    ! [A_125,B_126] :
      ( k2_pre_topc(A_125,B_126) = k2_struct_0(A_125)
      | ~ v1_tops_1(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1342,plain,(
    ! [B_126] :
      ( k2_pre_topc('#skF_1',B_126) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_126,'#skF_1')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1331])).

tff(c_1373,plain,(
    ! [B_130] :
      ( k2_pre_topc('#skF_1',B_130) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_130,'#skF_1')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1342])).

tff(c_1384,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_1373])).

tff(c_1395,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1329,c_1384])).

tff(c_89,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_89])).

tff(c_1607,plain,(
    ! [B_147] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_147),'#skF_1')
      | ~ v3_tops_1(B_147,'#skF_1')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_83,c_1579])).

tff(c_1614,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1607])).

tff(c_1623,plain,
    ( ~ v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1395,c_1614])).

tff(c_1666,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1623])).

tff(c_1669,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_1666])).

tff(c_1673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1669])).

tff(c_1675,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1623])).

tff(c_1350,plain,(
    ! [B_126] :
      ( k2_pre_topc('#skF_1',B_126) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_126,'#skF_1')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1342])).

tff(c_1719,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1675,c_1350])).

tff(c_1825,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1719])).

tff(c_1828,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1587,c_1825])).

tff(c_1832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_36,c_1828])).

tff(c_1833,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1719])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1484,plain,(
    ! [B_136,A_137] :
      ( v4_pre_topc(B_136,A_137)
      | k2_pre_topc(A_137,B_136) != B_136
      | ~ v2_pre_topc(A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1495,plain,(
    ! [B_136] :
      ( v4_pre_topc(B_136,'#skF_1')
      | k2_pre_topc('#skF_1',B_136) != B_136
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1484])).

tff(c_1503,plain,(
    ! [B_136] :
      ( v4_pre_topc(B_136,'#skF_1')
      | k2_pre_topc('#skF_1',B_136) != B_136
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1495])).

tff(c_1718,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1675,c_1503])).

tff(c_1866,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_1718])).

tff(c_1867,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1866])).

tff(c_170,plain,(
    ! [A_51,B_52] :
      ( k2_pre_topc(A_51,B_52) = B_52
      | ~ v4_pre_topc(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_181,plain,(
    ! [B_52] :
      ( k2_pre_topc('#skF_1',B_52) = B_52
      | ~ v4_pre_topc(B_52,'#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_170])).

tff(c_189,plain,(
    ! [B_52] :
      ( k2_pre_topc('#skF_1',B_52) = B_52
      | ~ v4_pre_topc(B_52,'#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_181])).

tff(c_1721,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1675,c_189])).

tff(c_1898,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_1721])).

tff(c_1899,plain,(
    ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1867,c_1898])).

tff(c_1902,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1699,c_1899])).

tff(c_1906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_38,c_1902])).

tff(c_1908,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1866])).

tff(c_1922,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_94])).

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

tff(c_46,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_96,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_93])).

tff(c_1989,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1922,c_96])).

tff(c_2013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:16:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.71  
% 3.71/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.71  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.71/1.71  
% 3.71/1.71  %Foreground sorts:
% 3.71/1.71  
% 3.71/1.71  
% 3.71/1.71  %Background operators:
% 3.71/1.71  
% 3.71/1.71  
% 3.71/1.71  %Foreground operators:
% 3.71/1.71  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.71/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.71/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.71/1.71  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.71/1.71  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.71/1.71  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.71/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.71/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.71/1.71  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.71/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.71  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.71/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.71/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.71/1.71  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.71/1.71  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.71/1.71  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.71/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.71  
% 3.71/1.73  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 3.71/1.73  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.71/1.73  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.71/1.73  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 3.71/1.73  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 3.71/1.73  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.71/1.73  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.71/1.73  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.71/1.73  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.71/1.73  tff(f_27, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.71/1.73  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.71/1.73  tff(f_39, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.71/1.73  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.71/1.73  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.71/1.73  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.71/1.73  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.71/1.73  tff(c_74, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.71/1.73  tff(c_79, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_18, c_74])).
% 3.71/1.73  tff(c_83, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_79])).
% 3.71/1.73  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.71/1.73  tff(c_84, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_40])).
% 3.71/1.73  tff(c_38, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.71/1.73  tff(c_1676, plain, (![A_150, B_151]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_150), B_151), A_150) | ~v3_pre_topc(B_151, A_150) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.71/1.73  tff(c_1690, plain, (![B_151]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_151), '#skF_1') | ~v3_pre_topc(B_151, '#skF_1') | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_1676])).
% 3.71/1.73  tff(c_1699, plain, (![B_151]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_151), '#skF_1') | ~v3_pre_topc(B_151, '#skF_1') | ~m1_subset_1(B_151, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_83, c_1690])).
% 3.71/1.73  tff(c_36, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.71/1.73  tff(c_1568, plain, (![A_143, B_144]: (v1_tops_1(k3_subset_1(u1_struct_0(A_143), B_144), A_143) | ~v3_tops_1(B_144, A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.71/1.73  tff(c_1579, plain, (![B_144]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_144), '#skF_1') | ~v3_tops_1(B_144, '#skF_1') | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_1568])).
% 3.71/1.73  tff(c_1587, plain, (![B_144]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_144), '#skF_1') | ~v3_tops_1(B_144, '#skF_1') | ~m1_subset_1(B_144, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_83, c_1579])).
% 3.71/1.73  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.71/1.73  tff(c_1283, plain, (![B_121, A_122]: (v1_tops_1(B_121, A_122) | k2_pre_topc(A_122, B_121)!=k2_struct_0(A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.71/1.73  tff(c_1294, plain, (![B_121]: (v1_tops_1(B_121, '#skF_1') | k2_pre_topc('#skF_1', B_121)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_121, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_1283])).
% 3.71/1.73  tff(c_1307, plain, (![B_124]: (v1_tops_1(B_124, '#skF_1') | k2_pre_topc('#skF_1', B_124)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1294])).
% 3.71/1.73  tff(c_1327, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_1307])).
% 3.71/1.73  tff(c_1329, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1327])).
% 3.71/1.73  tff(c_1331, plain, (![A_125, B_126]: (k2_pre_topc(A_125, B_126)=k2_struct_0(A_125) | ~v1_tops_1(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.71/1.73  tff(c_1342, plain, (![B_126]: (k2_pre_topc('#skF_1', B_126)=k2_struct_0('#skF_1') | ~v1_tops_1(B_126, '#skF_1') | ~m1_subset_1(B_126, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_1331])).
% 3.71/1.73  tff(c_1373, plain, (![B_130]: (k2_pre_topc('#skF_1', B_130)=k2_struct_0('#skF_1') | ~v1_tops_1(B_130, '#skF_1') | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1342])).
% 3.71/1.73  tff(c_1384, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_1373])).
% 3.71/1.73  tff(c_1395, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1329, c_1384])).
% 3.71/1.73  tff(c_89, plain, (![A_34, B_35]: (k3_subset_1(A_34, k3_subset_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.71/1.73  tff(c_94, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_84, c_89])).
% 3.71/1.73  tff(c_1607, plain, (![B_147]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_147), '#skF_1') | ~v3_tops_1(B_147, '#skF_1') | ~m1_subset_1(B_147, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_83, c_1579])).
% 3.71/1.73  tff(c_1614, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1607])).
% 3.71/1.73  tff(c_1623, plain, (~v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1395, c_1614])).
% 3.71/1.73  tff(c_1666, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1623])).
% 3.71/1.73  tff(c_1669, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1666])).
% 3.71/1.73  tff(c_1673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1669])).
% 3.71/1.73  tff(c_1675, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1623])).
% 3.71/1.73  tff(c_1350, plain, (![B_126]: (k2_pre_topc('#skF_1', B_126)=k2_struct_0('#skF_1') | ~v1_tops_1(B_126, '#skF_1') | ~m1_subset_1(B_126, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1342])).
% 3.71/1.73  tff(c_1719, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1675, c_1350])).
% 3.71/1.73  tff(c_1825, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1719])).
% 3.71/1.73  tff(c_1828, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1587, c_1825])).
% 3.71/1.73  tff(c_1832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_36, c_1828])).
% 3.71/1.73  tff(c_1833, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1719])).
% 3.71/1.73  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.71/1.73  tff(c_1484, plain, (![B_136, A_137]: (v4_pre_topc(B_136, A_137) | k2_pre_topc(A_137, B_136)!=B_136 | ~v2_pre_topc(A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.73  tff(c_1495, plain, (![B_136]: (v4_pre_topc(B_136, '#skF_1') | k2_pre_topc('#skF_1', B_136)!=B_136 | ~v2_pre_topc('#skF_1') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_1484])).
% 3.71/1.73  tff(c_1503, plain, (![B_136]: (v4_pre_topc(B_136, '#skF_1') | k2_pre_topc('#skF_1', B_136)!=B_136 | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1495])).
% 3.71/1.73  tff(c_1718, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_1675, c_1503])).
% 3.71/1.73  tff(c_1866, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1833, c_1718])).
% 3.71/1.73  tff(c_1867, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1866])).
% 3.71/1.73  tff(c_170, plain, (![A_51, B_52]: (k2_pre_topc(A_51, B_52)=B_52 | ~v4_pre_topc(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.73  tff(c_181, plain, (![B_52]: (k2_pre_topc('#skF_1', B_52)=B_52 | ~v4_pre_topc(B_52, '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_170])).
% 3.71/1.73  tff(c_189, plain, (![B_52]: (k2_pre_topc('#skF_1', B_52)=B_52 | ~v4_pre_topc(B_52, '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_181])).
% 3.71/1.73  tff(c_1721, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1675, c_189])).
% 3.71/1.73  tff(c_1898, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1833, c_1721])).
% 3.71/1.73  tff(c_1899, plain, (~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1867, c_1898])).
% 3.71/1.73  tff(c_1902, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1699, c_1899])).
% 3.71/1.73  tff(c_1906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_38, c_1902])).
% 3.71/1.73  tff(c_1908, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1866])).
% 3.71/1.73  tff(c_1922, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1908, c_94])).
% 3.71/1.73  tff(c_2, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.71/1.73  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.71/1.73  tff(c_10, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.71/1.73  tff(c_45, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 3.71/1.73  tff(c_46, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_45])).
% 3.71/1.73  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.71/1.73  tff(c_93, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_89])).
% 3.71/1.73  tff(c_96, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_93])).
% 3.71/1.73  tff(c_1989, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1922, c_96])).
% 3.71/1.73  tff(c_2013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1989])).
% 3.71/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.73  
% 3.71/1.73  Inference rules
% 3.71/1.73  ----------------------
% 3.71/1.73  #Ref     : 0
% 3.71/1.73  #Sup     : 378
% 3.71/1.73  #Fact    : 0
% 3.71/1.73  #Define  : 0
% 3.71/1.73  #Split   : 21
% 3.71/1.73  #Chain   : 0
% 3.71/1.73  #Close   : 0
% 3.71/1.73  
% 3.71/1.73  Ordering : KBO
% 3.71/1.73  
% 3.71/1.73  Simplification rules
% 3.71/1.73  ----------------------
% 3.71/1.73  #Subsume      : 67
% 3.71/1.73  #Demod        : 320
% 3.71/1.73  #Tautology    : 135
% 3.71/1.73  #SimpNegUnit  : 52
% 3.71/1.73  #BackRed      : 16
% 3.71/1.73  
% 3.71/1.73  #Partial instantiations: 0
% 3.71/1.73  #Strategies tried      : 1
% 3.71/1.73  
% 3.71/1.73  Timing (in seconds)
% 3.71/1.73  ----------------------
% 3.71/1.74  Preprocessing        : 0.33
% 3.71/1.74  Parsing              : 0.19
% 3.71/1.74  CNF conversion       : 0.02
% 3.71/1.74  Main loop            : 0.56
% 3.71/1.74  Inferencing          : 0.20
% 3.71/1.74  Reduction            : 0.19
% 3.71/1.74  Demodulation         : 0.13
% 3.71/1.74  BG Simplification    : 0.02
% 3.71/1.74  Subsumption          : 0.09
% 3.71/1.74  Abstraction          : 0.02
% 3.71/1.74  MUC search           : 0.00
% 3.71/1.74  Cooper               : 0.00
% 3.71/1.74  Total                : 0.93
% 3.71/1.74  Index Insertion      : 0.00
% 3.71/1.74  Index Deletion       : 0.00
% 3.71/1.74  Index Matching       : 0.00
% 3.71/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
