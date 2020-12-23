%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:03 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 605 expanded)
%              Number of leaves         :   42 ( 221 expanded)
%              Depth                    :   18
%              Number of atoms          :  201 (1363 expanded)
%              Number of equality atoms :   52 ( 350 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_80,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_82,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_24,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_72,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_72])).

tff(c_81,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_83,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_48])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_88,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_58])).

tff(c_462,plain,(
    ! [B_94,A_95] :
      ( v2_tops_1(B_94,A_95)
      | ~ r1_tarski(B_94,k2_tops_1(A_95,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_468,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_462])).

tff(c_476,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_81,c_6,c_468])).

tff(c_46,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_672,plain,(
    ! [B_111,A_112] :
      ( v3_tops_1(B_111,A_112)
      | ~ v4_pre_topc(B_111,A_112)
      | ~ v2_tops_1(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_683,plain,(
    ! [B_111] :
      ( v3_tops_1(B_111,'#skF_1')
      | ~ v4_pre_topc(B_111,'#skF_1')
      | ~ v2_tops_1(B_111,'#skF_1')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_672])).

tff(c_717,plain,(
    ! [B_115] :
      ( v3_tops_1(B_115,'#skF_1')
      | ~ v4_pre_topc(B_115,'#skF_1')
      | ~ v2_tops_1(B_115,'#skF_1')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_683])).

tff(c_728,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_83,c_717])).

tff(c_738,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_46,c_728])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_738])).

tff(c_741,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_748,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_48])).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_760,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(A_118,B_119) = k3_subset_1(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_766,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = k3_subset_1(A_13,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_760])).

tff(c_769,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_766])).

tff(c_791,plain,(
    ! [A_126,B_127] :
      ( k3_subset_1(A_126,k3_subset_1(A_126,B_127)) = B_127
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_795,plain,(
    ! [A_13] : k3_subset_1(A_13,k3_subset_1(A_13,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_791])).

tff(c_798,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_795])).

tff(c_742,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1301,plain,(
    ! [A_179,B_180] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_179),B_180),A_179)
      | ~ v3_tops_1(B_180,A_179)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1316,plain,(
    ! [B_180] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_180),'#skF_1')
      | ~ v3_tops_1(B_180,'#skF_1')
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_1301])).

tff(c_1322,plain,(
    ! [B_180] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_180),'#skF_1')
      | ~ v3_tops_1(B_180,'#skF_1')
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_81,c_1316])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_898,plain,(
    ! [A_141,B_142] :
      ( k2_pre_topc(A_141,B_142) = B_142
      | ~ v4_pre_topc(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_909,plain,(
    ! [B_142] :
      ( k2_pre_topc('#skF_1',B_142) = B_142
      | ~ v4_pre_topc(B_142,'#skF_1')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_898])).

tff(c_948,plain,(
    ! [B_147] :
      ( k2_pre_topc('#skF_1',B_147) = B_147
      | ~ v4_pre_topc(B_147,'#skF_1')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_909])).

tff(c_959,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_748,c_948])).

tff(c_968,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_959])).

tff(c_976,plain,(
    ! [A_148,B_149] :
      ( k2_pre_topc(A_148,B_149) = k2_struct_0(A_148)
      | ~ v1_tops_1(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_987,plain,(
    ! [B_149] :
      ( k2_pre_topc('#skF_1',B_149) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_149,'#skF_1')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_976])).

tff(c_1025,plain,(
    ! [B_156] :
      ( k2_pre_topc('#skF_1',B_156) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_156,'#skF_1')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_987])).

tff(c_1036,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_748,c_1025])).

tff(c_1044,plain,
    ( k2_struct_0('#skF_1') = '#skF_2'
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_1036])).

tff(c_1046,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1044])).

tff(c_796,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_748,c_791])).

tff(c_1373,plain,(
    ! [B_186] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_186),'#skF_1')
      | ~ v3_tops_1(B_186,'#skF_1')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_81,c_1316])).

tff(c_1383,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_1373])).

tff(c_1393,plain,
    ( ~ v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1046,c_1383])).

tff(c_1495,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1393])).

tff(c_1498,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_1495])).

tff(c_1502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_1498])).

tff(c_1504,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1393])).

tff(c_995,plain,(
    ! [B_149] :
      ( k2_pre_topc('#skF_1',B_149) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_149,'#skF_1')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_987])).

tff(c_1541,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1504,c_995])).

tff(c_1600,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1541])).

tff(c_1603,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1322,c_1600])).

tff(c_1607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_742,c_1603])).

tff(c_1608,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1541])).

tff(c_1631,plain,(
    ! [A_199,B_200] :
      ( k3_subset_1(u1_struct_0(A_199),k2_pre_topc(A_199,k3_subset_1(u1_struct_0(A_199),B_200))) = k1_tops_1(A_199,B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1670,plain,(
    ! [B_200] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_200))) = k1_tops_1('#skF_1',B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_1631])).

tff(c_1864,plain,(
    ! [B_206] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_206))) = k1_tops_1('#skF_1',B_206)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_81,c_81,c_1670])).

tff(c_1900,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_1864])).

tff(c_1919,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_798,c_1900])).

tff(c_876,plain,(
    ! [A_136,B_137,C_138] :
      ( k7_subset_1(A_136,B_137,C_138) = k4_xboole_0(B_137,C_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_887,plain,(
    ! [C_138] : k7_subset_1(k2_struct_0('#skF_1'),'#skF_2',C_138) = k4_xboole_0('#skF_2',C_138) ),
    inference(resolution,[status(thm)],[c_748,c_876])).

tff(c_1551,plain,(
    ! [A_196,B_197] :
      ( k7_subset_1(u1_struct_0(A_196),k2_pre_topc(A_196,B_197),k1_tops_1(A_196,B_197)) = k2_tops_1(A_196,B_197)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1563,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_1551])).

tff(c_1572,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_748,c_81,c_887,c_81,c_1563])).

tff(c_1926,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1919,c_1572])).

tff(c_1927,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1926])).

tff(c_1929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_741,c_1927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:45:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.66  
% 3.84/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.67  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.84/1.67  
% 3.84/1.67  %Foreground sorts:
% 3.84/1.67  
% 3.84/1.67  
% 3.84/1.67  %Background operators:
% 3.84/1.67  
% 3.84/1.67  
% 3.84/1.67  %Foreground operators:
% 3.84/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.84/1.67  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.84/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.67  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.84/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.84/1.67  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.84/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.84/1.67  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.84/1.67  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.84/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.84/1.67  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.84/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.84/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.84/1.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.84/1.67  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.84/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.84/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.84/1.67  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.84/1.67  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.84/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.84/1.67  
% 3.84/1.69  tff(f_144, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.84/1.69  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.84/1.69  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.84/1.69  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.84/1.69  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.84/1.69  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 3.84/1.69  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.84/1.69  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.84/1.69  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.84/1.69  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.84/1.69  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 3.84/1.69  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.84/1.69  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.84/1.69  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.84/1.69  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.84/1.69  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.84/1.69  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.84/1.69  tff(c_52, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.84/1.69  tff(c_82, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 3.84/1.69  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.84/1.69  tff(c_24, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.84/1.69  tff(c_72, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.84/1.69  tff(c_77, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_24, c_72])).
% 3.84/1.69  tff(c_81, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_77])).
% 3.84/1.69  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.84/1.69  tff(c_83, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_48])).
% 3.84/1.69  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.84/1.69  tff(c_58, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.84/1.69  tff(c_88, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_58])).
% 3.84/1.69  tff(c_462, plain, (![B_94, A_95]: (v2_tops_1(B_94, A_95) | ~r1_tarski(B_94, k2_tops_1(A_95, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.84/1.69  tff(c_468, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_88, c_462])).
% 3.84/1.69  tff(c_476, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_81, c_6, c_468])).
% 3.84/1.69  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.84/1.69  tff(c_672, plain, (![B_111, A_112]: (v3_tops_1(B_111, A_112) | ~v4_pre_topc(B_111, A_112) | ~v2_tops_1(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.84/1.69  tff(c_683, plain, (![B_111]: (v3_tops_1(B_111, '#skF_1') | ~v4_pre_topc(B_111, '#skF_1') | ~v2_tops_1(B_111, '#skF_1') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_672])).
% 3.84/1.69  tff(c_717, plain, (![B_115]: (v3_tops_1(B_115, '#skF_1') | ~v4_pre_topc(B_115, '#skF_1') | ~v2_tops_1(B_115, '#skF_1') | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_683])).
% 3.84/1.69  tff(c_728, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_83, c_717])).
% 3.84/1.69  tff(c_738, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_46, c_728])).
% 3.84/1.69  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_738])).
% 3.84/1.69  tff(c_741, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 3.84/1.69  tff(c_8, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.84/1.69  tff(c_748, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_48])).
% 3.84/1.69  tff(c_18, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.84/1.69  tff(c_760, plain, (![A_118, B_119]: (k4_xboole_0(A_118, B_119)=k3_subset_1(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.84/1.69  tff(c_766, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=k3_subset_1(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_760])).
% 3.84/1.69  tff(c_769, plain, (![A_13]: (k3_subset_1(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_766])).
% 3.84/1.69  tff(c_791, plain, (![A_126, B_127]: (k3_subset_1(A_126, k3_subset_1(A_126, B_127))=B_127 | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.84/1.69  tff(c_795, plain, (![A_13]: (k3_subset_1(A_13, k3_subset_1(A_13, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_791])).
% 3.84/1.69  tff(c_798, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_769, c_795])).
% 3.84/1.69  tff(c_742, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 3.84/1.69  tff(c_1301, plain, (![A_179, B_180]: (v1_tops_1(k3_subset_1(u1_struct_0(A_179), B_180), A_179) | ~v3_tops_1(B_180, A_179) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.84/1.69  tff(c_1316, plain, (![B_180]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_180), '#skF_1') | ~v3_tops_1(B_180, '#skF_1') | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_1301])).
% 3.84/1.69  tff(c_1322, plain, (![B_180]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_180), '#skF_1') | ~v3_tops_1(B_180, '#skF_1') | ~m1_subset_1(B_180, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_81, c_1316])).
% 3.84/1.69  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.84/1.69  tff(c_898, plain, (![A_141, B_142]: (k2_pre_topc(A_141, B_142)=B_142 | ~v4_pre_topc(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.84/1.69  tff(c_909, plain, (![B_142]: (k2_pre_topc('#skF_1', B_142)=B_142 | ~v4_pre_topc(B_142, '#skF_1') | ~m1_subset_1(B_142, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_898])).
% 3.84/1.69  tff(c_948, plain, (![B_147]: (k2_pre_topc('#skF_1', B_147)=B_147 | ~v4_pre_topc(B_147, '#skF_1') | ~m1_subset_1(B_147, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_909])).
% 3.84/1.69  tff(c_959, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_748, c_948])).
% 3.84/1.69  tff(c_968, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_959])).
% 3.84/1.69  tff(c_976, plain, (![A_148, B_149]: (k2_pre_topc(A_148, B_149)=k2_struct_0(A_148) | ~v1_tops_1(B_149, A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.84/1.69  tff(c_987, plain, (![B_149]: (k2_pre_topc('#skF_1', B_149)=k2_struct_0('#skF_1') | ~v1_tops_1(B_149, '#skF_1') | ~m1_subset_1(B_149, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_976])).
% 3.84/1.69  tff(c_1025, plain, (![B_156]: (k2_pre_topc('#skF_1', B_156)=k2_struct_0('#skF_1') | ~v1_tops_1(B_156, '#skF_1') | ~m1_subset_1(B_156, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_987])).
% 3.84/1.69  tff(c_1036, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_748, c_1025])).
% 3.84/1.69  tff(c_1044, plain, (k2_struct_0('#skF_1')='#skF_2' | ~v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_1036])).
% 3.84/1.69  tff(c_1046, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1044])).
% 3.84/1.69  tff(c_796, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_748, c_791])).
% 3.84/1.69  tff(c_1373, plain, (![B_186]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_186), '#skF_1') | ~v3_tops_1(B_186, '#skF_1') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_81, c_1316])).
% 3.84/1.69  tff(c_1383, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_796, c_1373])).
% 3.84/1.69  tff(c_1393, plain, (~v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1046, c_1383])).
% 3.84/1.69  tff(c_1495, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1393])).
% 3.84/1.69  tff(c_1498, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_1495])).
% 3.84/1.69  tff(c_1502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_748, c_1498])).
% 3.84/1.69  tff(c_1504, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1393])).
% 3.84/1.69  tff(c_995, plain, (![B_149]: (k2_pre_topc('#skF_1', B_149)=k2_struct_0('#skF_1') | ~v1_tops_1(B_149, '#skF_1') | ~m1_subset_1(B_149, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_987])).
% 3.84/1.69  tff(c_1541, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1504, c_995])).
% 3.84/1.69  tff(c_1600, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1541])).
% 3.84/1.69  tff(c_1603, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1322, c_1600])).
% 3.84/1.69  tff(c_1607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_748, c_742, c_1603])).
% 3.84/1.69  tff(c_1608, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1541])).
% 3.84/1.69  tff(c_1631, plain, (![A_199, B_200]: (k3_subset_1(u1_struct_0(A_199), k2_pre_topc(A_199, k3_subset_1(u1_struct_0(A_199), B_200)))=k1_tops_1(A_199, B_200) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.84/1.69  tff(c_1670, plain, (![B_200]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_200)))=k1_tops_1('#skF_1', B_200) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_1631])).
% 3.84/1.69  tff(c_1864, plain, (![B_206]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_206)))=k1_tops_1('#skF_1', B_206) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_81, c_81, c_1670])).
% 3.84/1.69  tff(c_1900, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1608, c_1864])).
% 3.84/1.69  tff(c_1919, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_748, c_798, c_1900])).
% 3.84/1.69  tff(c_876, plain, (![A_136, B_137, C_138]: (k7_subset_1(A_136, B_137, C_138)=k4_xboole_0(B_137, C_138) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.84/1.69  tff(c_887, plain, (![C_138]: (k7_subset_1(k2_struct_0('#skF_1'), '#skF_2', C_138)=k4_xboole_0('#skF_2', C_138))), inference(resolution, [status(thm)], [c_748, c_876])).
% 3.84/1.69  tff(c_1551, plain, (![A_196, B_197]: (k7_subset_1(u1_struct_0(A_196), k2_pre_topc(A_196, B_197), k1_tops_1(A_196, B_197))=k2_tops_1(A_196, B_197) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.84/1.69  tff(c_1563, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_968, c_1551])).
% 3.84/1.69  tff(c_1572, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_748, c_81, c_887, c_81, c_1563])).
% 3.84/1.69  tff(c_1926, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1919, c_1572])).
% 3.84/1.69  tff(c_1927, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1926])).
% 3.84/1.69  tff(c_1929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_741, c_1927])).
% 3.84/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.69  
% 3.84/1.69  Inference rules
% 3.84/1.69  ----------------------
% 3.84/1.69  #Ref     : 0
% 3.84/1.69  #Sup     : 408
% 3.84/1.69  #Fact    : 0
% 3.84/1.69  #Define  : 0
% 3.84/1.69  #Split   : 24
% 3.84/1.69  #Chain   : 0
% 3.84/1.69  #Close   : 0
% 3.84/1.69  
% 3.84/1.69  Ordering : KBO
% 3.84/1.69  
% 3.84/1.69  Simplification rules
% 3.84/1.69  ----------------------
% 3.84/1.69  #Subsume      : 46
% 3.84/1.69  #Demod        : 242
% 3.84/1.69  #Tautology    : 154
% 3.84/1.69  #SimpNegUnit  : 32
% 3.84/1.69  #BackRed      : 4
% 3.84/1.69  
% 3.84/1.69  #Partial instantiations: 0
% 3.84/1.69  #Strategies tried      : 1
% 3.84/1.69  
% 3.84/1.69  Timing (in seconds)
% 3.84/1.69  ----------------------
% 3.84/1.69  Preprocessing        : 0.35
% 3.84/1.69  Parsing              : 0.18
% 3.84/1.69  CNF conversion       : 0.02
% 3.84/1.69  Main loop            : 0.57
% 3.84/1.69  Inferencing          : 0.20
% 3.84/1.69  Reduction            : 0.19
% 3.84/1.69  Demodulation         : 0.13
% 3.84/1.69  BG Simplification    : 0.03
% 3.84/1.69  Subsumption          : 0.10
% 3.84/1.69  Abstraction          : 0.03
% 3.84/1.69  MUC search           : 0.00
% 3.84/1.69  Cooper               : 0.00
% 3.84/1.69  Total                : 0.96
% 3.84/1.69  Index Insertion      : 0.00
% 3.84/1.69  Index Deletion       : 0.00
% 3.84/1.69  Index Matching       : 0.00
% 3.84/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
