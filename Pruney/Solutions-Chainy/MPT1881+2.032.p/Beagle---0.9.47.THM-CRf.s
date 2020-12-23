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
% DateTime   : Thu Dec  3 10:30:10 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  144 (1029 expanded)
%              Number of leaves         :   38 ( 357 expanded)
%              Depth                    :   14
%              Number of atoms          :  325 (2717 expanded)
%              Number of equality atoms :   43 ( 403 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_34,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_57,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : ~ v1_subset_1(k2_subset_1(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_598,plain,(
    ! [A_117] :
      ( u1_struct_0(A_117) = k2_struct_0(A_117)
      | ~ l1_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_603,plain,(
    ! [A_118] :
      ( u1_struct_0(A_118) = k2_struct_0(A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_10,c_598])).

tff(c_607,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_603])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_609,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_42])).

tff(c_636,plain,(
    ! [A_125,B_126] :
      ( k2_pre_topc(A_125,B_126) = B_126
      | ~ v4_pre_topc(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_646,plain,(
    ! [B_126] :
      ( k2_pre_topc('#skF_2',B_126) = B_126
      | ~ v4_pre_topc(B_126,'#skF_2')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_636])).

tff(c_651,plain,(
    ! [B_127] :
      ( k2_pre_topc('#skF_2',B_127) = B_127
      | ~ v4_pre_topc(B_127,'#skF_2')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_646])).

tff(c_660,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_609,c_651])).

tff(c_661,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_660])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k3_subset_1(A_2,B_3),k1_zfmisc_1(A_2))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_46,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_663,plain,(
    ! [B_130,A_131] :
      ( v3_pre_topc(B_130,A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v1_tdlat_3(A_131)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_673,plain,(
    ! [B_130] :
      ( v3_pre_topc(B_130,'#skF_2')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_663])).

tff(c_693,plain,(
    ! [B_134] :
      ( v3_pre_topc(B_134,'#skF_2')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_673])).

tff(c_701,plain,(
    ! [B_3] :
      ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),B_3),'#skF_2')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_693])).

tff(c_782,plain,(
    ! [B_147,A_148] :
      ( v4_pre_topc(B_147,A_148)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_148),B_147),A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_788,plain,(
    ! [B_147] :
      ( v4_pre_topc(B_147,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),B_147),'#skF_2')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_782])).

tff(c_792,plain,(
    ! [B_149] :
      ( v4_pre_topc(B_149,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'),B_149),'#skF_2')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_607,c_788])).

tff(c_797,plain,(
    ! [B_150] :
      ( v4_pre_topc(B_150,'#skF_2')
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_701,c_792])).

tff(c_804,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_609,c_797])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_804])).

tff(c_810,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_843,plain,(
    ! [B_157,A_158] :
      ( v1_tops_1(B_157,A_158)
      | k2_pre_topc(A_158,B_157) != k2_struct_0(A_158)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_853,plain,(
    ! [B_157] :
      ( v1_tops_1(B_157,'#skF_2')
      | k2_pre_topc('#skF_2',B_157) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_843])).

tff(c_858,plain,(
    ! [B_159] :
      ( v1_tops_1(B_159,'#skF_2')
      | k2_pre_topc('#skF_2',B_159) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_159,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_853])).

tff(c_865,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_609,c_858])).

tff(c_868,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_865])).

tff(c_869,plain,(
    k2_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_870,plain,(
    ! [A_160,B_161] :
      ( k2_pre_topc(A_160,B_161) = k2_struct_0(A_160)
      | ~ v1_tops_1(B_161,A_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_880,plain,(
    ! [B_161] :
      ( k2_pre_topc('#skF_2',B_161) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_161,'#skF_2')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_870])).

tff(c_885,plain,(
    ! [B_162] :
      ( k2_pre_topc('#skF_2',B_162) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_162,'#skF_2')
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_880])).

tff(c_892,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_609,c_885])).

tff(c_895,plain,
    ( k2_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_892])).

tff(c_896,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_895])).

tff(c_812,plain,(
    ! [B_151,A_152] :
      ( v3_pre_topc(B_151,A_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ v1_tdlat_3(A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_822,plain,(
    ! [B_151] :
      ( v3_pre_topc(B_151,'#skF_2')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_812])).

tff(c_831,plain,(
    ! [B_153] :
      ( v3_pre_topc(B_153,'#skF_2')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_822])).

tff(c_840,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_609,c_831])).

tff(c_52,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_72,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_73,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_82,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_58,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_88,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_58])).

tff(c_89,plain,(
    ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_88])).

tff(c_83,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_42])).

tff(c_90,plain,(
    ! [B_39,A_40] :
      ( v1_subset_1(B_39,A_40)
      | B_39 = A_40
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_93,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_83,c_90])).

tff(c_96,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_93])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_83])).

tff(c_99,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_82])).

tff(c_132,plain,(
    ! [A_47,B_48] :
      ( k2_pre_topc(A_47,B_48) = B_48
      | ~ v4_pre_topc(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_142,plain,(
    ! [B_48] :
      ( k2_pre_topc('#skF_2',B_48) = B_48
      | ~ v4_pre_topc(B_48,'#skF_2')
      | ~ m1_subset_1(B_48,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_132])).

tff(c_173,plain,(
    ! [B_53] :
      ( k2_pre_topc('#skF_2',B_53) = B_53
      | ~ v4_pre_topc(B_53,'#skF_2')
      | ~ m1_subset_1(B_53,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_142])).

tff(c_182,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_173])).

tff(c_183,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_147,plain,(
    ! [B_49,A_50] :
      ( v3_pre_topc(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v1_tdlat_3(A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_157,plain,(
    ! [B_49] :
      ( v3_pre_topc(B_49,'#skF_2')
      | ~ m1_subset_1(B_49,k1_zfmisc_1('#skF_3'))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_147])).

tff(c_162,plain,(
    ! [B_51] :
      ( v3_pre_topc(B_51,'#skF_2')
      | ~ m1_subset_1(B_51,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_157])).

tff(c_170,plain,(
    ! [B_3] :
      ( v3_pre_topc(k3_subset_1('#skF_3',B_3),'#skF_2')
      | ~ m1_subset_1(B_3,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_255,plain,(
    ! [B_65,A_66] :
      ( v4_pre_topc(B_65,A_66)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_66),B_65),A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_261,plain,(
    ! [B_65] :
      ( v4_pre_topc(B_65,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1('#skF_3',B_65),'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_255])).

tff(c_265,plain,(
    ! [B_67] :
      ( v4_pre_topc(B_67,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1('#skF_3',B_67),'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_99,c_261])).

tff(c_296,plain,(
    ! [B_71] :
      ( v4_pre_topc(B_71,'#skF_2')
      | ~ m1_subset_1(B_71,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_170,c_265])).

tff(c_303,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_296])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_303])).

tff(c_309,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_315,plain,(
    ! [B_72,A_73] :
      ( v1_tops_1(B_72,A_73)
      | k2_pre_topc(A_73,B_72) != k2_struct_0(A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_325,plain,(
    ! [B_72] :
      ( v1_tops_1(B_72,'#skF_2')
      | k2_pre_topc('#skF_2',B_72) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_315])).

tff(c_330,plain,(
    ! [B_74] :
      ( v1_tops_1(B_74,'#skF_2')
      | k2_pre_topc('#skF_2',B_74) != '#skF_3'
      | ~ m1_subset_1(B_74,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_96,c_325])).

tff(c_337,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_98,c_330])).

tff(c_341,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_337])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_419,plain,(
    ! [B_88,A_89] :
      ( v2_tex_2(B_88,A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v1_tdlat_3(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_429,plain,(
    ! [B_88] :
      ( v2_tex_2(B_88,'#skF_2')
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_419])).

tff(c_433,plain,(
    ! [B_88] :
      ( v2_tex_2(B_88,'#skF_2')
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_429])).

tff(c_445,plain,(
    ! [B_92] :
      ( v2_tex_2(B_92,'#skF_2')
      | ~ m1_subset_1(B_92,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_433])).

tff(c_454,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_445])).

tff(c_563,plain,(
    ! [B_113,A_114] :
      ( v3_tex_2(B_113,A_114)
      | ~ v2_tex_2(B_113,A_114)
      | ~ v1_tops_1(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_573,plain,(
    ! [B_113] :
      ( v3_tex_2(B_113,'#skF_2')
      | ~ v2_tex_2(B_113,'#skF_2')
      | ~ v1_tops_1(B_113,'#skF_2')
      | ~ m1_subset_1(B_113,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_563])).

tff(c_577,plain,(
    ! [B_113] :
      ( v3_tex_2(B_113,'#skF_2')
      | ~ v2_tex_2(B_113,'#skF_2')
      | ~ v1_tops_1(B_113,'#skF_2')
      | ~ m1_subset_1(B_113,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_573])).

tff(c_580,plain,(
    ! [B_116] :
      ( v3_tex_2(B_116,'#skF_2')
      | ~ v2_tex_2(B_116,'#skF_2')
      | ~ v1_tops_1(B_116,'#skF_2')
      | ~ m1_subset_1(B_116,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_577])).

tff(c_587,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_580])).

tff(c_591,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_454,c_587])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_591])).

tff(c_595,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1003,plain,(
    ! [B_183,A_184] :
      ( v1_tops_1(B_183,A_184)
      | ~ v3_tex_2(B_183,A_184)
      | ~ v3_pre_topc(B_183,A_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1013,plain,(
    ! [B_183] :
      ( v1_tops_1(B_183,'#skF_2')
      | ~ v3_tex_2(B_183,'#skF_2')
      | ~ v3_pre_topc(B_183,'#skF_2')
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_1003])).

tff(c_1017,plain,(
    ! [B_183] :
      ( v1_tops_1(B_183,'#skF_2')
      | ~ v3_tex_2(B_183,'#skF_2')
      | ~ v3_pre_topc(B_183,'#skF_2')
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1013])).

tff(c_1019,plain,(
    ! [B_185] :
      ( v1_tops_1(B_185,'#skF_2')
      | ~ v3_tex_2(B_185,'#skF_2')
      | ~ v3_pre_topc(B_185,'#skF_2')
      | ~ m1_subset_1(B_185,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1017])).

tff(c_1026,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_609,c_1019])).

tff(c_1030,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_595,c_1026])).

tff(c_1032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_896,c_1030])).

tff(c_1034,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_594,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_608,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_594])).

tff(c_1040,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_608])).

tff(c_1043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_1040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.51  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.21/1.51  
% 3.21/1.51  %Foreground sorts:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Background operators:
% 3.21/1.51  
% 3.21/1.51  
% 3.21/1.51  %Foreground operators:
% 3.21/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.51  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.51  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.21/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.21/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.51  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.21/1.51  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.21/1.51  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.21/1.51  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.21/1.51  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.21/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.21/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.51  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.21/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.21/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.21/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.51  
% 3.47/1.54  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.47/1.54  tff(f_34, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.47/1.54  tff(f_163, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 3.47/1.54  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.47/1.54  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.47/1.54  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.47/1.54  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.47/1.54  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 3.47/1.54  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 3.47/1.54  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.47/1.54  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.47/1.54  tff(f_113, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.47/1.54  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 3.47/1.54  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 3.47/1.54  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.47/1.54  tff(c_6, plain, (![A_4]: (~v1_subset_1(k2_subset_1(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.47/1.54  tff(c_59, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 3.47/1.54  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.47/1.54  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.47/1.54  tff(c_598, plain, (![A_117]: (u1_struct_0(A_117)=k2_struct_0(A_117) | ~l1_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.54  tff(c_603, plain, (![A_118]: (u1_struct_0(A_118)=k2_struct_0(A_118) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_10, c_598])).
% 3.47/1.54  tff(c_607, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_603])).
% 3.47/1.54  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.47/1.54  tff(c_609, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_42])).
% 3.47/1.54  tff(c_636, plain, (![A_125, B_126]: (k2_pre_topc(A_125, B_126)=B_126 | ~v4_pre_topc(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.47/1.54  tff(c_646, plain, (![B_126]: (k2_pre_topc('#skF_2', B_126)=B_126 | ~v4_pre_topc(B_126, '#skF_2') | ~m1_subset_1(B_126, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_636])).
% 3.47/1.54  tff(c_651, plain, (![B_127]: (k2_pre_topc('#skF_2', B_127)=B_127 | ~v4_pre_topc(B_127, '#skF_2') | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_646])).
% 3.47/1.54  tff(c_660, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_609, c_651])).
% 3.47/1.54  tff(c_661, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_660])).
% 3.47/1.54  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k3_subset_1(A_2, B_3), k1_zfmisc_1(A_2)) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.54  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.47/1.54  tff(c_46, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.47/1.54  tff(c_663, plain, (![B_130, A_131]: (v3_pre_topc(B_130, A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~v1_tdlat_3(A_131) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.54  tff(c_673, plain, (![B_130]: (v3_pre_topc(B_130, '#skF_2') | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_663])).
% 3.47/1.54  tff(c_693, plain, (![B_134]: (v3_pre_topc(B_134, '#skF_2') | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_673])).
% 3.47/1.54  tff(c_701, plain, (![B_3]: (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), B_3), '#skF_2') | ~m1_subset_1(B_3, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_693])).
% 3.47/1.54  tff(c_782, plain, (![B_147, A_148]: (v4_pre_topc(B_147, A_148) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_148), B_147), A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.47/1.54  tff(c_788, plain, (![B_147]: (v4_pre_topc(B_147, '#skF_2') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), B_147), '#skF_2') | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_782])).
% 3.47/1.54  tff(c_792, plain, (![B_149]: (v4_pre_topc(B_149, '#skF_2') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_2'), B_149), '#skF_2') | ~m1_subset_1(B_149, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_607, c_788])).
% 3.47/1.54  tff(c_797, plain, (![B_150]: (v4_pre_topc(B_150, '#skF_2') | ~m1_subset_1(B_150, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_701, c_792])).
% 3.47/1.54  tff(c_804, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_609, c_797])).
% 3.47/1.54  tff(c_809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_661, c_804])).
% 3.47/1.54  tff(c_810, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_660])).
% 3.47/1.54  tff(c_843, plain, (![B_157, A_158]: (v1_tops_1(B_157, A_158) | k2_pre_topc(A_158, B_157)!=k2_struct_0(A_158) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.54  tff(c_853, plain, (![B_157]: (v1_tops_1(B_157, '#skF_2') | k2_pre_topc('#skF_2', B_157)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_157, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_843])).
% 3.47/1.54  tff(c_858, plain, (![B_159]: (v1_tops_1(B_159, '#skF_2') | k2_pre_topc('#skF_2', B_159)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_159, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_853])).
% 3.47/1.54  tff(c_865, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_609, c_858])).
% 3.47/1.54  tff(c_868, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_810, c_865])).
% 3.47/1.54  tff(c_869, plain, (k2_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_868])).
% 3.47/1.54  tff(c_870, plain, (![A_160, B_161]: (k2_pre_topc(A_160, B_161)=k2_struct_0(A_160) | ~v1_tops_1(B_161, A_160) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.54  tff(c_880, plain, (![B_161]: (k2_pre_topc('#skF_2', B_161)=k2_struct_0('#skF_2') | ~v1_tops_1(B_161, '#skF_2') | ~m1_subset_1(B_161, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_870])).
% 3.47/1.54  tff(c_885, plain, (![B_162]: (k2_pre_topc('#skF_2', B_162)=k2_struct_0('#skF_2') | ~v1_tops_1(B_162, '#skF_2') | ~m1_subset_1(B_162, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_880])).
% 3.47/1.54  tff(c_892, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_609, c_885])).
% 3.47/1.54  tff(c_895, plain, (k2_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_810, c_892])).
% 3.47/1.54  tff(c_896, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_869, c_895])).
% 3.47/1.54  tff(c_812, plain, (![B_151, A_152]: (v3_pre_topc(B_151, A_152) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~v1_tdlat_3(A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.54  tff(c_822, plain, (![B_151]: (v3_pre_topc(B_151, '#skF_2') | ~m1_subset_1(B_151, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_812])).
% 3.47/1.54  tff(c_831, plain, (![B_153]: (v3_pre_topc(B_153, '#skF_2') | ~m1_subset_1(B_153, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_822])).
% 3.47/1.54  tff(c_840, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_609, c_831])).
% 3.47/1.54  tff(c_52, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.47/1.54  tff(c_72, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 3.47/1.54  tff(c_73, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.54  tff(c_78, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_10, c_73])).
% 3.47/1.54  tff(c_82, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_78])).
% 3.47/1.54  tff(c_58, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.47/1.54  tff(c_88, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_58])).
% 3.47/1.54  tff(c_89, plain, (~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_88])).
% 3.47/1.54  tff(c_83, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_42])).
% 3.47/1.54  tff(c_90, plain, (![B_39, A_40]: (v1_subset_1(B_39, A_40) | B_39=A_40 | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.54  tff(c_93, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_83, c_90])).
% 3.47/1.54  tff(c_96, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_89, c_93])).
% 3.47/1.54  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_83])).
% 3.47/1.54  tff(c_99, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_82])).
% 3.47/1.54  tff(c_132, plain, (![A_47, B_48]: (k2_pre_topc(A_47, B_48)=B_48 | ~v4_pre_topc(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.47/1.54  tff(c_142, plain, (![B_48]: (k2_pre_topc('#skF_2', B_48)=B_48 | ~v4_pre_topc(B_48, '#skF_2') | ~m1_subset_1(B_48, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_132])).
% 3.47/1.54  tff(c_173, plain, (![B_53]: (k2_pre_topc('#skF_2', B_53)=B_53 | ~v4_pre_topc(B_53, '#skF_2') | ~m1_subset_1(B_53, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_142])).
% 3.47/1.54  tff(c_182, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_98, c_173])).
% 3.47/1.54  tff(c_183, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_182])).
% 3.47/1.54  tff(c_147, plain, (![B_49, A_50]: (v3_pre_topc(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~v1_tdlat_3(A_50) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.47/1.54  tff(c_157, plain, (![B_49]: (v3_pre_topc(B_49, '#skF_2') | ~m1_subset_1(B_49, k1_zfmisc_1('#skF_3')) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_147])).
% 3.47/1.54  tff(c_162, plain, (![B_51]: (v3_pre_topc(B_51, '#skF_2') | ~m1_subset_1(B_51, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_157])).
% 3.47/1.54  tff(c_170, plain, (![B_3]: (v3_pre_topc(k3_subset_1('#skF_3', B_3), '#skF_2') | ~m1_subset_1(B_3, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_4, c_162])).
% 3.47/1.54  tff(c_255, plain, (![B_65, A_66]: (v4_pre_topc(B_65, A_66) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_66), B_65), A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.47/1.54  tff(c_261, plain, (![B_65]: (v4_pre_topc(B_65, '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', B_65), '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_255])).
% 3.47/1.54  tff(c_265, plain, (![B_67]: (v4_pre_topc(B_67, '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', B_67), '#skF_2') | ~m1_subset_1(B_67, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_99, c_261])).
% 3.47/1.54  tff(c_296, plain, (![B_71]: (v4_pre_topc(B_71, '#skF_2') | ~m1_subset_1(B_71, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_170, c_265])).
% 3.47/1.54  tff(c_303, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_98, c_296])).
% 3.47/1.54  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_303])).
% 3.47/1.54  tff(c_309, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_182])).
% 3.47/1.54  tff(c_315, plain, (![B_72, A_73]: (v1_tops_1(B_72, A_73) | k2_pre_topc(A_73, B_72)!=k2_struct_0(A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.54  tff(c_325, plain, (![B_72]: (v1_tops_1(B_72, '#skF_2') | k2_pre_topc('#skF_2', B_72)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_315])).
% 3.47/1.54  tff(c_330, plain, (![B_74]: (v1_tops_1(B_74, '#skF_2') | k2_pre_topc('#skF_2', B_74)!='#skF_3' | ~m1_subset_1(B_74, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_96, c_325])).
% 3.47/1.54  tff(c_337, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_98, c_330])).
% 3.47/1.54  tff(c_341, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_337])).
% 3.47/1.54  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.47/1.54  tff(c_419, plain, (![B_88, A_89]: (v2_tex_2(B_88, A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v1_tdlat_3(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.47/1.54  tff(c_429, plain, (![B_88]: (v2_tex_2(B_88, '#skF_2') | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_419])).
% 3.47/1.54  tff(c_433, plain, (![B_88]: (v2_tex_2(B_88, '#skF_2') | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_429])).
% 3.47/1.54  tff(c_445, plain, (![B_92]: (v2_tex_2(B_92, '#skF_2') | ~m1_subset_1(B_92, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_433])).
% 3.47/1.54  tff(c_454, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_98, c_445])).
% 3.47/1.54  tff(c_563, plain, (![B_113, A_114]: (v3_tex_2(B_113, A_114) | ~v2_tex_2(B_113, A_114) | ~v1_tops_1(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.54  tff(c_573, plain, (![B_113]: (v3_tex_2(B_113, '#skF_2') | ~v2_tex_2(B_113, '#skF_2') | ~v1_tops_1(B_113, '#skF_2') | ~m1_subset_1(B_113, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_563])).
% 3.47/1.54  tff(c_577, plain, (![B_113]: (v3_tex_2(B_113, '#skF_2') | ~v2_tex_2(B_113, '#skF_2') | ~v1_tops_1(B_113, '#skF_2') | ~m1_subset_1(B_113, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_573])).
% 3.47/1.54  tff(c_580, plain, (![B_116]: (v3_tex_2(B_116, '#skF_2') | ~v2_tex_2(B_116, '#skF_2') | ~v1_tops_1(B_116, '#skF_2') | ~m1_subset_1(B_116, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_577])).
% 3.47/1.54  tff(c_587, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_98, c_580])).
% 3.47/1.54  tff(c_591, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_454, c_587])).
% 3.47/1.54  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_591])).
% 3.47/1.54  tff(c_595, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.47/1.54  tff(c_1003, plain, (![B_183, A_184]: (v1_tops_1(B_183, A_184) | ~v3_tex_2(B_183, A_184) | ~v3_pre_topc(B_183, A_184) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.47/1.54  tff(c_1013, plain, (![B_183]: (v1_tops_1(B_183, '#skF_2') | ~v3_tex_2(B_183, '#skF_2') | ~v3_pre_topc(B_183, '#skF_2') | ~m1_subset_1(B_183, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_1003])).
% 3.47/1.54  tff(c_1017, plain, (![B_183]: (v1_tops_1(B_183, '#skF_2') | ~v3_tex_2(B_183, '#skF_2') | ~v3_pre_topc(B_183, '#skF_2') | ~m1_subset_1(B_183, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1013])).
% 3.47/1.54  tff(c_1019, plain, (![B_185]: (v1_tops_1(B_185, '#skF_2') | ~v3_tex_2(B_185, '#skF_2') | ~v3_pre_topc(B_185, '#skF_2') | ~m1_subset_1(B_185, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1017])).
% 3.47/1.54  tff(c_1026, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_609, c_1019])).
% 3.47/1.54  tff(c_1030, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_840, c_595, c_1026])).
% 3.47/1.54  tff(c_1032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_896, c_1030])).
% 3.47/1.54  tff(c_1034, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_868])).
% 3.47/1.54  tff(c_594, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 3.47/1.54  tff(c_608, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_594])).
% 3.47/1.54  tff(c_1040, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_608])).
% 3.47/1.54  tff(c_1043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_1040])).
% 3.47/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.54  
% 3.47/1.54  Inference rules
% 3.47/1.54  ----------------------
% 3.47/1.54  #Ref     : 0
% 3.47/1.54  #Sup     : 183
% 3.47/1.54  #Fact    : 0
% 3.47/1.54  #Define  : 0
% 3.47/1.54  #Split   : 6
% 3.47/1.54  #Chain   : 0
% 3.47/1.54  #Close   : 0
% 3.47/1.54  
% 3.47/1.54  Ordering : KBO
% 3.47/1.54  
% 3.47/1.54  Simplification rules
% 3.47/1.54  ----------------------
% 3.47/1.54  #Subsume      : 21
% 3.47/1.54  #Demod        : 132
% 3.47/1.54  #Tautology    : 50
% 3.47/1.54  #SimpNegUnit  : 19
% 3.47/1.54  #BackRed      : 13
% 3.47/1.54  
% 3.47/1.54  #Partial instantiations: 0
% 3.47/1.54  #Strategies tried      : 1
% 3.47/1.54  
% 3.47/1.54  Timing (in seconds)
% 3.47/1.54  ----------------------
% 3.47/1.54  Preprocessing        : 0.33
% 3.47/1.54  Parsing              : 0.17
% 3.47/1.54  CNF conversion       : 0.02
% 3.47/1.54  Main loop            : 0.41
% 3.47/1.54  Inferencing          : 0.16
% 3.47/1.54  Reduction            : 0.12
% 3.47/1.54  Demodulation         : 0.08
% 3.47/1.54  BG Simplification    : 0.02
% 3.47/1.54  Subsumption          : 0.07
% 3.47/1.54  Abstraction          : 0.02
% 3.47/1.54  MUC search           : 0.00
% 3.47/1.54  Cooper               : 0.00
% 3.47/1.54  Total                : 0.79
% 3.47/1.54  Index Insertion      : 0.00
% 3.47/1.54  Index Deletion       : 0.00
% 3.47/1.54  Index Matching       : 0.00
% 3.47/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
