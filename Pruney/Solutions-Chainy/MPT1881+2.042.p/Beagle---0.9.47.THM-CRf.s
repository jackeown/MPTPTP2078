%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:12 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 378 expanded)
%              Number of leaves         :   34 ( 140 expanded)
%              Depth                    :   10
%              Number of atoms          :  268 (1183 expanded)
%              Number of equality atoms :   30 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_34,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_49,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_tops_1(B,A)
              & v2_tex_2(B,A) )
           => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : ~ v1_subset_1(k2_subset_1(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_518,plain,(
    ! [A_101,B_102] :
      ( k2_pre_topc(A_101,B_102) = B_102
      | ~ v4_pre_topc(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_528,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_518])).

tff(c_533,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_528])).

tff(c_534,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k3_subset_1(A_2,B_3),k1_zfmisc_1(A_2))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_536,plain,(
    ! [B_105,A_106] :
      ( v3_pre_topc(B_105,A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v1_tdlat_3(A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_760,plain,(
    ! [A_143,B_144] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_143),B_144),A_143)
      | ~ v1_tdlat_3(A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143))) ) ),
    inference(resolution,[status(thm)],[c_4,c_536])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( v4_pre_topc(B_10,A_8)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_8),B_10),A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_765,plain,(
    ! [B_145,A_146] :
      ( v4_pre_topc(B_145,A_146)
      | ~ v1_tdlat_3(A_146)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146))) ) ),
    inference(resolution,[status(thm)],[c_760,c_12])).

tff(c_775,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_765])).

tff(c_780,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_40,c_775])).

tff(c_782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_780])).

tff(c_783,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_806,plain,(
    ! [B_151,A_152] :
      ( v1_tops_1(B_151,A_152)
      | k2_pre_topc(A_152,B_151) != u1_struct_0(A_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_816,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_806])).

tff(c_821,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | u1_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_783,c_816])).

tff(c_822,plain,(
    u1_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_821])).

tff(c_823,plain,(
    ! [A_153,B_154] :
      ( k2_pre_topc(A_153,B_154) = u1_struct_0(A_153)
      | ~ v1_tops_1(B_154,A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_833,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_823])).

tff(c_838,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_783,c_833])).

tff(c_839,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_822,c_838])).

tff(c_785,plain,(
    ! [B_147,A_148] :
      ( v3_pre_topc(B_147,A_148)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ v1_tdlat_3(A_148)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_795,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_785])).

tff(c_800,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_40,c_795])).

tff(c_52,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_64,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_65,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46])).

tff(c_66,plain,(
    ! [B_32,A_33] :
      ( v1_subset_1(B_32,A_33)
      | B_32 = A_33
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_69,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_72,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_69])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36])).

tff(c_129,plain,(
    ! [A_44,B_45] :
      ( k2_pre_topc(A_44,B_45) = B_45
      | ~ v4_pre_topc(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,(
    ! [B_45] :
      ( k2_pre_topc('#skF_2',B_45) = B_45
      | ~ v4_pre_topc(B_45,'#skF_2')
      | ~ m1_subset_1(B_45,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_129])).

tff(c_144,plain,(
    ! [B_46] :
      ( k2_pre_topc('#skF_2',B_46) = B_46
      | ~ v4_pre_topc(B_46,'#skF_2')
      | ~ m1_subset_1(B_46,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_139])).

tff(c_153,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_144])).

tff(c_154,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_103,plain,(
    ! [B_40,A_41] :
      ( v3_pre_topc(B_40,A_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ v1_tdlat_3(A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_113,plain,(
    ! [B_40] :
      ( v3_pre_topc(B_40,'#skF_2')
      | ~ m1_subset_1(B_40,k1_zfmisc_1('#skF_3'))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_103])).

tff(c_118,plain,(
    ! [B_42] :
      ( v3_pre_topc(B_42,'#skF_2')
      | ~ m1_subset_1(B_42,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_40,c_113])).

tff(c_126,plain,(
    ! [B_3] :
      ( v3_pre_topc(k3_subset_1('#skF_3',B_3),'#skF_2')
      | ~ m1_subset_1(B_3,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_118])).

tff(c_279,plain,(
    ! [B_65,A_66] :
      ( v4_pre_topc(B_65,A_66)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_66),B_65),A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_285,plain,(
    ! [B_65] :
      ( v4_pre_topc(B_65,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1('#skF_3',B_65),'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_279])).

tff(c_289,plain,(
    ! [B_67] :
      ( v4_pre_topc(B_67,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1('#skF_3',B_67),'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_72,c_285])).

tff(c_294,plain,(
    ! [B_68] :
      ( v4_pre_topc(B_68,'#skF_2')
      | ~ m1_subset_1(B_68,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_126,c_289])).

tff(c_301,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_294])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_301])).

tff(c_307,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_309,plain,(
    ! [B_69,A_70] :
      ( v1_tops_1(B_69,A_70)
      | k2_pre_topc(A_70,B_69) != u1_struct_0(A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_319,plain,(
    ! [B_69] :
      ( v1_tops_1(B_69,'#skF_2')
      | k2_pre_topc('#skF_2',B_69) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_69,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_309])).

tff(c_328,plain,(
    ! [B_71] :
      ( v1_tops_1(B_71,'#skF_2')
      | k2_pre_topc('#skF_2',B_71) != '#skF_3'
      | ~ m1_subset_1(B_71,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_72,c_319])).

tff(c_335,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_74,c_328])).

tff(c_339,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_335])).

tff(c_412,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v1_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_422,plain,(
    ! [B_83] :
      ( v2_tex_2(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_412])).

tff(c_426,plain,(
    ! [B_83] :
      ( v2_tex_2(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_422])).

tff(c_428,plain,(
    ! [B_85] :
      ( v2_tex_2(B_85,'#skF_2')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_426])).

tff(c_437,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_428])).

tff(c_465,plain,(
    ! [B_91,A_92] :
      ( v3_tex_2(B_91,A_92)
      | ~ v2_tex_2(B_91,A_92)
      | ~ v1_tops_1(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_475,plain,(
    ! [B_91] :
      ( v3_tex_2(B_91,'#skF_2')
      | ~ v2_tex_2(B_91,'#skF_2')
      | ~ v1_tops_1(B_91,'#skF_2')
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_465])).

tff(c_479,plain,(
    ! [B_91] :
      ( v3_tex_2(B_91,'#skF_2')
      | ~ v2_tex_2(B_91,'#skF_2')
      | ~ v1_tops_1(B_91,'#skF_2')
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_475])).

tff(c_482,plain,(
    ! [B_94] :
      ( v3_tex_2(B_94,'#skF_2')
      | ~ v2_tex_2(B_94,'#skF_2')
      | ~ v1_tops_1(B_94,'#skF_2')
      | ~ m1_subset_1(B_94,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_479])).

tff(c_489,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_482])).

tff(c_493,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_437,c_489])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_493])).

tff(c_496,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_932,plain,(
    ! [B_178,A_179] :
      ( v1_tops_1(B_178,A_179)
      | ~ v3_tex_2(B_178,A_179)
      | ~ v3_pre_topc(B_178,A_179)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_942,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_932])).

tff(c_947,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_800,c_496,c_942])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_839,c_947])).

tff(c_951,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_821])).

tff(c_499,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_46])).

tff(c_952,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_499])).

tff(c_955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_952])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.58  
% 3.51/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.58  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.51/1.58  
% 3.51/1.58  %Foreground sorts:
% 3.51/1.58  
% 3.51/1.58  
% 3.51/1.58  %Background operators:
% 3.51/1.58  
% 3.51/1.58  
% 3.51/1.58  %Foreground operators:
% 3.51/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.51/1.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.51/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.58  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.51/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.51/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.51/1.58  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.51/1.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.51/1.58  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.51/1.58  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.51/1.58  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.51/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.58  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.51/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.51/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.51/1.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.51/1.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.51/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.58  
% 3.51/1.60  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.51/1.60  tff(f_34, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.51/1.60  tff(f_149, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 3.51/1.60  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.51/1.60  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.51/1.60  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 3.51/1.60  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 3.51/1.60  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 3.51/1.60  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.51/1.60  tff(f_99, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 3.51/1.60  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 3.51/1.60  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 3.51/1.60  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.51/1.60  tff(c_6, plain, (![A_4]: (~v1_subset_1(k2_subset_1(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.51/1.60  tff(c_53, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 3.51/1.60  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.51/1.60  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.51/1.60  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.51/1.60  tff(c_518, plain, (![A_101, B_102]: (k2_pre_topc(A_101, B_102)=B_102 | ~v4_pre_topc(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.51/1.60  tff(c_528, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_518])).
% 3.51/1.60  tff(c_533, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_528])).
% 3.51/1.60  tff(c_534, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_533])).
% 3.51/1.60  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.51/1.60  tff(c_40, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.51/1.60  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k3_subset_1(A_2, B_3), k1_zfmisc_1(A_2)) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.51/1.60  tff(c_536, plain, (![B_105, A_106]: (v3_pre_topc(B_105, A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~v1_tdlat_3(A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.51/1.60  tff(c_760, plain, (![A_143, B_144]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_143), B_144), A_143) | ~v1_tdlat_3(A_143) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))))), inference(resolution, [status(thm)], [c_4, c_536])).
% 3.51/1.60  tff(c_12, plain, (![B_10, A_8]: (v4_pre_topc(B_10, A_8) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_8), B_10), A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.51/1.60  tff(c_765, plain, (![B_145, A_146]: (v4_pre_topc(B_145, A_146) | ~v1_tdlat_3(A_146) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))))), inference(resolution, [status(thm)], [c_760, c_12])).
% 3.51/1.60  tff(c_775, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_765])).
% 3.51/1.60  tff(c_780, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_40, c_775])).
% 3.51/1.60  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_534, c_780])).
% 3.51/1.60  tff(c_783, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_533])).
% 3.51/1.60  tff(c_806, plain, (![B_151, A_152]: (v1_tops_1(B_151, A_152) | k2_pre_topc(A_152, B_151)!=u1_struct_0(A_152) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.51/1.60  tff(c_816, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_806])).
% 3.51/1.60  tff(c_821, plain, (v1_tops_1('#skF_3', '#skF_2') | u1_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_783, c_816])).
% 3.51/1.60  tff(c_822, plain, (u1_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_821])).
% 3.51/1.60  tff(c_823, plain, (![A_153, B_154]: (k2_pre_topc(A_153, B_154)=u1_struct_0(A_153) | ~v1_tops_1(B_154, A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.51/1.60  tff(c_833, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_823])).
% 3.51/1.60  tff(c_838, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_783, c_833])).
% 3.51/1.60  tff(c_839, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_822, c_838])).
% 3.51/1.60  tff(c_785, plain, (![B_147, A_148]: (v3_pre_topc(B_147, A_148) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_148))) | ~v1_tdlat_3(A_148) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.51/1.60  tff(c_795, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_785])).
% 3.51/1.60  tff(c_800, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_40, c_795])).
% 3.51/1.60  tff(c_52, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.51/1.60  tff(c_64, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.51/1.60  tff(c_46, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.51/1.60  tff(c_65, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_46])).
% 3.51/1.60  tff(c_66, plain, (![B_32, A_33]: (v1_subset_1(B_32, A_33) | B_32=A_33 | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.51/1.60  tff(c_69, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_36, c_66])).
% 3.51/1.60  tff(c_72, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_64, c_69])).
% 3.51/1.60  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_36])).
% 3.51/1.60  tff(c_129, plain, (![A_44, B_45]: (k2_pre_topc(A_44, B_45)=B_45 | ~v4_pre_topc(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.51/1.60  tff(c_139, plain, (![B_45]: (k2_pre_topc('#skF_2', B_45)=B_45 | ~v4_pre_topc(B_45, '#skF_2') | ~m1_subset_1(B_45, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_129])).
% 3.51/1.60  tff(c_144, plain, (![B_46]: (k2_pre_topc('#skF_2', B_46)=B_46 | ~v4_pre_topc(B_46, '#skF_2') | ~m1_subset_1(B_46, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_139])).
% 3.51/1.60  tff(c_153, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_144])).
% 3.51/1.60  tff(c_154, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_153])).
% 3.51/1.60  tff(c_103, plain, (![B_40, A_41]: (v3_pre_topc(B_40, A_41) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_41))) | ~v1_tdlat_3(A_41) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.51/1.60  tff(c_113, plain, (![B_40]: (v3_pre_topc(B_40, '#skF_2') | ~m1_subset_1(B_40, k1_zfmisc_1('#skF_3')) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_103])).
% 3.51/1.60  tff(c_118, plain, (![B_42]: (v3_pre_topc(B_42, '#skF_2') | ~m1_subset_1(B_42, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_40, c_113])).
% 3.51/1.60  tff(c_126, plain, (![B_3]: (v3_pre_topc(k3_subset_1('#skF_3', B_3), '#skF_2') | ~m1_subset_1(B_3, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_4, c_118])).
% 3.51/1.60  tff(c_279, plain, (![B_65, A_66]: (v4_pre_topc(B_65, A_66) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_66), B_65), A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.51/1.60  tff(c_285, plain, (![B_65]: (v4_pre_topc(B_65, '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', B_65), '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_279])).
% 3.51/1.60  tff(c_289, plain, (![B_67]: (v4_pre_topc(B_67, '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', B_67), '#skF_2') | ~m1_subset_1(B_67, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_72, c_285])).
% 3.51/1.60  tff(c_294, plain, (![B_68]: (v4_pre_topc(B_68, '#skF_2') | ~m1_subset_1(B_68, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_126, c_289])).
% 3.51/1.60  tff(c_301, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_294])).
% 3.51/1.60  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_301])).
% 3.51/1.60  tff(c_307, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_153])).
% 3.51/1.60  tff(c_309, plain, (![B_69, A_70]: (v1_tops_1(B_69, A_70) | k2_pre_topc(A_70, B_69)!=u1_struct_0(A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.51/1.60  tff(c_319, plain, (![B_69]: (v1_tops_1(B_69, '#skF_2') | k2_pre_topc('#skF_2', B_69)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_69, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_309])).
% 3.51/1.60  tff(c_328, plain, (![B_71]: (v1_tops_1(B_71, '#skF_2') | k2_pre_topc('#skF_2', B_71)!='#skF_3' | ~m1_subset_1(B_71, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_72, c_319])).
% 3.51/1.60  tff(c_335, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_74, c_328])).
% 3.51/1.60  tff(c_339, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_335])).
% 3.51/1.60  tff(c_412, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v1_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.51/1.60  tff(c_422, plain, (![B_83]: (v2_tex_2(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_412])).
% 3.51/1.60  tff(c_426, plain, (![B_83]: (v2_tex_2(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_422])).
% 3.51/1.60  tff(c_428, plain, (![B_85]: (v2_tex_2(B_85, '#skF_2') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_426])).
% 3.51/1.60  tff(c_437, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_428])).
% 3.51/1.60  tff(c_465, plain, (![B_91, A_92]: (v3_tex_2(B_91, A_92) | ~v2_tex_2(B_91, A_92) | ~v1_tops_1(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.51/1.60  tff(c_475, plain, (![B_91]: (v3_tex_2(B_91, '#skF_2') | ~v2_tex_2(B_91, '#skF_2') | ~v1_tops_1(B_91, '#skF_2') | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_465])).
% 3.51/1.60  tff(c_479, plain, (![B_91]: (v3_tex_2(B_91, '#skF_2') | ~v2_tex_2(B_91, '#skF_2') | ~v1_tops_1(B_91, '#skF_2') | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_475])).
% 3.51/1.60  tff(c_482, plain, (![B_94]: (v3_tex_2(B_94, '#skF_2') | ~v2_tex_2(B_94, '#skF_2') | ~v1_tops_1(B_94, '#skF_2') | ~m1_subset_1(B_94, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_479])).
% 3.51/1.60  tff(c_489, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_482])).
% 3.51/1.60  tff(c_493, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_437, c_489])).
% 3.51/1.60  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_493])).
% 3.51/1.60  tff(c_496, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.51/1.60  tff(c_932, plain, (![B_178, A_179]: (v1_tops_1(B_178, A_179) | ~v3_tex_2(B_178, A_179) | ~v3_pre_topc(B_178, A_179) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.51/1.60  tff(c_942, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_932])).
% 3.51/1.60  tff(c_947, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_800, c_496, c_942])).
% 3.51/1.60  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_839, c_947])).
% 3.51/1.60  tff(c_951, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_821])).
% 3.51/1.60  tff(c_499, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_46])).
% 3.51/1.60  tff(c_952, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_951, c_499])).
% 3.51/1.60  tff(c_955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_952])).
% 3.51/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.60  
% 3.51/1.60  Inference rules
% 3.51/1.60  ----------------------
% 3.51/1.60  #Ref     : 0
% 3.51/1.60  #Sup     : 162
% 3.51/1.60  #Fact    : 0
% 3.51/1.60  #Define  : 0
% 3.51/1.60  #Split   : 6
% 3.51/1.60  #Chain   : 0
% 3.51/1.60  #Close   : 0
% 3.51/1.60  
% 3.51/1.60  Ordering : KBO
% 3.51/1.60  
% 3.51/1.60  Simplification rules
% 3.51/1.61  ----------------------
% 3.51/1.61  #Subsume      : 13
% 3.51/1.61  #Demod        : 122
% 3.51/1.61  #Tautology    : 48
% 3.51/1.61  #SimpNegUnit  : 24
% 3.51/1.61  #BackRed      : 4
% 3.51/1.61  
% 3.51/1.61  #Partial instantiations: 0
% 3.51/1.61  #Strategies tried      : 1
% 3.51/1.61  
% 3.51/1.61  Timing (in seconds)
% 3.51/1.61  ----------------------
% 3.51/1.61  Preprocessing        : 0.35
% 3.51/1.61  Parsing              : 0.19
% 3.51/1.61  CNF conversion       : 0.02
% 3.51/1.61  Main loop            : 0.46
% 3.51/1.61  Inferencing          : 0.19
% 3.51/1.61  Reduction            : 0.13
% 3.51/1.61  Demodulation         : 0.08
% 3.51/1.61  BG Simplification    : 0.03
% 3.51/1.61  Subsumption          : 0.08
% 3.51/1.61  Abstraction          : 0.03
% 3.51/1.61  MUC search           : 0.00
% 3.51/1.61  Cooper               : 0.00
% 3.51/1.61  Total                : 0.86
% 3.51/1.61  Index Insertion      : 0.00
% 3.51/1.61  Index Deletion       : 0.00
% 3.51/1.61  Index Matching       : 0.00
% 3.51/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
