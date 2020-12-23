%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:10 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 393 expanded)
%              Number of leaves         :   31 ( 144 expanded)
%              Depth                    :   10
%              Number of atoms          :  267 (1246 expanded)
%              Number of equality atoms :   28 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
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

tff(f_44,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_132,axiom,(
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

tff(f_116,axiom,(
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

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_532,plain,(
    ! [A_107,B_108] :
      ( k2_pre_topc(A_107,B_108) = B_108
      | ~ v4_pre_topc(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_542,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_532])).

tff(c_547,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_542])).

tff(c_548,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_38,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_549,plain,(
    ! [B_109,A_110] :
      ( v3_pre_topc(B_109,A_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ v1_tdlat_3(A_110)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_774,plain,(
    ! [A_148,B_149] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_148),B_149),A_148)
      | ~ v1_tdlat_3(A_148)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148))) ) ),
    inference(resolution,[status(thm)],[c_2,c_549])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( v4_pre_topc(B_8,A_6)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_6),B_8),A_6)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_779,plain,(
    ! [B_150,A_151] :
      ( v4_pre_topc(B_150,A_151)
      | ~ v1_tdlat_3(A_151)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151))) ) ),
    inference(resolution,[status(thm)],[c_774,c_8])).

tff(c_789,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_779])).

tff(c_794,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_38,c_789])).

tff(c_796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_794])).

tff(c_797,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_819,plain,(
    ! [B_154,A_155] :
      ( v1_tops_1(B_154,A_155)
      | k2_pre_topc(A_155,B_154) != u1_struct_0(A_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_829,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_819])).

tff(c_834,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | u1_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_797,c_829])).

tff(c_835,plain,(
    u1_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_834])).

tff(c_836,plain,(
    ! [A_156,B_157] :
      ( k2_pre_topc(A_156,B_157) = u1_struct_0(A_156)
      | ~ v1_tops_1(B_157,A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_846,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_836])).

tff(c_851,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_797,c_846])).

tff(c_852,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_835,c_851])).

tff(c_799,plain,(
    ! [B_152,A_153] :
      ( v3_pre_topc(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ v1_tdlat_3(A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_809,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_799])).

tff(c_814,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_38,c_809])).

tff(c_50,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_53,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_44])).

tff(c_55,plain,(
    ! [B_31,A_32] :
      ( v1_subset_1(B_31,A_32)
      | B_31 = A_32
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_55])).

tff(c_61,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_58])).

tff(c_63,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34])).

tff(c_122,plain,(
    ! [A_43,B_44] :
      ( k2_pre_topc(A_43,B_44) = B_44
      | ~ v4_pre_topc(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_132,plain,(
    ! [B_44] :
      ( k2_pre_topc('#skF_2',B_44) = B_44
      | ~ v4_pre_topc(B_44,'#skF_2')
      | ~ m1_subset_1(B_44,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_122])).

tff(c_137,plain,(
    ! [B_45] :
      ( k2_pre_topc('#skF_2',B_45) = B_45
      | ~ v4_pre_topc(B_45,'#skF_2')
      | ~ m1_subset_1(B_45,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_132])).

tff(c_146,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_137])).

tff(c_147,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_96,plain,(
    ! [B_39,A_40] :
      ( v3_pre_topc(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ v1_tdlat_3(A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_106,plain,(
    ! [B_39] :
      ( v3_pre_topc(B_39,'#skF_2')
      | ~ m1_subset_1(B_39,k1_zfmisc_1('#skF_3'))
      | ~ v1_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_96])).

tff(c_111,plain,(
    ! [B_41] :
      ( v3_pre_topc(B_41,'#skF_2')
      | ~ m1_subset_1(B_41,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_38,c_106])).

tff(c_119,plain,(
    ! [B_2] :
      ( v3_pre_topc(k3_subset_1('#skF_3',B_2),'#skF_2')
      | ~ m1_subset_1(B_2,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2,c_111])).

tff(c_240,plain,(
    ! [B_59,A_60] :
      ( v4_pre_topc(B_59,A_60)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_60),B_59),A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_243,plain,(
    ! [B_59] :
      ( v4_pre_topc(B_59,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1('#skF_3',B_59),'#skF_2')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_240])).

tff(c_246,plain,(
    ! [B_61] :
      ( v4_pre_topc(B_61,'#skF_2')
      | ~ v3_pre_topc(k3_subset_1('#skF_3',B_61),'#skF_2')
      | ~ m1_subset_1(B_61,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_61,c_243])).

tff(c_251,plain,(
    ! [B_62] :
      ( v4_pre_topc(B_62,'#skF_2')
      | ~ m1_subset_1(B_62,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_119,c_246])).

tff(c_258,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_251])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_258])).

tff(c_264,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_270,plain,(
    ! [B_63,A_64] :
      ( v1_tops_1(B_63,A_64)
      | k2_pre_topc(A_64,B_63) != u1_struct_0(A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_280,plain,(
    ! [B_63] :
      ( v1_tops_1(B_63,'#skF_2')
      | k2_pre_topc('#skF_2',B_63) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_270])).

tff(c_285,plain,(
    ! [B_65] :
      ( v1_tops_1(B_65,'#skF_2')
      | k2_pre_topc('#skF_2',B_65) != '#skF_3'
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_61,c_280])).

tff(c_292,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_63,c_285])).

tff(c_296,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_292])).

tff(c_403,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v1_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_413,plain,(
    ! [B_83] :
      ( v2_tex_2(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_403])).

tff(c_417,plain,(
    ! [B_83] :
      ( v2_tex_2(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_413])).

tff(c_419,plain,(
    ! [B_85] :
      ( v2_tex_2(B_85,'#skF_2')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_417])).

tff(c_428,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_419])).

tff(c_480,plain,(
    ! [B_96,A_97] :
      ( v3_tex_2(B_96,A_97)
      | ~ v2_tex_2(B_96,A_97)
      | ~ v1_tops_1(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_490,plain,(
    ! [B_96] :
      ( v3_tex_2(B_96,'#skF_2')
      | ~ v2_tex_2(B_96,'#skF_2')
      | ~ v1_tops_1(B_96,'#skF_2')
      | ~ m1_subset_1(B_96,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_480])).

tff(c_494,plain,(
    ! [B_96] :
      ( v3_tex_2(B_96,'#skF_2')
      | ~ v2_tex_2(B_96,'#skF_2')
      | ~ v1_tops_1(B_96,'#skF_2')
      | ~ m1_subset_1(B_96,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_490])).

tff(c_496,plain,(
    ! [B_98] :
      ( v3_tex_2(B_98,'#skF_2')
      | ~ v2_tex_2(B_98,'#skF_2')
      | ~ v1_tops_1(B_98,'#skF_2')
      | ~ m1_subset_1(B_98,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_494])).

tff(c_503,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_496])).

tff(c_507,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_428,c_503])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_507])).

tff(c_510,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_893,plain,(
    ! [B_167,A_168] :
      ( v1_tops_1(B_167,A_168)
      | ~ v3_tex_2(B_167,A_168)
      | ~ v3_pre_topc(B_167,A_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_903,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_893])).

tff(c_908,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_814,c_510,c_903])).

tff(c_910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_852,c_908])).

tff(c_912,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_511,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_913,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_511])).

tff(c_914,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_34])).

tff(c_20,plain,(
    ! [B_14] :
      ( ~ v1_subset_1(B_14,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_944,plain,(
    ~ v1_subset_1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_914,c_20])).

tff(c_951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n023.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 09:36:51 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.47  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 3.22/1.47  
% 3.22/1.47  %Foreground sorts:
% 3.22/1.47  
% 3.22/1.47  
% 3.22/1.47  %Background operators:
% 3.22/1.47  
% 3.22/1.47  
% 3.22/1.47  %Foreground operators:
% 3.22/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.22/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.22/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.22/1.47  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.22/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.22/1.47  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.22/1.47  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.22/1.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.22/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.22/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.22/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.47  
% 3.32/1.49  tff(f_150, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 3.32/1.49  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.32/1.49  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.32/1.49  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 3.32/1.49  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 3.32/1.49  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 3.32/1.49  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.32/1.49  tff(f_100, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 3.32/1.49  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 3.32/1.49  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 3.32/1.49  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.32/1.49  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.32/1.49  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.32/1.49  tff(c_532, plain, (![A_107, B_108]: (k2_pre_topc(A_107, B_108)=B_108 | ~v4_pre_topc(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.32/1.49  tff(c_542, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_532])).
% 3.32/1.49  tff(c_547, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_542])).
% 3.32/1.49  tff(c_548, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_547])).
% 3.32/1.49  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.32/1.49  tff(c_38, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.32/1.49  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.49  tff(c_549, plain, (![B_109, A_110]: (v3_pre_topc(B_109, A_110) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~v1_tdlat_3(A_110) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.32/1.49  tff(c_774, plain, (![A_148, B_149]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_148), B_149), A_148) | ~v1_tdlat_3(A_148) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))))), inference(resolution, [status(thm)], [c_2, c_549])).
% 3.32/1.49  tff(c_8, plain, (![B_8, A_6]: (v4_pre_topc(B_8, A_6) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_6), B_8), A_6) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.49  tff(c_779, plain, (![B_150, A_151]: (v4_pre_topc(B_150, A_151) | ~v1_tdlat_3(A_151) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))))), inference(resolution, [status(thm)], [c_774, c_8])).
% 3.32/1.49  tff(c_789, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_779])).
% 3.32/1.49  tff(c_794, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_38, c_789])).
% 3.32/1.49  tff(c_796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_548, c_794])).
% 3.32/1.49  tff(c_797, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_547])).
% 3.32/1.49  tff(c_819, plain, (![B_154, A_155]: (v1_tops_1(B_154, A_155) | k2_pre_topc(A_155, B_154)!=u1_struct_0(A_155) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.49  tff(c_829, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_819])).
% 3.32/1.49  tff(c_834, plain, (v1_tops_1('#skF_3', '#skF_2') | u1_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_797, c_829])).
% 3.32/1.49  tff(c_835, plain, (u1_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_834])).
% 3.32/1.49  tff(c_836, plain, (![A_156, B_157]: (k2_pre_topc(A_156, B_157)=u1_struct_0(A_156) | ~v1_tops_1(B_157, A_156) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.49  tff(c_846, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_836])).
% 3.32/1.49  tff(c_851, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_797, c_846])).
% 3.32/1.49  tff(c_852, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_835, c_851])).
% 3.32/1.49  tff(c_799, plain, (![B_152, A_153]: (v3_pre_topc(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_153))) | ~v1_tdlat_3(A_153) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.32/1.49  tff(c_809, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_799])).
% 3.32/1.49  tff(c_814, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_38, c_809])).
% 3.32/1.49  tff(c_50, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.32/1.49  tff(c_53, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.32/1.49  tff(c_44, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.32/1.49  tff(c_54, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_53, c_44])).
% 3.32/1.49  tff(c_55, plain, (![B_31, A_32]: (v1_subset_1(B_31, A_32) | B_31=A_32 | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.49  tff(c_58, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_34, c_55])).
% 3.32/1.49  tff(c_61, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_53, c_58])).
% 3.32/1.49  tff(c_63, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_34])).
% 3.32/1.49  tff(c_122, plain, (![A_43, B_44]: (k2_pre_topc(A_43, B_44)=B_44 | ~v4_pre_topc(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.32/1.49  tff(c_132, plain, (![B_44]: (k2_pre_topc('#skF_2', B_44)=B_44 | ~v4_pre_topc(B_44, '#skF_2') | ~m1_subset_1(B_44, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_122])).
% 3.32/1.49  tff(c_137, plain, (![B_45]: (k2_pre_topc('#skF_2', B_45)=B_45 | ~v4_pre_topc(B_45, '#skF_2') | ~m1_subset_1(B_45, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_132])).
% 3.32/1.49  tff(c_146, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_63, c_137])).
% 3.32/1.49  tff(c_147, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_146])).
% 3.32/1.49  tff(c_96, plain, (![B_39, A_40]: (v3_pre_topc(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~v1_tdlat_3(A_40) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.32/1.49  tff(c_106, plain, (![B_39]: (v3_pre_topc(B_39, '#skF_2') | ~m1_subset_1(B_39, k1_zfmisc_1('#skF_3')) | ~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_96])).
% 3.32/1.49  tff(c_111, plain, (![B_41]: (v3_pre_topc(B_41, '#skF_2') | ~m1_subset_1(B_41, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_38, c_106])).
% 3.32/1.49  tff(c_119, plain, (![B_2]: (v3_pre_topc(k3_subset_1('#skF_3', B_2), '#skF_2') | ~m1_subset_1(B_2, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_2, c_111])).
% 3.32/1.49  tff(c_240, plain, (![B_59, A_60]: (v4_pre_topc(B_59, A_60) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_60), B_59), A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.49  tff(c_243, plain, (![B_59]: (v4_pre_topc(B_59, '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', B_59), '#skF_2') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_240])).
% 3.32/1.49  tff(c_246, plain, (![B_61]: (v4_pre_topc(B_61, '#skF_2') | ~v3_pre_topc(k3_subset_1('#skF_3', B_61), '#skF_2') | ~m1_subset_1(B_61, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_61, c_243])).
% 3.32/1.49  tff(c_251, plain, (![B_62]: (v4_pre_topc(B_62, '#skF_2') | ~m1_subset_1(B_62, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_119, c_246])).
% 3.32/1.49  tff(c_258, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_63, c_251])).
% 3.32/1.49  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_258])).
% 3.32/1.49  tff(c_264, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_146])).
% 3.32/1.49  tff(c_270, plain, (![B_63, A_64]: (v1_tops_1(B_63, A_64) | k2_pre_topc(A_64, B_63)!=u1_struct_0(A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.49  tff(c_280, plain, (![B_63]: (v1_tops_1(B_63, '#skF_2') | k2_pre_topc('#skF_2', B_63)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_270])).
% 3.32/1.49  tff(c_285, plain, (![B_65]: (v1_tops_1(B_65, '#skF_2') | k2_pre_topc('#skF_2', B_65)!='#skF_3' | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_61, c_280])).
% 3.32/1.49  tff(c_292, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_63, c_285])).
% 3.32/1.49  tff(c_296, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_292])).
% 3.32/1.49  tff(c_403, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v1_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.49  tff(c_413, plain, (![B_83]: (v2_tex_2(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_403])).
% 3.32/1.49  tff(c_417, plain, (![B_83]: (v2_tex_2(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_413])).
% 3.32/1.49  tff(c_419, plain, (![B_85]: (v2_tex_2(B_85, '#skF_2') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_417])).
% 3.32/1.49  tff(c_428, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_63, c_419])).
% 3.32/1.49  tff(c_480, plain, (![B_96, A_97]: (v3_tex_2(B_96, A_97) | ~v2_tex_2(B_96, A_97) | ~v1_tops_1(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.32/1.49  tff(c_490, plain, (![B_96]: (v3_tex_2(B_96, '#skF_2') | ~v2_tex_2(B_96, '#skF_2') | ~v1_tops_1(B_96, '#skF_2') | ~m1_subset_1(B_96, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_480])).
% 3.32/1.49  tff(c_494, plain, (![B_96]: (v3_tex_2(B_96, '#skF_2') | ~v2_tex_2(B_96, '#skF_2') | ~v1_tops_1(B_96, '#skF_2') | ~m1_subset_1(B_96, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_490])).
% 3.32/1.49  tff(c_496, plain, (![B_98]: (v3_tex_2(B_98, '#skF_2') | ~v2_tex_2(B_98, '#skF_2') | ~v1_tops_1(B_98, '#skF_2') | ~m1_subset_1(B_98, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_494])).
% 3.32/1.49  tff(c_503, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_63, c_496])).
% 3.32/1.49  tff(c_507, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_428, c_503])).
% 3.32/1.49  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_507])).
% 3.32/1.49  tff(c_510, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 3.32/1.49  tff(c_893, plain, (![B_167, A_168]: (v1_tops_1(B_167, A_168) | ~v3_tex_2(B_167, A_168) | ~v3_pre_topc(B_167, A_168) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.49  tff(c_903, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_893])).
% 3.32/1.49  tff(c_908, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_814, c_510, c_903])).
% 3.32/1.49  tff(c_910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_852, c_908])).
% 3.32/1.49  tff(c_912, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_834])).
% 3.32/1.49  tff(c_511, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 3.32/1.49  tff(c_913, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_912, c_511])).
% 3.32/1.49  tff(c_914, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_912, c_34])).
% 3.32/1.49  tff(c_20, plain, (![B_14]: (~v1_subset_1(B_14, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.49  tff(c_944, plain, (~v1_subset_1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_914, c_20])).
% 3.32/1.49  tff(c_951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_913, c_944])).
% 3.32/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.49  
% 3.32/1.49  Inference rules
% 3.32/1.49  ----------------------
% 3.32/1.49  #Ref     : 0
% 3.32/1.49  #Sup     : 165
% 3.32/1.49  #Fact    : 0
% 3.32/1.49  #Define  : 0
% 3.32/1.49  #Split   : 6
% 3.32/1.49  #Chain   : 0
% 3.32/1.49  #Close   : 0
% 3.32/1.49  
% 3.32/1.49  Ordering : KBO
% 3.32/1.49  
% 3.32/1.49  Simplification rules
% 3.32/1.49  ----------------------
% 3.32/1.49  #Subsume      : 11
% 3.32/1.49  #Demod        : 121
% 3.32/1.49  #Tautology    : 50
% 3.32/1.49  #SimpNegUnit  : 22
% 3.32/1.49  #BackRed      : 4
% 3.32/1.49  
% 3.32/1.49  #Partial instantiations: 0
% 3.32/1.49  #Strategies tried      : 1
% 3.32/1.49  
% 3.32/1.49  Timing (in seconds)
% 3.32/1.49  ----------------------
% 3.32/1.49  Preprocessing        : 0.32
% 3.32/1.49  Parsing              : 0.16
% 3.32/1.49  CNF conversion       : 0.02
% 3.32/1.49  Main loop            : 0.39
% 3.32/1.49  Inferencing          : 0.15
% 3.32/1.49  Reduction            : 0.11
% 3.32/1.49  Demodulation         : 0.07
% 3.32/1.49  BG Simplification    : 0.02
% 3.32/1.49  Subsumption          : 0.07
% 3.32/1.49  Abstraction          : 0.02
% 3.32/1.49  MUC search           : 0.00
% 3.32/1.49  Cooper               : 0.00
% 3.32/1.49  Total                : 0.75
% 3.32/1.49  Index Insertion      : 0.00
% 3.32/1.49  Index Deletion       : 0.00
% 3.32/1.49  Index Matching       : 0.00
% 3.32/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
