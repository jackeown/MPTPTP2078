%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:09 EST 2020

% Result     : Theorem 4.30s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 331 expanded)
%              Number of leaves         :   38 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  280 ( 947 expanded)
%              Number of equality atoms :   30 ( 102 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
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

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_55,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

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

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : ~ v1_subset_1(k2_subset_1(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [A_5] : ~ v1_subset_1(A_5,A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_2138,plain,(
    ! [B_283,A_284] :
      ( v2_tex_2(B_283,A_284)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284)
      | ~ v1_tdlat_3(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2164,plain,(
    ! [A_284] :
      ( v2_tex_2(u1_struct_0(A_284),A_284)
      | ~ l1_pre_topc(A_284)
      | ~ v1_tdlat_3(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(resolution,[status(thm)],[c_71,c_2138])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_70,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_87,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_88,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_64])).

tff(c_104,plain,(
    ! [B_50,A_51] :
      ( v1_subset_1(B_50,A_51)
      | B_50 = A_51
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_110,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_104])).

tff(c_117,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_110])).

tff(c_294,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,B_75) = B_75
      | ~ v4_pre_topc(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_304,plain,(
    ! [B_75] :
      ( k2_pre_topc('#skF_3',B_75) = B_75
      | ~ v4_pre_topc(B_75,'#skF_3')
      | ~ m1_subset_1(B_75,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_294])).

tff(c_319,plain,(
    ! [B_76] :
      ( k2_pre_topc('#skF_3',B_76) = B_76
      | ~ v4_pre_topc(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_304])).

tff(c_334,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_319])).

tff(c_335,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_195,plain,(
    ! [B_63,A_64] :
      ( v3_pre_topc(B_63,A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ v1_tdlat_3(A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_205,plain,(
    ! [B_63] :
      ( v3_pre_topc(B_63,'#skF_3')
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_4'))
      | ~ v1_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_195])).

tff(c_220,plain,(
    ! [B_65] :
      ( v3_pre_topc(B_65,'#skF_3')
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_205])).

tff(c_233,plain,(
    ! [B_4] :
      ( v3_pre_topc(k3_subset_1('#skF_4',B_4),'#skF_3')
      | ~ m1_subset_1(B_4,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_220])).

tff(c_480,plain,(
    ! [B_96,A_97] :
      ( v4_pre_topc(B_96,A_97)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_97),B_96),A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_487,plain,(
    ! [B_96] :
      ( v4_pre_topc(B_96,'#skF_3')
      | ~ v3_pre_topc(k3_subset_1('#skF_4',B_96),'#skF_3')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_480])).

tff(c_530,plain,(
    ! [B_100] :
      ( v4_pre_topc(B_100,'#skF_3')
      | ~ v3_pre_topc(k3_subset_1('#skF_4',B_100),'#skF_3')
      | ~ m1_subset_1(B_100,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117,c_487])).

tff(c_539,plain,(
    ! [B_101] :
      ( v4_pre_topc(B_101,'#skF_3')
      | ~ m1_subset_1(B_101,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_233,c_530])).

tff(c_551,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_539])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_335,c_551])).

tff(c_558,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_689,plain,(
    ! [B_119,A_120] :
      ( v1_tops_1(B_119,A_120)
      | k2_pre_topc(A_120,B_119) != u1_struct_0(A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_699,plain,(
    ! [B_119] :
      ( v1_tops_1(B_119,'#skF_3')
      | k2_pre_topc('#skF_3',B_119) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_119,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_689])).

tff(c_714,plain,(
    ! [B_121] :
      ( v1_tops_1(B_121,'#skF_3')
      | k2_pre_topc('#skF_3',B_121) != '#skF_4'
      | ~ m1_subset_1(B_121,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117,c_699])).

tff(c_726,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_71,c_714])).

tff(c_731,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_726])).

tff(c_977,plain,(
    ! [B_145,A_146] :
      ( v2_tex_2(B_145,A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v1_tdlat_3(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_987,plain,(
    ! [B_145] :
      ( v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_977])).

tff(c_999,plain,(
    ! [B_145] :
      ( v2_tex_2(B_145,'#skF_3')
      | ~ m1_subset_1(B_145,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_987])).

tff(c_1003,plain,(
    ! [B_147] :
      ( v2_tex_2(B_147,'#skF_3')
      | ~ m1_subset_1(B_147,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_999])).

tff(c_1018,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_1003])).

tff(c_1260,plain,(
    ! [B_176,A_177] :
      ( v3_tex_2(B_176,A_177)
      | ~ v2_tex_2(B_176,A_177)
      | ~ v1_tops_1(B_176,A_177)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1270,plain,(
    ! [B_176] :
      ( v3_tex_2(B_176,'#skF_3')
      | ~ v2_tex_2(B_176,'#skF_3')
      | ~ v1_tops_1(B_176,'#skF_3')
      | ~ m1_subset_1(B_176,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_1260])).

tff(c_1282,plain,(
    ! [B_176] :
      ( v3_tex_2(B_176,'#skF_3')
      | ~ v2_tex_2(B_176,'#skF_3')
      | ~ v1_tops_1(B_176,'#skF_3')
      | ~ m1_subset_1(B_176,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1270])).

tff(c_1286,plain,(
    ! [B_178] :
      ( v3_tex_2(B_178,'#skF_3')
      | ~ v2_tex_2(B_178,'#skF_3')
      | ~ v1_tops_1(B_178,'#skF_3')
      | ~ m1_subset_1(B_178,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1282])).

tff(c_1298,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_1286])).

tff(c_1303,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_1018,c_1298])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1303])).

tff(c_1306,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1420,plain,(
    ! [A_200,B_201] :
      ( k2_pre_topc(A_200,B_201) = B_201
      | ~ v4_pre_topc(B_201,A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1434,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1420])).

tff(c_1444,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1434])).

tff(c_1446,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1444])).

tff(c_1448,plain,(
    ! [B_203,A_204] :
      ( v3_pre_topc(B_203,A_204)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ v1_tdlat_3(A_204)
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1889,plain,(
    ! [A_255,B_256] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_255),B_256),A_255)
      | ~ v1_tdlat_3(A_255)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255))) ) ),
    inference(resolution,[status(thm)],[c_6,c_1448])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( v4_pre_topc(B_13,A_11)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_11),B_13),A_11)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1894,plain,(
    ! [B_257,A_258] :
      ( v4_pre_topc(B_257,A_258)
      | ~ v1_tdlat_3(A_258)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_258))) ) ),
    inference(resolution,[status(thm)],[c_1889,c_18])).

tff(c_1911,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1894])).

tff(c_1922,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_1911])).

tff(c_1924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1446,c_1922])).

tff(c_1925,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1444])).

tff(c_1958,plain,(
    ! [B_262,A_263] :
      ( v1_tops_1(B_262,A_263)
      | k2_pre_topc(A_263,B_262) != u1_struct_0(A_263)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1972,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1958])).

tff(c_1982,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | u1_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1925,c_1972])).

tff(c_1984,plain,(
    u1_struct_0('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1982])).

tff(c_1310,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,B_180)
      | ~ m1_subset_1(A_179,k1_zfmisc_1(B_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1317,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_1310])).

tff(c_2490,plain,(
    ! [C_326,B_327,A_328] :
      ( C_326 = B_327
      | ~ r1_tarski(B_327,C_326)
      | ~ v2_tex_2(C_326,A_328)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ v3_tex_2(B_327,A_328)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2498,plain,(
    ! [A_328] :
      ( u1_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(u1_struct_0('#skF_3'),A_328)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ v3_tex_2('#skF_4',A_328)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(resolution,[status(thm)],[c_1317,c_2490])).

tff(c_2586,plain,(
    ! [A_340] :
      ( ~ v2_tex_2(u1_struct_0('#skF_3'),A_340)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ v3_tex_2('#skF_4',A_340)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ l1_pre_topc(A_340) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1984,c_2498])).

tff(c_2593,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_2586])).

tff(c_2597,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1306,c_2593])).

tff(c_2600,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2164,c_2597])).

tff(c_2603,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_2600])).

tff(c_2605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2603])).

tff(c_2607,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1982])).

tff(c_1307,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2609,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2607,c_1307])).

tff(c_2613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:19:59 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.30/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.30/1.81  
% 4.30/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.81  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.55/1.81  
% 4.55/1.81  %Foreground sorts:
% 4.55/1.81  
% 4.55/1.81  
% 4.55/1.81  %Background operators:
% 4.55/1.81  
% 4.55/1.81  
% 4.55/1.81  %Foreground operators:
% 4.55/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.55/1.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.55/1.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.81  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.55/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.55/1.81  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.55/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.81  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.55/1.81  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.55/1.81  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.55/1.81  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.55/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.81  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.55/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.55/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.55/1.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.55/1.81  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.55/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.81  
% 4.55/1.83  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.55/1.83  tff(f_36, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.55/1.83  tff(f_163, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 4.55/1.83  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.55/1.83  tff(f_129, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 4.55/1.83  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.55/1.83  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.55/1.83  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.55/1.83  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 4.55/1.83  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 4.55/1.83  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.55/1.83  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.55/1.83  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.55/1.83  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.55/1.83  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.83  tff(c_8, plain, (![A_5]: (~v1_subset_1(k2_subset_1(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.55/1.83  tff(c_72, plain, (![A_5]: (~v1_subset_1(A_5, A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 4.55/1.83  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.55/1.83  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.55/1.83  tff(c_58, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.55/1.83  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.55/1.83  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.55/1.83  tff(c_71, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.55/1.83  tff(c_2138, plain, (![B_283, A_284]: (v2_tex_2(B_283, A_284) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284) | ~v1_tdlat_3(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.55/1.83  tff(c_2164, plain, (![A_284]: (v2_tex_2(u1_struct_0(A_284), A_284) | ~l1_pre_topc(A_284) | ~v1_tdlat_3(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284))), inference(resolution, [status(thm)], [c_71, c_2138])).
% 4.55/1.83  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.55/1.83  tff(c_70, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.55/1.83  tff(c_87, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 4.55/1.83  tff(c_64, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.55/1.83  tff(c_88, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_87, c_64])).
% 4.55/1.83  tff(c_104, plain, (![B_50, A_51]: (v1_subset_1(B_50, A_51) | B_50=A_51 | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.55/1.83  tff(c_110, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_104])).
% 4.55/1.83  tff(c_117, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_87, c_110])).
% 4.55/1.83  tff(c_294, plain, (![A_74, B_75]: (k2_pre_topc(A_74, B_75)=B_75 | ~v4_pre_topc(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.83  tff(c_304, plain, (![B_75]: (k2_pre_topc('#skF_3', B_75)=B_75 | ~v4_pre_topc(B_75, '#skF_3') | ~m1_subset_1(B_75, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_294])).
% 4.55/1.83  tff(c_319, plain, (![B_76]: (k2_pre_topc('#skF_3', B_76)=B_76 | ~v4_pre_topc(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_304])).
% 4.55/1.83  tff(c_334, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_319])).
% 4.55/1.83  tff(c_335, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_334])).
% 4.55/1.83  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.83  tff(c_195, plain, (![B_63, A_64]: (v3_pre_topc(B_63, A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~v1_tdlat_3(A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.55/1.83  tff(c_205, plain, (![B_63]: (v3_pre_topc(B_63, '#skF_3') | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_4')) | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_195])).
% 4.55/1.83  tff(c_220, plain, (![B_65]: (v3_pre_topc(B_65, '#skF_3') | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_205])).
% 4.55/1.83  tff(c_233, plain, (![B_4]: (v3_pre_topc(k3_subset_1('#skF_4', B_4), '#skF_3') | ~m1_subset_1(B_4, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_220])).
% 4.55/1.83  tff(c_480, plain, (![B_96, A_97]: (v4_pre_topc(B_96, A_97) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_97), B_96), A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.55/1.83  tff(c_487, plain, (![B_96]: (v4_pre_topc(B_96, '#skF_3') | ~v3_pre_topc(k3_subset_1('#skF_4', B_96), '#skF_3') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_480])).
% 4.55/1.83  tff(c_530, plain, (![B_100]: (v4_pre_topc(B_100, '#skF_3') | ~v3_pre_topc(k3_subset_1('#skF_4', B_100), '#skF_3') | ~m1_subset_1(B_100, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117, c_487])).
% 4.55/1.83  tff(c_539, plain, (![B_101]: (v4_pre_topc(B_101, '#skF_3') | ~m1_subset_1(B_101, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_233, c_530])).
% 4.55/1.83  tff(c_551, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_539])).
% 4.55/1.83  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_335, c_551])).
% 4.55/1.83  tff(c_558, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_334])).
% 4.55/1.83  tff(c_689, plain, (![B_119, A_120]: (v1_tops_1(B_119, A_120) | k2_pre_topc(A_120, B_119)!=u1_struct_0(A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.55/1.83  tff(c_699, plain, (![B_119]: (v1_tops_1(B_119, '#skF_3') | k2_pre_topc('#skF_3', B_119)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_119, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_689])).
% 4.55/1.83  tff(c_714, plain, (![B_121]: (v1_tops_1(B_121, '#skF_3') | k2_pre_topc('#skF_3', B_121)!='#skF_4' | ~m1_subset_1(B_121, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117, c_699])).
% 4.55/1.83  tff(c_726, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_71, c_714])).
% 4.55/1.83  tff(c_731, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_726])).
% 4.55/1.83  tff(c_977, plain, (![B_145, A_146]: (v2_tex_2(B_145, A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v1_tdlat_3(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.55/1.83  tff(c_987, plain, (![B_145]: (v2_tex_2(B_145, '#skF_3') | ~m1_subset_1(B_145, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_977])).
% 4.55/1.83  tff(c_999, plain, (![B_145]: (v2_tex_2(B_145, '#skF_3') | ~m1_subset_1(B_145, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_987])).
% 4.55/1.83  tff(c_1003, plain, (![B_147]: (v2_tex_2(B_147, '#skF_3') | ~m1_subset_1(B_147, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_999])).
% 4.55/1.83  tff(c_1018, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_1003])).
% 4.55/1.83  tff(c_1260, plain, (![B_176, A_177]: (v3_tex_2(B_176, A_177) | ~v2_tex_2(B_176, A_177) | ~v1_tops_1(B_176, A_177) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.55/1.83  tff(c_1270, plain, (![B_176]: (v3_tex_2(B_176, '#skF_3') | ~v2_tex_2(B_176, '#skF_3') | ~v1_tops_1(B_176, '#skF_3') | ~m1_subset_1(B_176, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_1260])).
% 4.55/1.83  tff(c_1282, plain, (![B_176]: (v3_tex_2(B_176, '#skF_3') | ~v2_tex_2(B_176, '#skF_3') | ~v1_tops_1(B_176, '#skF_3') | ~m1_subset_1(B_176, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1270])).
% 4.55/1.83  tff(c_1286, plain, (![B_178]: (v3_tex_2(B_178, '#skF_3') | ~v2_tex_2(B_178, '#skF_3') | ~v1_tops_1(B_178, '#skF_3') | ~m1_subset_1(B_178, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_1282])).
% 4.55/1.83  tff(c_1298, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_1286])).
% 4.55/1.83  tff(c_1303, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_731, c_1018, c_1298])).
% 4.55/1.83  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1303])).
% 4.55/1.83  tff(c_1306, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_70])).
% 4.55/1.83  tff(c_1420, plain, (![A_200, B_201]: (k2_pre_topc(A_200, B_201)=B_201 | ~v4_pre_topc(B_201, A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.83  tff(c_1434, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1420])).
% 4.55/1.83  tff(c_1444, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1434])).
% 4.55/1.83  tff(c_1446, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1444])).
% 4.55/1.83  tff(c_1448, plain, (![B_203, A_204]: (v3_pre_topc(B_203, A_204) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_204))) | ~v1_tdlat_3(A_204) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.55/1.83  tff(c_1889, plain, (![A_255, B_256]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_255), B_256), A_255) | ~v1_tdlat_3(A_255) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))))), inference(resolution, [status(thm)], [c_6, c_1448])).
% 4.55/1.83  tff(c_18, plain, (![B_13, A_11]: (v4_pre_topc(B_13, A_11) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_11), B_13), A_11) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.55/1.83  tff(c_1894, plain, (![B_257, A_258]: (v4_pre_topc(B_257, A_258) | ~v1_tdlat_3(A_258) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_258))))), inference(resolution, [status(thm)], [c_1889, c_18])).
% 4.55/1.83  tff(c_1911, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1894])).
% 4.55/1.83  tff(c_1922, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_1911])).
% 4.55/1.83  tff(c_1924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1446, c_1922])).
% 4.55/1.83  tff(c_1925, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1444])).
% 4.55/1.83  tff(c_1958, plain, (![B_262, A_263]: (v1_tops_1(B_262, A_263) | k2_pre_topc(A_263, B_262)!=u1_struct_0(A_263) | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.55/1.83  tff(c_1972, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1958])).
% 4.55/1.83  tff(c_1982, plain, (v1_tops_1('#skF_4', '#skF_3') | u1_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1925, c_1972])).
% 4.55/1.83  tff(c_1984, plain, (u1_struct_0('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_1982])).
% 4.55/1.83  tff(c_1310, plain, (![A_179, B_180]: (r1_tarski(A_179, B_180) | ~m1_subset_1(A_179, k1_zfmisc_1(B_180)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.55/1.83  tff(c_1317, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1310])).
% 4.55/1.83  tff(c_2490, plain, (![C_326, B_327, A_328]: (C_326=B_327 | ~r1_tarski(B_327, C_326) | ~v2_tex_2(C_326, A_328) | ~m1_subset_1(C_326, k1_zfmisc_1(u1_struct_0(A_328))) | ~v3_tex_2(B_327, A_328) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.55/1.83  tff(c_2498, plain, (![A_328]: (u1_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(u1_struct_0('#skF_3'), A_328) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_328))) | ~v3_tex_2('#skF_4', A_328) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(resolution, [status(thm)], [c_1317, c_2490])).
% 4.55/1.83  tff(c_2586, plain, (![A_340]: (~v2_tex_2(u1_struct_0('#skF_3'), A_340) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_340))) | ~v3_tex_2('#skF_4', A_340) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_340))) | ~l1_pre_topc(A_340))), inference(negUnitSimplification, [status(thm)], [c_1984, c_2498])).
% 4.55/1.83  tff(c_2593, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_71, c_2586])).
% 4.55/1.83  tff(c_2597, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1306, c_2593])).
% 4.55/1.83  tff(c_2600, plain, (~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2164, c_2597])).
% 4.55/1.83  tff(c_2603, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_2600])).
% 4.55/1.83  tff(c_2605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2603])).
% 4.55/1.83  tff(c_2607, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1982])).
% 4.55/1.83  tff(c_1307, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_70])).
% 4.55/1.83  tff(c_2609, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2607, c_1307])).
% 4.55/1.83  tff(c_2613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2609])).
% 4.55/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.83  
% 4.55/1.83  Inference rules
% 4.55/1.83  ----------------------
% 4.55/1.83  #Ref     : 0
% 4.55/1.83  #Sup     : 483
% 4.55/1.83  #Fact    : 0
% 4.55/1.83  #Define  : 0
% 4.55/1.83  #Split   : 6
% 4.55/1.83  #Chain   : 0
% 4.55/1.83  #Close   : 0
% 4.55/1.83  
% 4.55/1.83  Ordering : KBO
% 4.55/1.83  
% 4.55/1.83  Simplification rules
% 4.55/1.83  ----------------------
% 4.55/1.83  #Subsume      : 98
% 4.55/1.83  #Demod        : 325
% 4.55/1.83  #Tautology    : 116
% 4.55/1.83  #SimpNegUnit  : 35
% 4.55/1.83  #BackRed      : 5
% 4.55/1.83  
% 4.55/1.83  #Partial instantiations: 0
% 4.55/1.83  #Strategies tried      : 1
% 4.55/1.83  
% 4.55/1.83  Timing (in seconds)
% 4.55/1.83  ----------------------
% 4.55/1.83  Preprocessing        : 0.36
% 4.55/1.83  Parsing              : 0.20
% 4.55/1.83  CNF conversion       : 0.02
% 4.55/1.83  Main loop            : 0.66
% 4.55/1.83  Inferencing          : 0.27
% 4.55/1.83  Reduction            : 0.18
% 4.55/1.83  Demodulation         : 0.12
% 4.55/1.83  BG Simplification    : 0.03
% 4.55/1.83  Subsumption          : 0.13
% 4.55/1.83  Abstraction          : 0.03
% 4.55/1.83  MUC search           : 0.00
% 4.55/1.83  Cooper               : 0.00
% 4.55/1.83  Total                : 1.07
% 4.55/1.83  Index Insertion      : 0.00
% 4.55/1.83  Index Deletion       : 0.00
% 4.55/1.83  Index Matching       : 0.00
% 4.55/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
