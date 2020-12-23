%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:11 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 722 expanded)
%              Number of leaves         :   41 ( 252 expanded)
%              Depth                    :   12
%              Number of atoms          :  332 (2199 expanded)
%              Number of equality atoms :   37 ( 246 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_tex_2 > v3_pre_topc > v2_tops_1 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_240,negated_conjecture,(
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

tff(f_64,axiom,(
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

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_176,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_tops_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_190,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_222,axiom,(
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

tff(f_206,axiom,(
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

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_4897,plain,(
    ! [A_476,B_477] :
      ( k2_pre_topc(A_476,B_477) = B_477
      | ~ v4_pre_topc(B_477,A_476)
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0(A_476)))
      | ~ l1_pre_topc(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4907,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4897])).

tff(c_4912,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4907])).

tff(c_4913,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4912])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_64,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4955,plain,(
    ! [A_480,B_481] :
      ( k2_pre_topc(A_480,B_481) = u1_struct_0(A_480)
      | ~ v1_tops_1(B_481,A_480)
      | ~ m1_subset_1(B_481,k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ l1_pre_topc(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4965,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4955])).

tff(c_4970,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4965])).

tff(c_4971,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4970])).

tff(c_4824,plain,(
    ! [A_465,B_466] :
      ( k3_subset_1(A_465,k3_subset_1(A_465,B_466)) = B_466
      | ~ m1_subset_1(B_466,k1_zfmisc_1(A_465)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4827,plain,(
    k3_subset_1(u1_struct_0('#skF_3'),k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_4824])).

tff(c_5015,plain,(
    ! [A_489,B_490] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_489),B_490),A_489)
      | ~ v2_tops_1(B_490,A_489)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(u1_struct_0(A_489)))
      | ~ l1_pre_topc(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5025,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4827,c_5015])).

tff(c_5028,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5025])).

tff(c_5029,plain,
    ( ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4971,c_5028])).

tff(c_5030,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5029])).

tff(c_5033,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_4,c_5030])).

tff(c_5037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5033])).

tff(c_5039,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5029])).

tff(c_48,plain,(
    ! [B_45,A_42] :
      ( v3_pre_topc(B_45,A_42)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ v1_tdlat_3(A_42)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_5053,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_5039,c_48])).

tff(c_5078,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_64,c_5053])).

tff(c_6036,plain,(
    ! [A_573,B_574] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_573),B_574),A_573)
      | ~ m1_subset_1(B_574,k1_zfmisc_1(u1_struct_0(A_573)))
      | ~ v3_pre_topc(B_574,A_573)
      | ~ l1_pre_topc(A_573)
      | ~ v2_pre_topc(A_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6046,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4827,c_6036])).

tff(c_6048,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_5078,c_5039,c_6046])).

tff(c_6050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4913,c_6048])).

tff(c_6051,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4912])).

tff(c_6053,plain,(
    ! [A_575,B_576] :
      ( k2_pre_topc(A_575,B_576) = u1_struct_0(A_575)
      | ~ v1_tops_1(B_576,A_575)
      | ~ m1_subset_1(B_576,k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ l1_pre_topc(A_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_6063,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_6053])).

tff(c_6068,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6063])).

tff(c_6073,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6051,c_6068])).

tff(c_6074,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6073])).

tff(c_4881,plain,(
    ! [B_474,A_475] :
      ( v3_pre_topc(B_474,A_475)
      | ~ m1_subset_1(B_474,k1_zfmisc_1(u1_struct_0(A_475)))
      | ~ v1_tdlat_3(A_475)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_4891,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4881])).

tff(c_4896,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_64,c_4891])).

tff(c_76,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_79,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_70,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_80,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_70])).

tff(c_82,plain,(
    ! [B_59,A_60] :
      ( v1_subset_1(B_59,A_60)
      | B_59 = A_60
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_85,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_82])).

tff(c_88,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_85])).

tff(c_90,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60])).

tff(c_191,plain,(
    ! [A_73,B_74] :
      ( k2_pre_topc(A_73,B_74) = B_74
      | ~ v4_pre_topc(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,(
    ! [B_74] :
      ( k2_pre_topc('#skF_3',B_74) = B_74
      | ~ v4_pre_topc(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_191])).

tff(c_206,plain,(
    ! [B_75] :
      ( k2_pre_topc('#skF_3',B_75) = B_75
      | ~ v4_pre_topc(B_75,'#skF_3')
      | ~ m1_subset_1(B_75,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_201])).

tff(c_215,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_206])).

tff(c_216,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_242,plain,(
    ! [A_79,B_80] :
      ( k2_pre_topc(A_79,B_80) = u1_struct_0(A_79)
      | ~ v1_tops_1(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_252,plain,(
    ! [B_80] :
      ( k2_pre_topc('#skF_3',B_80) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_242])).

tff(c_262,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_3',B_82) = '#skF_4'
      | ~ v1_tops_1(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_88,c_252])).

tff(c_271,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_262])).

tff(c_272,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_110,plain,(
    ! [A_61,B_62] :
      ( k3_subset_1(A_61,k3_subset_1(A_61,B_62)) = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_90,c_110])).

tff(c_425,plain,(
    ! [A_97,B_98] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_97),B_98),A_97)
      | ~ v2_tops_1(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_432,plain,(
    ! [B_98] :
      ( v1_tops_1(k3_subset_1('#skF_4',B_98),'#skF_3')
      | ~ v2_tops_1(B_98,'#skF_3')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_425])).

tff(c_435,plain,(
    ! [B_99] :
      ( v1_tops_1(k3_subset_1('#skF_4',B_99),'#skF_3')
      | ~ v2_tops_1(B_99,'#skF_3')
      | ~ m1_subset_1(B_99,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_88,c_432])).

tff(c_445,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v2_tops_1(k3_subset_1('#skF_4','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_435])).

tff(c_447,plain,
    ( ~ v2_tops_1(k3_subset_1('#skF_4','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_445])).

tff(c_475,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_478,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_475])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_478])).

tff(c_484,plain,(
    m1_subset_1(k3_subset_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_217,plain,(
    ! [B_76,A_77] :
      ( v3_pre_topc(B_76,A_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ v1_tdlat_3(A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_227,plain,(
    ! [B_76] :
      ( v3_pre_topc(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_4'))
      | ~ v1_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_217])).

tff(c_231,plain,(
    ! [B_76] :
      ( v3_pre_topc(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_64,c_227])).

tff(c_522,plain,(
    v3_pre_topc(k3_subset_1('#skF_4','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_484,c_231])).

tff(c_1846,plain,(
    ! [A_219,B_220] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_219),B_220),A_219)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ v3_pre_topc(B_220,A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1856,plain,(
    ! [B_220] :
      ( v4_pre_topc(k3_subset_1('#skF_4',B_220),'#skF_3')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_220,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1846])).

tff(c_1859,plain,(
    ! [B_221] :
      ( v4_pre_topc(k3_subset_1('#skF_4',B_221),'#skF_3')
      | ~ m1_subset_1(B_221,k1_zfmisc_1('#skF_4'))
      | ~ v3_pre_topc(B_221,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_88,c_1856])).

tff(c_1869,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4'))
    | ~ v3_pre_topc(k3_subset_1('#skF_4','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1859])).

tff(c_1872,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_484,c_1869])).

tff(c_1874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_1872])).

tff(c_1875,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_1911,plain,(
    ! [B_226,A_227] :
      ( v1_tops_1(B_226,A_227)
      | k2_pre_topc(A_227,B_226) != u1_struct_0(A_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1921,plain,(
    ! [B_226] :
      ( v1_tops_1(B_226,'#skF_3')
      | k2_pre_topc('#skF_3',B_226) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_226,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1911])).

tff(c_1926,plain,(
    ! [B_228] :
      ( v1_tops_1(B_228,'#skF_3')
      | k2_pre_topc('#skF_3',B_228) != '#skF_4'
      | ~ m1_subset_1(B_228,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_88,c_1921])).

tff(c_1933,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_90,c_1926])).

tff(c_1937,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_1933])).

tff(c_3271,plain,(
    ! [B_341,A_342] :
      ( v2_tex_2(B_341,A_342)
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ l1_pre_topc(A_342)
      | ~ v1_tdlat_3(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_3281,plain,(
    ! [B_341] :
      ( v2_tex_2(B_341,'#skF_3')
      | ~ m1_subset_1(B_341,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_3271])).

tff(c_3285,plain,(
    ! [B_341] :
      ( v2_tex_2(B_341,'#skF_3')
      | ~ m1_subset_1(B_341,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_3281])).

tff(c_3287,plain,(
    ! [B_343] :
      ( v2_tex_2(B_343,'#skF_3')
      | ~ m1_subset_1(B_343,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3285])).

tff(c_3300,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_3287])).

tff(c_4758,plain,(
    ! [B_456,A_457] :
      ( v3_tex_2(B_456,A_457)
      | ~ v2_tex_2(B_456,A_457)
      | ~ v1_tops_1(B_456,A_457)
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_4771,plain,(
    ! [B_456] :
      ( v3_tex_2(B_456,'#skF_3')
      | ~ v2_tex_2(B_456,'#skF_3')
      | ~ v1_tops_1(B_456,'#skF_3')
      | ~ m1_subset_1(B_456,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_4758])).

tff(c_4776,plain,(
    ! [B_456] :
      ( v3_tex_2(B_456,'#skF_3')
      | ~ v2_tex_2(B_456,'#skF_3')
      | ~ v1_tops_1(B_456,'#skF_3')
      | ~ m1_subset_1(B_456,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_4771])).

tff(c_4778,plain,(
    ! [B_458] :
      ( v3_tex_2(B_458,'#skF_3')
      | ~ v2_tex_2(B_458,'#skF_3')
      | ~ v1_tops_1(B_458,'#skF_3')
      | ~ m1_subset_1(B_458,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4776])).

tff(c_4791,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_4778])).

tff(c_4800,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_3300,c_4791])).

tff(c_4802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4800])).

tff(c_4803,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_7346,plain,(
    ! [B_678,A_679] :
      ( v1_tops_1(B_678,A_679)
      | ~ v3_tex_2(B_678,A_679)
      | ~ v3_pre_topc(B_678,A_679)
      | ~ m1_subset_1(B_678,k1_zfmisc_1(u1_struct_0(A_679)))
      | ~ l1_pre_topc(A_679)
      | ~ v2_pre_topc(A_679)
      | v2_struct_0(A_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_7362,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_7346])).

tff(c_7372,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_4896,c_4803,c_7362])).

tff(c_7374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6074,c_7372])).

tff(c_7375,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6073])).

tff(c_4804,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_7380,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7375,c_4804])).

tff(c_7381,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7375,c_60])).

tff(c_44,plain,(
    ! [B_39] :
      ( ~ v1_subset_1(B_39,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_7423,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_7381,c_44])).

tff(c_7435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7380,c_7423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.66  
% 7.68/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.66  %$ v4_pre_topc > v3_tops_1 > v3_tex_2 > v3_pre_topc > v2_tops_1 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.68/2.66  
% 7.68/2.66  %Foreground sorts:
% 7.68/2.66  
% 7.68/2.66  
% 7.68/2.66  %Background operators:
% 7.68/2.66  
% 7.68/2.66  
% 7.68/2.66  %Foreground operators:
% 7.68/2.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.68/2.66  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.68/2.66  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.68/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.66  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.68/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.68/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.68/2.66  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 7.68/2.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.68/2.66  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 7.68/2.66  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.68/2.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.68/2.66  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.68/2.66  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.68/2.66  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.68/2.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.68/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.68/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.68/2.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.68/2.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.68/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.68/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.68/2.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.68/2.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.68/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.68/2.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.68/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.68/2.66  
% 7.68/2.68  tff(f_240, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 7.68/2.68  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.68/2.68  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.68/2.68  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 7.68/2.68  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.68/2.68  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 7.68/2.68  tff(f_176, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 7.68/2.68  tff(f_119, axiom, (![A, B]: ((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_tops_1)).
% 7.68/2.68  tff(f_155, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 7.68/2.68  tff(f_190, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 7.68/2.68  tff(f_222, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 7.68/2.68  tff(f_206, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 7.68/2.68  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 7.68/2.68  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 7.68/2.68  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_240])).
% 7.68/2.68  tff(c_4897, plain, (![A_476, B_477]: (k2_pre_topc(A_476, B_477)=B_477 | ~v4_pre_topc(B_477, A_476) | ~m1_subset_1(B_477, k1_zfmisc_1(u1_struct_0(A_476))) | ~l1_pre_topc(A_476))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.68/2.68  tff(c_4907, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4897])).
% 7.68/2.68  tff(c_4912, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4907])).
% 7.68/2.68  tff(c_4913, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_4912])).
% 7.68/2.68  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 7.68/2.68  tff(c_64, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 7.68/2.68  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.68/2.68  tff(c_4955, plain, (![A_480, B_481]: (k2_pre_topc(A_480, B_481)=u1_struct_0(A_480) | ~v1_tops_1(B_481, A_480) | ~m1_subset_1(B_481, k1_zfmisc_1(u1_struct_0(A_480))) | ~l1_pre_topc(A_480))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.68/2.68  tff(c_4965, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4955])).
% 7.68/2.68  tff(c_4970, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4965])).
% 7.68/2.68  tff(c_4971, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_4970])).
% 7.68/2.68  tff(c_4824, plain, (![A_465, B_466]: (k3_subset_1(A_465, k3_subset_1(A_465, B_466))=B_466 | ~m1_subset_1(B_466, k1_zfmisc_1(A_465)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.68  tff(c_4827, plain, (k3_subset_1(u1_struct_0('#skF_3'), k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_60, c_4824])).
% 7.68/2.68  tff(c_5015, plain, (![A_489, B_490]: (v1_tops_1(k3_subset_1(u1_struct_0(A_489), B_490), A_489) | ~v2_tops_1(B_490, A_489) | ~m1_subset_1(B_490, k1_zfmisc_1(u1_struct_0(A_489))) | ~l1_pre_topc(A_489))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.68/2.68  tff(c_5025, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4827, c_5015])).
% 7.68/2.68  tff(c_5028, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5025])).
% 7.68/2.68  tff(c_5029, plain, (~v2_tops_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_4971, c_5028])).
% 7.68/2.68  tff(c_5030, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_5029])).
% 7.68/2.68  tff(c_5033, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4, c_5030])).
% 7.68/2.68  tff(c_5037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_5033])).
% 7.68/2.68  tff(c_5039, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_5029])).
% 7.68/2.68  tff(c_48, plain, (![B_45, A_42]: (v3_pre_topc(B_45, A_42) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_42))) | ~v1_tdlat_3(A_42) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.68/2.68  tff(c_5053, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_5039, c_48])).
% 7.68/2.68  tff(c_5078, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_64, c_5053])).
% 7.68/2.68  tff(c_6036, plain, (![A_573, B_574]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_573), B_574), A_573) | ~m1_subset_1(B_574, k1_zfmisc_1(u1_struct_0(A_573))) | ~v3_pre_topc(B_574, A_573) | ~l1_pre_topc(A_573) | ~v2_pre_topc(A_573))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.68/2.68  tff(c_6046, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4827, c_6036])).
% 7.68/2.68  tff(c_6048, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_5078, c_5039, c_6046])).
% 7.68/2.68  tff(c_6050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4913, c_6048])).
% 7.68/2.68  tff(c_6051, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_4912])).
% 7.68/2.68  tff(c_6053, plain, (![A_575, B_576]: (k2_pre_topc(A_575, B_576)=u1_struct_0(A_575) | ~v1_tops_1(B_576, A_575) | ~m1_subset_1(B_576, k1_zfmisc_1(u1_struct_0(A_575))) | ~l1_pre_topc(A_575))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.68/2.68  tff(c_6063, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_6053])).
% 7.68/2.68  tff(c_6068, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6063])).
% 7.68/2.68  tff(c_6073, plain, (u1_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6051, c_6068])).
% 7.68/2.68  tff(c_6074, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_6073])).
% 7.68/2.68  tff(c_4881, plain, (![B_474, A_475]: (v3_pre_topc(B_474, A_475) | ~m1_subset_1(B_474, k1_zfmisc_1(u1_struct_0(A_475))) | ~v1_tdlat_3(A_475) | ~l1_pre_topc(A_475) | ~v2_pre_topc(A_475))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.68/2.68  tff(c_4891, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4881])).
% 7.68/2.68  tff(c_4896, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_64, c_4891])).
% 7.68/2.68  tff(c_76, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 7.68/2.68  tff(c_79, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_76])).
% 7.68/2.68  tff(c_70, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 7.68/2.68  tff(c_80, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_79, c_70])).
% 7.68/2.68  tff(c_82, plain, (![B_59, A_60]: (v1_subset_1(B_59, A_60) | B_59=A_60 | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.68/2.68  tff(c_85, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_82])).
% 7.68/2.68  tff(c_88, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_79, c_85])).
% 7.68/2.68  tff(c_90, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60])).
% 7.68/2.68  tff(c_191, plain, (![A_73, B_74]: (k2_pre_topc(A_73, B_74)=B_74 | ~v4_pre_topc(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.68/2.69  tff(c_201, plain, (![B_74]: (k2_pre_topc('#skF_3', B_74)=B_74 | ~v4_pre_topc(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_191])).
% 7.68/2.69  tff(c_206, plain, (![B_75]: (k2_pre_topc('#skF_3', B_75)=B_75 | ~v4_pre_topc(B_75, '#skF_3') | ~m1_subset_1(B_75, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_201])).
% 7.68/2.69  tff(c_215, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_206])).
% 7.68/2.69  tff(c_216, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_215])).
% 7.68/2.69  tff(c_242, plain, (![A_79, B_80]: (k2_pre_topc(A_79, B_80)=u1_struct_0(A_79) | ~v1_tops_1(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.68/2.69  tff(c_252, plain, (![B_80]: (k2_pre_topc('#skF_3', B_80)=u1_struct_0('#skF_3') | ~v1_tops_1(B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_242])).
% 7.68/2.69  tff(c_262, plain, (![B_82]: (k2_pre_topc('#skF_3', B_82)='#skF_4' | ~v1_tops_1(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_88, c_252])).
% 7.68/2.69  tff(c_271, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_262])).
% 7.68/2.69  tff(c_272, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_271])).
% 7.68/2.69  tff(c_110, plain, (![A_61, B_62]: (k3_subset_1(A_61, k3_subset_1(A_61, B_62))=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.68/2.69  tff(c_113, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_90, c_110])).
% 7.68/2.69  tff(c_425, plain, (![A_97, B_98]: (v1_tops_1(k3_subset_1(u1_struct_0(A_97), B_98), A_97) | ~v2_tops_1(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.68/2.69  tff(c_432, plain, (![B_98]: (v1_tops_1(k3_subset_1('#skF_4', B_98), '#skF_3') | ~v2_tops_1(B_98, '#skF_3') | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_425])).
% 7.68/2.69  tff(c_435, plain, (![B_99]: (v1_tops_1(k3_subset_1('#skF_4', B_99), '#skF_3') | ~v2_tops_1(B_99, '#skF_3') | ~m1_subset_1(B_99, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_88, c_432])).
% 7.68/2.69  tff(c_445, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v2_tops_1(k3_subset_1('#skF_4', '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_435])).
% 7.68/2.69  tff(c_447, plain, (~v2_tops_1(k3_subset_1('#skF_4', '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_272, c_445])).
% 7.68/2.69  tff(c_475, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_447])).
% 7.68/2.69  tff(c_478, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_475])).
% 7.68/2.69  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_478])).
% 7.68/2.69  tff(c_484, plain, (m1_subset_1(k3_subset_1('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_447])).
% 7.68/2.69  tff(c_217, plain, (![B_76, A_77]: (v3_pre_topc(B_76, A_77) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~v1_tdlat_3(A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.68/2.69  tff(c_227, plain, (![B_76]: (v3_pre_topc(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_4')) | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_217])).
% 7.68/2.69  tff(c_231, plain, (![B_76]: (v3_pre_topc(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_64, c_227])).
% 7.68/2.69  tff(c_522, plain, (v3_pre_topc(k3_subset_1('#skF_4', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_484, c_231])).
% 7.68/2.69  tff(c_1846, plain, (![A_219, B_220]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_219), B_220), A_219) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~v3_pre_topc(B_220, A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.68/2.69  tff(c_1856, plain, (![B_220]: (v4_pre_topc(k3_subset_1('#skF_4', B_220), '#skF_3') | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_220, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1846])).
% 7.68/2.69  tff(c_1859, plain, (![B_221]: (v4_pre_topc(k3_subset_1('#skF_4', B_221), '#skF_3') | ~m1_subset_1(B_221, k1_zfmisc_1('#skF_4')) | ~v3_pre_topc(B_221, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_88, c_1856])).
% 7.68/2.69  tff(c_1869, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4')) | ~v3_pre_topc(k3_subset_1('#skF_4', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_113, c_1859])).
% 7.68/2.69  tff(c_1872, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_522, c_484, c_1869])).
% 7.68/2.69  tff(c_1874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_1872])).
% 7.68/2.69  tff(c_1875, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_215])).
% 7.68/2.69  tff(c_1911, plain, (![B_226, A_227]: (v1_tops_1(B_226, A_227) | k2_pre_topc(A_227, B_226)!=u1_struct_0(A_227) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.68/2.69  tff(c_1921, plain, (![B_226]: (v1_tops_1(B_226, '#skF_3') | k2_pre_topc('#skF_3', B_226)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_226, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1911])).
% 7.68/2.69  tff(c_1926, plain, (![B_228]: (v1_tops_1(B_228, '#skF_3') | k2_pre_topc('#skF_3', B_228)!='#skF_4' | ~m1_subset_1(B_228, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_88, c_1921])).
% 7.68/2.69  tff(c_1933, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_90, c_1926])).
% 7.68/2.69  tff(c_1937, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_1933])).
% 7.68/2.69  tff(c_3271, plain, (![B_341, A_342]: (v2_tex_2(B_341, A_342) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_342))) | ~l1_pre_topc(A_342) | ~v1_tdlat_3(A_342) | ~v2_pre_topc(A_342) | v2_struct_0(A_342))), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.68/2.69  tff(c_3281, plain, (![B_341]: (v2_tex_2(B_341, '#skF_3') | ~m1_subset_1(B_341, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_3271])).
% 7.68/2.69  tff(c_3285, plain, (![B_341]: (v2_tex_2(B_341, '#skF_3') | ~m1_subset_1(B_341, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_3281])).
% 7.68/2.69  tff(c_3287, plain, (![B_343]: (v2_tex_2(B_343, '#skF_3') | ~m1_subset_1(B_343, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_3285])).
% 7.68/2.69  tff(c_3300, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_3287])).
% 7.68/2.69  tff(c_4758, plain, (![B_456, A_457]: (v3_tex_2(B_456, A_457) | ~v2_tex_2(B_456, A_457) | ~v1_tops_1(B_456, A_457) | ~m1_subset_1(B_456, k1_zfmisc_1(u1_struct_0(A_457))) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(cnfTransformation, [status(thm)], [f_222])).
% 7.68/2.69  tff(c_4771, plain, (![B_456]: (v3_tex_2(B_456, '#skF_3') | ~v2_tex_2(B_456, '#skF_3') | ~v1_tops_1(B_456, '#skF_3') | ~m1_subset_1(B_456, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_4758])).
% 7.68/2.69  tff(c_4776, plain, (![B_456]: (v3_tex_2(B_456, '#skF_3') | ~v2_tex_2(B_456, '#skF_3') | ~v1_tops_1(B_456, '#skF_3') | ~m1_subset_1(B_456, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_4771])).
% 7.68/2.69  tff(c_4778, plain, (![B_458]: (v3_tex_2(B_458, '#skF_3') | ~v2_tex_2(B_458, '#skF_3') | ~v1_tops_1(B_458, '#skF_3') | ~m1_subset_1(B_458, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_4776])).
% 7.68/2.69  tff(c_4791, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_4778])).
% 7.68/2.69  tff(c_4800, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1937, c_3300, c_4791])).
% 7.68/2.69  tff(c_4802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_4800])).
% 7.68/2.69  tff(c_4803, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_76])).
% 7.68/2.69  tff(c_7346, plain, (![B_678, A_679]: (v1_tops_1(B_678, A_679) | ~v3_tex_2(B_678, A_679) | ~v3_pre_topc(B_678, A_679) | ~m1_subset_1(B_678, k1_zfmisc_1(u1_struct_0(A_679))) | ~l1_pre_topc(A_679) | ~v2_pre_topc(A_679) | v2_struct_0(A_679))), inference(cnfTransformation, [status(thm)], [f_206])).
% 7.68/2.69  tff(c_7362, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_7346])).
% 7.68/2.69  tff(c_7372, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_4896, c_4803, c_7362])).
% 7.68/2.69  tff(c_7374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_6074, c_7372])).
% 7.68/2.69  tff(c_7375, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_6073])).
% 7.68/2.69  tff(c_4804, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_76])).
% 7.68/2.69  tff(c_7380, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7375, c_4804])).
% 7.68/2.69  tff(c_7381, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7375, c_60])).
% 7.68/2.69  tff(c_44, plain, (![B_39]: (~v1_subset_1(B_39, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.68/2.69  tff(c_7423, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_7381, c_44])).
% 7.68/2.69  tff(c_7435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7380, c_7423])).
% 7.68/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.69  
% 7.68/2.69  Inference rules
% 7.68/2.69  ----------------------
% 7.68/2.69  #Ref     : 0
% 7.68/2.69  #Sup     : 1506
% 7.68/2.69  #Fact    : 0
% 7.68/2.69  #Define  : 0
% 7.68/2.69  #Split   : 36
% 7.68/2.69  #Chain   : 0
% 7.68/2.69  #Close   : 0
% 7.68/2.69  
% 7.68/2.69  Ordering : KBO
% 7.68/2.69  
% 7.68/2.69  Simplification rules
% 7.68/2.69  ----------------------
% 7.68/2.69  #Subsume      : 247
% 7.68/2.69  #Demod        : 1368
% 7.68/2.69  #Tautology    : 481
% 7.68/2.69  #SimpNegUnit  : 254
% 7.68/2.69  #BackRed      : 38
% 7.68/2.69  
% 7.68/2.69  #Partial instantiations: 0
% 7.68/2.69  #Strategies tried      : 1
% 7.68/2.69  
% 7.68/2.69  Timing (in seconds)
% 7.68/2.69  ----------------------
% 7.68/2.69  Preprocessing        : 0.37
% 7.68/2.69  Parsing              : 0.20
% 7.68/2.69  CNF conversion       : 0.03
% 7.68/2.69  Main loop            : 1.51
% 7.68/2.69  Inferencing          : 0.55
% 7.68/2.69  Reduction            : 0.46
% 7.68/2.69  Demodulation         : 0.29
% 7.68/2.69  BG Simplification    : 0.06
% 7.68/2.69  Subsumption          : 0.31
% 7.68/2.69  Abstraction          : 0.06
% 7.68/2.69  MUC search           : 0.00
% 7.68/2.69  Cooper               : 0.00
% 7.68/2.69  Total                : 1.93
% 7.68/2.69  Index Insertion      : 0.00
% 7.68/2.69  Index Deletion       : 0.00
% 7.68/2.69  Index Matching       : 0.00
% 7.68/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
