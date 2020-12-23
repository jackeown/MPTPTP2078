%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:28 EST 2020

% Result     : Theorem 4.25s
% Output     : CNFRefutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 203 expanded)
%              Number of leaves         :   32 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 694 expanded)
%              Number of equality atoms :   21 (  49 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_52,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_106,axiom,(
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

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_24,plain,(
    ! [B_17] :
      ( ~ v1_subset_1(B_17,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_53,plain,(
    ! [B_17] : ~ v1_subset_1(B_17,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_24])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_135,plain,(
    ! [A_41,B_42] :
      ( k2_pre_topc(A_41,B_42) = B_42
      | ~ v4_pre_topc(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_145,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_135])).

tff(c_154,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_145])).

tff(c_156,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_65,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_80,plain,(
    ! [A_32,B_33] :
      ( k3_subset_1(A_32,k3_subset_1(A_32,B_33)) = B_33
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_80])).

tff(c_301,plain,(
    ! [B_58,A_59] :
      ( v4_pre_topc(B_58,A_59)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_59),B_58),A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_311,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_301])).

tff(c_318,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_65,c_311])).

tff(c_319,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_322,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_319])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_322])).

tff(c_327,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_328,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_476,plain,(
    ! [B_62,A_63] :
      ( v3_pre_topc(B_62,A_63)
      | ~ v4_pre_topc(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ v3_tdlat_3(A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_479,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_328,c_476])).

tff(c_496,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_327,c_479])).

tff(c_14,plain,(
    ! [B_12,A_10] :
      ( v4_pre_topc(B_12,A_10)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_10),B_12),A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_505,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_496,c_14])).

tff(c_508,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_505])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_508])).

tff(c_511,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_517,plain,(
    ! [B_64,A_65] :
      ( v1_tops_1(B_64,A_65)
      | k2_pre_topc(A_65,B_64) != u1_struct_0(A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_527,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_517])).

tff(c_536,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | u1_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_511,c_527])).

tff(c_538,plain,(
    u1_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_592,plain,(
    ! [A_70,B_71] :
      ( k2_pre_topc(A_70,B_71) = u1_struct_0(A_70)
      | ~ v1_tops_1(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_602,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_592])).

tff(c_611,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_511,c_602])).

tff(c_612,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_611])).

tff(c_38,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_830,plain,(
    ! [B_83,A_84] :
      ( v1_tops_1(B_83,A_84)
      | ~ v3_tex_2(B_83,A_84)
      | ~ v3_pre_topc(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_840,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_830])).

tff(c_849,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_65,c_38,c_840])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_612,c_849])).

tff(c_853,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_36,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_856,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_36])).

tff(c_860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_856])).

tff(c_862,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_861,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1229,plain,(
    ! [B_115,A_116] :
      ( v3_pre_topc(B_115,A_116)
      | ~ v4_pre_topc(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ v3_tdlat_3(A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1239,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1229])).

tff(c_1248,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_861,c_1239])).

tff(c_1250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_862,c_1248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:17 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.25/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.25/2.17  
% 4.25/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.25/2.18  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 4.25/2.18  
% 4.25/2.18  %Foreground sorts:
% 4.25/2.18  
% 4.25/2.18  
% 4.25/2.18  %Background operators:
% 4.25/2.18  
% 4.25/2.18  
% 4.25/2.18  %Foreground operators:
% 4.25/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.25/2.18  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.25/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.25/2.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.25/2.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.25/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.25/2.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.25/2.18  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.25/2.18  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.25/2.18  tff('#skF_2', type, '#skF_2': $i).
% 4.25/2.18  tff('#skF_3', type, '#skF_3': $i).
% 4.25/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.25/2.18  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.25/2.18  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.25/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.25/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.25/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.25/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.25/2.18  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.25/2.18  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.25/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.25/2.18  
% 4.25/2.20  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.25/2.20  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.25/2.20  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.25/2.20  tff(f_128, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 4.25/2.20  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.25/2.20  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.25/2.20  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.25/2.20  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 4.25/2.20  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 4.25/2.20  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.25/2.20  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 4.25/2.20  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.25/2.20  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.25/2.20  tff(c_51, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.25/2.20  tff(c_24, plain, (![B_17]: (~v1_subset_1(B_17, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.25/2.20  tff(c_53, plain, (![B_17]: (~v1_subset_1(B_17, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_24])).
% 4.25/2.20  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.25/2.20  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.25/2.20  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.25/2.20  tff(c_135, plain, (![A_41, B_42]: (k2_pre_topc(A_41, B_42)=B_42 | ~v4_pre_topc(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.25/2.20  tff(c_145, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_135])).
% 4.25/2.20  tff(c_154, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_145])).
% 4.25/2.20  tff(c_156, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_154])).
% 4.25/2.20  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.25/2.20  tff(c_46, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.25/2.20  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.25/2.20  tff(c_40, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.25/2.20  tff(c_65, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 4.25/2.20  tff(c_80, plain, (![A_32, B_33]: (k3_subset_1(A_32, k3_subset_1(A_32, B_33))=B_33 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.25/2.20  tff(c_85, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_42, c_80])).
% 4.25/2.20  tff(c_301, plain, (![B_58, A_59]: (v4_pre_topc(B_58, A_59) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_59), B_58), A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.25/2.20  tff(c_311, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_301])).
% 4.25/2.20  tff(c_318, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_65, c_311])).
% 4.25/2.20  tff(c_319, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_318])).
% 4.25/2.20  tff(c_322, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_319])).
% 4.25/2.20  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_322])).
% 4.25/2.20  tff(c_327, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_318])).
% 4.25/2.20  tff(c_328, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_318])).
% 4.25/2.20  tff(c_476, plain, (![B_62, A_63]: (v3_pre_topc(B_62, A_63) | ~v4_pre_topc(B_62, A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~v3_tdlat_3(A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.25/2.20  tff(c_479, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_328, c_476])).
% 4.25/2.20  tff(c_496, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_327, c_479])).
% 4.25/2.20  tff(c_14, plain, (![B_12, A_10]: (v4_pre_topc(B_12, A_10) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_10), B_12), A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.25/2.20  tff(c_505, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_496, c_14])).
% 4.25/2.20  tff(c_508, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_505])).
% 4.25/2.20  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_508])).
% 4.25/2.20  tff(c_511, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_154])).
% 4.25/2.20  tff(c_517, plain, (![B_64, A_65]: (v1_tops_1(B_64, A_65) | k2_pre_topc(A_65, B_64)!=u1_struct_0(A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.25/2.20  tff(c_527, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_517])).
% 4.25/2.20  tff(c_536, plain, (v1_tops_1('#skF_3', '#skF_2') | u1_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_511, c_527])).
% 4.25/2.20  tff(c_538, plain, (u1_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_536])).
% 4.25/2.20  tff(c_592, plain, (![A_70, B_71]: (k2_pre_topc(A_70, B_71)=u1_struct_0(A_70) | ~v1_tops_1(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.25/2.20  tff(c_602, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_592])).
% 4.25/2.20  tff(c_611, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_511, c_602])).
% 4.25/2.20  tff(c_612, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_538, c_611])).
% 4.25/2.20  tff(c_38, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.25/2.20  tff(c_830, plain, (![B_83, A_84]: (v1_tops_1(B_83, A_84) | ~v3_tex_2(B_83, A_84) | ~v3_pre_topc(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.25/2.20  tff(c_840, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_830])).
% 4.25/2.20  tff(c_849, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_65, c_38, c_840])).
% 4.25/2.20  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_612, c_849])).
% 4.25/2.20  tff(c_853, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_536])).
% 4.25/2.20  tff(c_36, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.25/2.20  tff(c_856, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_853, c_36])).
% 4.25/2.20  tff(c_860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_856])).
% 4.25/2.20  tff(c_862, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.25/2.20  tff(c_861, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.25/2.20  tff(c_1229, plain, (![B_115, A_116]: (v3_pre_topc(B_115, A_116) | ~v4_pre_topc(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~v3_tdlat_3(A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.25/2.20  tff(c_1239, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1229])).
% 4.25/2.20  tff(c_1248, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_861, c_1239])).
% 4.25/2.20  tff(c_1250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_862, c_1248])).
% 4.25/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.25/2.20  
% 4.25/2.20  Inference rules
% 4.25/2.20  ----------------------
% 4.25/2.20  #Ref     : 0
% 4.25/2.20  #Sup     : 239
% 4.25/2.20  #Fact    : 0
% 4.25/2.20  #Define  : 0
% 4.25/2.20  #Split   : 11
% 4.25/2.20  #Chain   : 0
% 4.25/2.20  #Close   : 0
% 4.25/2.20  
% 4.25/2.20  Ordering : KBO
% 4.25/2.20  
% 4.25/2.20  Simplification rules
% 4.25/2.20  ----------------------
% 4.25/2.20  #Subsume      : 15
% 4.25/2.20  #Demod        : 238
% 4.25/2.20  #Tautology    : 126
% 4.25/2.20  #SimpNegUnit  : 25
% 4.25/2.20  #BackRed      : 15
% 4.25/2.20  
% 4.25/2.20  #Partial instantiations: 0
% 4.25/2.20  #Strategies tried      : 1
% 4.25/2.20  
% 4.25/2.20  Timing (in seconds)
% 4.25/2.20  ----------------------
% 4.25/2.21  Preprocessing        : 0.54
% 4.25/2.21  Parsing              : 0.28
% 4.25/2.21  CNF conversion       : 0.04
% 4.25/2.21  Main loop            : 0.73
% 4.25/2.21  Inferencing          : 0.26
% 4.25/2.21  Reduction            : 0.24
% 4.25/2.21  Demodulation         : 0.17
% 4.25/2.21  BG Simplification    : 0.04
% 4.25/2.21  Subsumption          : 0.12
% 4.25/2.21  Abstraction          : 0.04
% 4.25/2.21  MUC search           : 0.00
% 4.25/2.21  Cooper               : 0.00
% 4.25/2.21  Total                : 1.33
% 4.25/2.21  Index Insertion      : 0.00
% 4.25/2.21  Index Deletion       : 0.00
% 4.25/2.21  Index Matching       : 0.00
% 4.25/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
