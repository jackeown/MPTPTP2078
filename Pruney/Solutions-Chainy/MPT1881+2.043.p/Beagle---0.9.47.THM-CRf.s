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
% DateTime   : Thu Dec  3 10:30:12 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 431 expanded)
%              Number of leaves         :   31 ( 156 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 (1281 expanded)
%              Number of equality atoms :   17 ( 103 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_130,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_112,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
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

tff(c_6,plain,(
    ! [A_3] : ~ v1_subset_1(k2_subset_1(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_3] : ~ v1_subset_1(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_32,plain,(
    ! [A_20] :
      ( v2_tex_2(u1_struct_0(A_20),A_20)
      | ~ v1_tdlat_3(A_20)
      | ~ m1_subset_1(u1_struct_0(A_20),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_62,plain,(
    ! [A_20] :
      ( v2_tex_2(u1_struct_0(A_20),A_20)
      | ~ v1_tdlat_3(A_20)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_75,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_98,plain,(
    ! [B_41,A_42] :
      ( v1_subset_1(B_41,A_42)
      | B_41 = A_42
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_115,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_107])).

tff(c_14,plain,(
    ! [A_6] :
      ( m1_subset_1('#skF_1'(A_6),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_14])).

tff(c_137,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_131])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_tops_1('#skF_1'(A_6),A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_653,plain,(
    ! [B_97,A_98] :
      ( v2_tex_2(B_97,A_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v1_tdlat_3(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_656,plain,(
    ! [B_97] :
      ( v2_tex_2(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_653])).

tff(c_669,plain,(
    ! [B_97] :
      ( v2_tex_2(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_656])).

tff(c_674,plain,(
    ! [B_99] :
      ( v2_tex_2(B_99,'#skF_3')
      | ~ m1_subset_1(B_99,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_669])).

tff(c_686,plain,(
    v2_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_137,c_674])).

tff(c_975,plain,(
    ! [B_138,A_139] :
      ( v3_tex_2(B_138,A_139)
      | ~ v2_tex_2(B_138,A_139)
      | ~ v1_tops_1(B_138,A_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_981,plain,(
    ! [B_138] :
      ( v3_tex_2(B_138,'#skF_3')
      | ~ v2_tex_2(B_138,'#skF_3')
      | ~ v1_tops_1(B_138,'#skF_3')
      | ~ m1_subset_1(B_138,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_975])).

tff(c_995,plain,(
    ! [B_138] :
      ( v3_tex_2(B_138,'#skF_3')
      | ~ v2_tex_2(B_138,'#skF_3')
      | ~ v1_tops_1(B_138,'#skF_3')
      | ~ m1_subset_1(B_138,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_981])).

tff(c_1000,plain,(
    ! [B_140] :
      ( v3_tex_2(B_140,'#skF_3')
      | ~ v2_tex_2(B_140,'#skF_3')
      | ~ v1_tops_1(B_140,'#skF_3')
      | ~ m1_subset_1(B_140,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_995])).

tff(c_1006,plain,
    ( v3_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v1_tops_1('#skF_1'('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_137,c_1000])).

tff(c_1018,plain,
    ( v3_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v1_tops_1('#skF_1'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_1006])).

tff(c_1024,plain,(
    ~ v1_tops_1('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1018])).

tff(c_1048,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1024])).

tff(c_1052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1048])).

tff(c_1053,plain,(
    v3_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1018])).

tff(c_629,plain,(
    ! [A_94] :
      ( v2_tex_2(u1_struct_0(A_94),A_94)
      | ~ v1_tdlat_3(A_94)
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_632,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_629])).

tff(c_634,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_632])).

tff(c_635,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_634])).

tff(c_50,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_76,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_50])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( v1_subset_1(B_9,A_8)
      | B_9 = A_8
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,
    ( v1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | '#skF_1'('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_137,c_16])).

tff(c_148,plain,(
    '#skF_1'('#skF_3') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_162,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_12])).

tff(c_170,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_162])).

tff(c_188,plain,(
    ! [A_46] :
      ( v2_tex_2(u1_struct_0(A_46),A_46)
      | ~ v1_tdlat_3(A_46)
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_194,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_188])).

tff(c_197,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_194])).

tff(c_198,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_197])).

tff(c_554,plain,(
    ! [B_87,A_88] :
      ( v3_tex_2(B_87,A_88)
      | ~ v2_tex_2(B_87,A_88)
      | ~ v1_tops_1(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_560,plain,(
    ! [B_87] :
      ( v3_tex_2(B_87,'#skF_3')
      | ~ v2_tex_2(B_87,'#skF_3')
      | ~ v1_tops_1(B_87,'#skF_3')
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_554])).

tff(c_574,plain,(
    ! [B_87] :
      ( v3_tex_2(B_87,'#skF_3')
      | ~ v2_tex_2(B_87,'#skF_3')
      | ~ v1_tops_1(B_87,'#skF_3')
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_560])).

tff(c_579,plain,(
    ! [B_89] :
      ( v3_tex_2(B_89,'#skF_3')
      | ~ v2_tex_2(B_89,'#skF_3')
      | ~ v1_tops_1(B_89,'#skF_3')
      | ~ m1_subset_1(B_89,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_574])).

tff(c_590,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_579])).

tff(c_595,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_198,c_590])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_595])).

tff(c_599,plain,(
    '#skF_1'('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_92,plain,(
    ! [A_39] :
      ( m1_subset_1('#skF_1'(A_39),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_96,plain,(
    ! [A_39] :
      ( r1_tarski('#skF_1'(A_39),u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_128,plain,
    ( r1_tarski('#skF_1'('#skF_3'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_96])).

tff(c_135,plain,(
    r1_tarski('#skF_1'('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_128])).

tff(c_1087,plain,(
    ! [C_144,B_145,A_146] :
      ( C_144 = B_145
      | ~ r1_tarski(B_145,C_144)
      | ~ v2_tex_2(C_144,A_146)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ v3_tex_2(B_145,A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1103,plain,(
    ! [A_146] :
      ( '#skF_1'('#skF_3') = '#skF_4'
      | ~ v2_tex_2('#skF_4',A_146)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ v3_tex_2('#skF_1'('#skF_3'),A_146)
      | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(resolution,[status(thm)],[c_135,c_1087])).

tff(c_1154,plain,(
    ! [A_150] :
      ( ~ v2_tex_2('#skF_4',A_150)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ v3_tex_2('#skF_1'('#skF_3'),A_150)
      | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_599,c_1103])).

tff(c_1157,plain,
    ( ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1154])).

tff(c_1167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_137,c_1053,c_58,c_115,c_635,c_1157])).

tff(c_1168,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1178,plain,(
    ! [A_153,B_154] :
      ( r1_tarski(A_153,B_154)
      | ~ m1_subset_1(A_153,k1_zfmisc_1(B_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1189,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_1178])).

tff(c_1513,plain,(
    ! [C_204,B_205,A_206] :
      ( C_204 = B_205
      | ~ r1_tarski(B_205,C_204)
      | ~ v2_tex_2(C_204,A_206)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ v3_tex_2(B_205,A_206)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1530,plain,(
    ! [A_206] :
      ( u1_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(u1_struct_0('#skF_3'),A_206)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ v3_tex_2('#skF_4',A_206)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206) ) ),
    inference(resolution,[status(thm)],[c_1189,c_1513])).

tff(c_1535,plain,(
    ! [A_209] :
      ( ~ v2_tex_2(u1_struct_0('#skF_3'),A_209)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ v3_tex_2('#skF_4',A_209)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(splitLeft,[status(thm)],[c_1530])).

tff(c_1542,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1535])).

tff(c_1546,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1168,c_1542])).

tff(c_1549,plain,
    ( ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1546])).

tff(c_1552,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1549])).

tff(c_1554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1552])).

tff(c_1555,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1530])).

tff(c_1169,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1557,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_1169])).

tff(c_1561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.61  
% 3.70/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.61  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.70/1.61  
% 3.70/1.61  %Foreground sorts:
% 3.70/1.61  
% 3.70/1.61  
% 3.70/1.61  %Background operators:
% 3.70/1.61  
% 3.70/1.61  
% 3.70/1.61  %Foreground operators:
% 3.70/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.70/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.61  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.70/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.70/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.70/1.61  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.70/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.61  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.70/1.61  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.70/1.61  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.70/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.70/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.70/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.70/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.61  
% 3.70/1.63  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.70/1.63  tff(f_32, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 3.70/1.63  tff(f_130, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 3.70/1.63  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.70/1.63  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 3.70/1.63  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.70/1.63  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_tops_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_tops_1)).
% 3.70/1.63  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.70/1.63  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 3.70/1.63  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.63  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.70/1.63  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/1.63  tff(c_6, plain, (![A_3]: (~v1_subset_1(k2_subset_1(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.70/1.63  tff(c_57, plain, (![A_3]: (~v1_subset_1(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 3.70/1.63  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.70/1.63  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.70/1.63  tff(c_44, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.70/1.63  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.70/1.63  tff(c_58, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.70/1.63  tff(c_32, plain, (![A_20]: (v2_tex_2(u1_struct_0(A_20), A_20) | ~v1_tdlat_3(A_20) | ~m1_subset_1(u1_struct_0(A_20), k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.70/1.63  tff(c_62, plain, (![A_20]: (v2_tex_2(u1_struct_0(A_20), A_20) | ~v1_tdlat_3(A_20) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 3.70/1.63  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.70/1.63  tff(c_56, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.70/1.63  tff(c_75, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.70/1.63  tff(c_98, plain, (![B_41, A_42]: (v1_subset_1(B_41, A_42) | B_41=A_42 | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.70/1.63  tff(c_107, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_98])).
% 3.70/1.63  tff(c_115, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_75, c_107])).
% 3.70/1.63  tff(c_14, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.70/1.63  tff(c_131, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_14])).
% 3.70/1.63  tff(c_137, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_131])).
% 3.70/1.63  tff(c_12, plain, (![A_6]: (v1_tops_1('#skF_1'(A_6), A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.70/1.63  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.70/1.63  tff(c_653, plain, (![B_97, A_98]: (v2_tex_2(B_97, A_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v1_tdlat_3(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.70/1.63  tff(c_656, plain, (![B_97]: (v2_tex_2(B_97, '#skF_3') | ~m1_subset_1(B_97, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_653])).
% 3.70/1.63  tff(c_669, plain, (![B_97]: (v2_tex_2(B_97, '#skF_3') | ~m1_subset_1(B_97, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_656])).
% 3.70/1.63  tff(c_674, plain, (![B_99]: (v2_tex_2(B_99, '#skF_3') | ~m1_subset_1(B_99, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_669])).
% 3.70/1.63  tff(c_686, plain, (v2_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_137, c_674])).
% 3.70/1.63  tff(c_975, plain, (![B_138, A_139]: (v3_tex_2(B_138, A_139) | ~v2_tex_2(B_138, A_139) | ~v1_tops_1(B_138, A_139) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.70/1.63  tff(c_981, plain, (![B_138]: (v3_tex_2(B_138, '#skF_3') | ~v2_tex_2(B_138, '#skF_3') | ~v1_tops_1(B_138, '#skF_3') | ~m1_subset_1(B_138, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_975])).
% 3.70/1.63  tff(c_995, plain, (![B_138]: (v3_tex_2(B_138, '#skF_3') | ~v2_tex_2(B_138, '#skF_3') | ~v1_tops_1(B_138, '#skF_3') | ~m1_subset_1(B_138, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_981])).
% 3.70/1.63  tff(c_1000, plain, (![B_140]: (v3_tex_2(B_140, '#skF_3') | ~v2_tex_2(B_140, '#skF_3') | ~v1_tops_1(B_140, '#skF_3') | ~m1_subset_1(B_140, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_995])).
% 3.70/1.63  tff(c_1006, plain, (v3_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v2_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v1_tops_1('#skF_1'('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_137, c_1000])).
% 3.70/1.63  tff(c_1018, plain, (v3_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v1_tops_1('#skF_1'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_686, c_1006])).
% 3.70/1.63  tff(c_1024, plain, (~v1_tops_1('#skF_1'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1018])).
% 3.70/1.63  tff(c_1048, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1024])).
% 3.70/1.63  tff(c_1052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1048])).
% 3.70/1.63  tff(c_1053, plain, (v3_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1018])).
% 3.70/1.63  tff(c_629, plain, (![A_94]: (v2_tex_2(u1_struct_0(A_94), A_94) | ~v1_tdlat_3(A_94) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 3.70/1.63  tff(c_632, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_629])).
% 3.70/1.63  tff(c_634, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_632])).
% 3.70/1.63  tff(c_635, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_634])).
% 3.70/1.63  tff(c_50, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.70/1.63  tff(c_76, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_75, c_50])).
% 3.70/1.63  tff(c_16, plain, (![B_9, A_8]: (v1_subset_1(B_9, A_8) | B_9=A_8 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.70/1.63  tff(c_145, plain, (v1_subset_1('#skF_1'('#skF_3'), '#skF_4') | '#skF_1'('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_137, c_16])).
% 3.70/1.63  tff(c_148, plain, ('#skF_1'('#skF_3')='#skF_4'), inference(splitLeft, [status(thm)], [c_145])).
% 3.70/1.63  tff(c_162, plain, (v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_148, c_12])).
% 3.70/1.63  tff(c_170, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_162])).
% 3.70/1.63  tff(c_188, plain, (![A_46]: (v2_tex_2(u1_struct_0(A_46), A_46) | ~v1_tdlat_3(A_46) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 3.70/1.63  tff(c_194, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_188])).
% 3.70/1.63  tff(c_197, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_194])).
% 3.70/1.63  tff(c_198, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_197])).
% 3.70/1.63  tff(c_554, plain, (![B_87, A_88]: (v3_tex_2(B_87, A_88) | ~v2_tex_2(B_87, A_88) | ~v1_tops_1(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.70/1.63  tff(c_560, plain, (![B_87]: (v3_tex_2(B_87, '#skF_3') | ~v2_tex_2(B_87, '#skF_3') | ~v1_tops_1(B_87, '#skF_3') | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_554])).
% 3.70/1.63  tff(c_574, plain, (![B_87]: (v3_tex_2(B_87, '#skF_3') | ~v2_tex_2(B_87, '#skF_3') | ~v1_tops_1(B_87, '#skF_3') | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_560])).
% 3.70/1.63  tff(c_579, plain, (![B_89]: (v3_tex_2(B_89, '#skF_3') | ~v2_tex_2(B_89, '#skF_3') | ~v1_tops_1(B_89, '#skF_3') | ~m1_subset_1(B_89, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_574])).
% 3.70/1.63  tff(c_590, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_579])).
% 3.70/1.63  tff(c_595, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_198, c_590])).
% 3.70/1.63  tff(c_597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_595])).
% 3.70/1.63  tff(c_599, plain, ('#skF_1'('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_145])).
% 3.70/1.63  tff(c_92, plain, (![A_39]: (m1_subset_1('#skF_1'(A_39), k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.70/1.63  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.70/1.63  tff(c_96, plain, (![A_39]: (r1_tarski('#skF_1'(A_39), u1_struct_0(A_39)) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_92, c_8])).
% 3.70/1.63  tff(c_128, plain, (r1_tarski('#skF_1'('#skF_3'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_96])).
% 3.70/1.63  tff(c_135, plain, (r1_tarski('#skF_1'('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_128])).
% 3.70/1.63  tff(c_1087, plain, (![C_144, B_145, A_146]: (C_144=B_145 | ~r1_tarski(B_145, C_144) | ~v2_tex_2(C_144, A_146) | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(A_146))) | ~v3_tex_2(B_145, A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.63  tff(c_1103, plain, (![A_146]: ('#skF_1'('#skF_3')='#skF_4' | ~v2_tex_2('#skF_4', A_146) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_146))) | ~v3_tex_2('#skF_1'('#skF_3'), A_146) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(resolution, [status(thm)], [c_135, c_1087])).
% 3.70/1.63  tff(c_1154, plain, (![A_150]: (~v2_tex_2('#skF_4', A_150) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_150))) | ~v3_tex_2('#skF_1'('#skF_3'), A_150) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(negUnitSimplification, [status(thm)], [c_599, c_1103])).
% 3.70/1.63  tff(c_1157, plain, (~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_1154])).
% 3.70/1.63  tff(c_1167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_137, c_1053, c_58, c_115, c_635, c_1157])).
% 3.70/1.63  tff(c_1168, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 3.70/1.63  tff(c_1178, plain, (![A_153, B_154]: (r1_tarski(A_153, B_154) | ~m1_subset_1(A_153, k1_zfmisc_1(B_154)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.70/1.63  tff(c_1189, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_1178])).
% 3.70/1.63  tff(c_1513, plain, (![C_204, B_205, A_206]: (C_204=B_205 | ~r1_tarski(B_205, C_204) | ~v2_tex_2(C_204, A_206) | ~m1_subset_1(C_204, k1_zfmisc_1(u1_struct_0(A_206))) | ~v3_tex_2(B_205, A_206) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.63  tff(c_1530, plain, (![A_206]: (u1_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(u1_struct_0('#skF_3'), A_206) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_206))) | ~v3_tex_2('#skF_4', A_206) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206))), inference(resolution, [status(thm)], [c_1189, c_1513])).
% 3.70/1.63  tff(c_1535, plain, (![A_209]: (~v2_tex_2(u1_struct_0('#skF_3'), A_209) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_209))) | ~v3_tex_2('#skF_4', A_209) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(splitLeft, [status(thm)], [c_1530])).
% 3.70/1.63  tff(c_1542, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1535])).
% 3.70/1.63  tff(c_1546, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1168, c_1542])).
% 3.70/1.63  tff(c_1549, plain, (~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1546])).
% 3.70/1.63  tff(c_1552, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1549])).
% 3.70/1.63  tff(c_1554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1552])).
% 3.70/1.63  tff(c_1555, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1530])).
% 3.70/1.63  tff(c_1169, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 3.70/1.63  tff(c_1557, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_1169])).
% 3.70/1.63  tff(c_1561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_1557])).
% 3.70/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.63  
% 3.70/1.63  Inference rules
% 3.70/1.63  ----------------------
% 3.70/1.63  #Ref     : 0
% 3.70/1.63  #Sup     : 283
% 3.70/1.63  #Fact    : 0
% 3.70/1.63  #Define  : 0
% 3.70/1.63  #Split   : 6
% 3.70/1.63  #Chain   : 0
% 3.70/1.63  #Close   : 0
% 3.70/1.63  
% 3.70/1.63  Ordering : KBO
% 3.70/1.63  
% 3.70/1.63  Simplification rules
% 3.70/1.63  ----------------------
% 3.70/1.63  #Subsume      : 72
% 3.70/1.63  #Demod        : 292
% 3.70/1.63  #Tautology    : 68
% 3.70/1.63  #SimpNegUnit  : 44
% 3.70/1.63  #BackRed      : 8
% 3.70/1.63  
% 3.70/1.63  #Partial instantiations: 0
% 3.70/1.63  #Strategies tried      : 1
% 3.70/1.63  
% 3.70/1.63  Timing (in seconds)
% 3.70/1.63  ----------------------
% 3.70/1.64  Preprocessing        : 0.30
% 3.70/1.64  Parsing              : 0.16
% 3.70/1.64  CNF conversion       : 0.02
% 3.70/1.64  Main loop            : 0.53
% 3.70/1.64  Inferencing          : 0.20
% 3.70/1.64  Reduction            : 0.15
% 3.70/1.64  Demodulation         : 0.10
% 3.70/1.64  BG Simplification    : 0.02
% 3.70/1.64  Subsumption          : 0.11
% 3.70/1.64  Abstraction          : 0.02
% 3.70/1.64  MUC search           : 0.00
% 3.70/1.64  Cooper               : 0.00
% 3.70/1.64  Total                : 0.88
% 3.70/1.64  Index Insertion      : 0.00
% 3.70/1.64  Index Deletion       : 0.00
% 3.70/1.64  Index Matching       : 0.00
% 3.70/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
