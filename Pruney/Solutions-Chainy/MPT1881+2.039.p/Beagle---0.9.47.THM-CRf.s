%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:11 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :  189 (1117 expanded)
%              Number of leaves         :   41 ( 397 expanded)
%              Depth                    :   14
%              Number of atoms          :  463 (2927 expanded)
%              Number of equality atoms :   68 ( 461 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_174,negated_conjecture,(
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
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_156,axiom,(
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

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_140,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] : ~ v1_subset_1(k2_subset_1(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_3] : ~ v1_subset_1(A_3,A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_14,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_979,plain,(
    ! [A_140] :
      ( u1_struct_0(A_140) = k2_struct_0(A_140)
      | ~ l1_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_984,plain,(
    ! [A_141] :
      ( u1_struct_0(A_141) = k2_struct_0(A_141)
      | ~ l1_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_14,c_979])).

tff(c_988,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_984])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_990,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_54])).

tff(c_88,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_93,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_97,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_93])).

tff(c_70,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_87,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_98,plain,(
    ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_87])).

tff(c_64,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_105,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_64])).

tff(c_106,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_105])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_99,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_54])).

tff(c_122,plain,(
    ! [B_53,A_54] :
      ( v1_subset_1(B_53,A_54)
      | B_53 = A_54
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_125,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_99,c_122])).

tff(c_134,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_125])).

tff(c_16,plain,(
    ! [A_8] :
      ( v4_pre_topc(k2_struct_0(A_8),A_8)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_16])).

tff(c_153,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_149])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_143,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_97])).

tff(c_281,plain,(
    ! [A_71,B_72] :
      ( k2_pre_topc(A_71,B_72) = B_72
      | ~ v4_pre_topc(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_287,plain,(
    ! [B_72] :
      ( k2_pre_topc('#skF_3',B_72) = B_72
      | ~ v4_pre_topc(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_281])).

tff(c_307,plain,(
    ! [B_74] :
      ( k2_pre_topc('#skF_3',B_74) = B_74
      | ~ v4_pre_topc(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_287])).

tff(c_315,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_307])).

tff(c_319,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_315])).

tff(c_344,plain,(
    ! [B_77,A_78] :
      ( v1_tops_1(B_77,A_78)
      | k2_pre_topc(A_78,B_77) != u1_struct_0(A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_350,plain,(
    ! [B_77] :
      ( v1_tops_1(B_77,'#skF_3')
      | k2_pre_topc('#skF_3',B_77) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_77,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_344])).

tff(c_364,plain,(
    ! [B_79] :
      ( v1_tops_1(B_79,'#skF_3')
      | k2_pre_topc('#skF_3',B_79) != '#skF_4'
      | ~ m1_subset_1(B_79,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_143,c_350])).

tff(c_372,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_71,c_364])).

tff(c_376,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_372])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_58,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_527,plain,(
    ! [B_95,A_96] :
      ( v2_tex_2(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v1_tdlat_3(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_533,plain,(
    ! [B_95] :
      ( v2_tex_2(B_95,'#skF_3')
      | ~ m1_subset_1(B_95,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_527])).

tff(c_544,plain,(
    ! [B_95] :
      ( v2_tex_2(B_95,'#skF_3')
      | ~ m1_subset_1(B_95,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_533])).

tff(c_548,plain,(
    ! [B_97] :
      ( v2_tex_2(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_544])).

tff(c_558,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_548])).

tff(c_939,plain,(
    ! [B_137,A_138] :
      ( v3_tex_2(B_137,A_138)
      | ~ v2_tex_2(B_137,A_138)
      | ~ v1_tops_1(B_137,A_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_945,plain,(
    ! [B_137] :
      ( v3_tex_2(B_137,'#skF_3')
      | ~ v2_tex_2(B_137,'#skF_3')
      | ~ v1_tops_1(B_137,'#skF_3')
      | ~ m1_subset_1(B_137,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_939])).

tff(c_956,plain,(
    ! [B_137] :
      ( v3_tex_2(B_137,'#skF_3')
      | ~ v2_tex_2(B_137,'#skF_3')
      | ~ v1_tops_1(B_137,'#skF_3')
      | ~ m1_subset_1(B_137,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_945])).

tff(c_960,plain,(
    ! [B_139] :
      ( v3_tex_2(B_139,'#skF_3')
      | ~ v2_tex_2(B_139,'#skF_3')
      | ~ v1_tops_1(B_139,'#skF_3')
      | ~ m1_subset_1(B_139,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_956])).

tff(c_968,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_960])).

tff(c_972,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_558,c_968])).

tff(c_974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_972])).

tff(c_975,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1058,plain,(
    ! [B_155,A_156] :
      ( v2_tex_2(B_155,A_156)
      | ~ v3_tex_2(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1078,plain,(
    ! [A_157] :
      ( v2_tex_2(u1_struct_0(A_157),A_157)
      | ~ v3_tex_2(u1_struct_0(A_157),A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_71,c_1058])).

tff(c_1081,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1078])).

tff(c_1083,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_988,c_1081])).

tff(c_1084,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1083])).

tff(c_1129,plain,(
    ! [A_162,B_163] :
      ( k2_pre_topc(A_162,B_163) = B_163
      | ~ v4_pre_topc(B_163,A_162)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1149,plain,(
    ! [A_164] :
      ( k2_pre_topc(A_164,u1_struct_0(A_164)) = u1_struct_0(A_164)
      | ~ v4_pre_topc(u1_struct_0(A_164),A_164)
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_71,c_1129])).

tff(c_1152,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1149])).

tff(c_1154,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_988,c_988,c_1152])).

tff(c_1190,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1154])).

tff(c_1193,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1190])).

tff(c_1197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1193])).

tff(c_1198,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1154])).

tff(c_1222,plain,(
    ! [B_170,A_171] :
      ( v1_tops_1(B_170,A_171)
      | k2_pre_topc(A_171,B_170) != u1_struct_0(A_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1242,plain,(
    ! [A_172] :
      ( v1_tops_1(u1_struct_0(A_172),A_172)
      | k2_pre_topc(A_172,u1_struct_0(A_172)) != u1_struct_0(A_172)
      | ~ l1_pre_topc(A_172) ) ),
    inference(resolution,[status(thm)],[c_71,c_1222])).

tff(c_1245,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1242])).

tff(c_1247,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1198,c_988,c_988,c_1245])).

tff(c_1417,plain,(
    ! [B_189,A_190] :
      ( v2_tex_2(B_189,A_190)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190)
      | ~ v1_tdlat_3(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1427,plain,(
    ! [B_189] :
      ( v2_tex_2(B_189,'#skF_3')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1417])).

tff(c_1435,plain,(
    ! [B_189] :
      ( v2_tex_2(B_189,'#skF_3')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1427])).

tff(c_1438,plain,(
    ! [B_191] :
      ( v2_tex_2(B_191,'#skF_3')
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1435])).

tff(c_1453,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_1438])).

tff(c_1784,plain,(
    ! [B_229,A_230] :
      ( v3_tex_2(B_229,A_230)
      | ~ v2_tex_2(B_229,A_230)
      | ~ v1_tops_1(B_229,A_230)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1794,plain,(
    ! [B_229] :
      ( v3_tex_2(B_229,'#skF_3')
      | ~ v2_tex_2(B_229,'#skF_3')
      | ~ v1_tops_1(B_229,'#skF_3')
      | ~ m1_subset_1(B_229,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1784])).

tff(c_1802,plain,(
    ! [B_229] :
      ( v3_tex_2(B_229,'#skF_3')
      | ~ v2_tex_2(B_229,'#skF_3')
      | ~ v1_tops_1(B_229,'#skF_3')
      | ~ m1_subset_1(B_229,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1794])).

tff(c_1805,plain,(
    ! [B_231] :
      ( v3_tex_2(B_231,'#skF_3')
      | ~ v2_tex_2(B_231,'#skF_3')
      | ~ v1_tops_1(B_231,'#skF_3')
      | ~ m1_subset_1(B_231,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1802])).

tff(c_1816,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_1805])).

tff(c_1823,plain,(
    v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_1453,c_1816])).

tff(c_1825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1084,c_1823])).

tff(c_1826,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1083])).

tff(c_1876,plain,(
    ! [A_236,B_237] :
      ( k2_pre_topc(A_236,B_237) = B_237
      | ~ v4_pre_topc(B_237,A_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1886,plain,(
    ! [B_237] :
      ( k2_pre_topc('#skF_3',B_237) = B_237
      | ~ v4_pre_topc(B_237,'#skF_3')
      | ~ m1_subset_1(B_237,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1876])).

tff(c_1995,plain,(
    ! [B_247] :
      ( k2_pre_topc('#skF_3',B_247) = B_247
      | ~ v4_pre_topc(B_247,'#skF_3')
      | ~ m1_subset_1(B_247,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1886])).

tff(c_2008,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_990,c_1995])).

tff(c_2012,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2008])).

tff(c_1969,plain,(
    ! [B_244,A_245] :
      ( v1_tops_1(B_244,A_245)
      | k2_pre_topc(A_245,B_244) != u1_struct_0(A_245)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1979,plain,(
    ! [B_244] :
      ( v1_tops_1(B_244,'#skF_3')
      | k2_pre_topc('#skF_3',B_244) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_244,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1969])).

tff(c_2055,plain,(
    ! [B_253] :
      ( v1_tops_1(B_253,'#skF_3')
      | k2_pre_topc('#skF_3',B_253) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_253,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_988,c_1979])).

tff(c_2068,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_990,c_2055])).

tff(c_2092,plain,(
    k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2068])).

tff(c_2072,plain,(
    ! [A_254,B_255] :
      ( k2_pre_topc(A_254,B_255) = u1_struct_0(A_254)
      | ~ v1_tops_1(B_255,A_254)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2082,plain,(
    ! [B_255] :
      ( k2_pre_topc('#skF_3',B_255) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_255,'#skF_3')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_2072])).

tff(c_2103,plain,(
    ! [B_257] :
      ( k2_pre_topc('#skF_3',B_257) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_257,'#skF_3')
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_988,c_2082])).

tff(c_2110,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_990,c_2103])).

tff(c_2118,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2092,c_2110])).

tff(c_1902,plain,(
    ! [B_239,A_240] :
      ( v3_pre_topc(B_239,A_240)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ v1_tdlat_3(A_240)
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1912,plain,(
    ! [B_239] :
      ( v3_pre_topc(B_239,'#skF_3')
      | ~ m1_subset_1(B_239,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v1_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1902])).

tff(c_1922,plain,(
    ! [B_241] :
      ( v3_pre_topc(B_241,'#skF_3')
      | ~ m1_subset_1(B_241,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_1912])).

tff(c_1935,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_990,c_1922])).

tff(c_2575,plain,(
    ! [B_308,A_309] :
      ( v1_tops_1(B_308,A_309)
      | ~ v3_tex_2(B_308,A_309)
      | ~ v3_pre_topc(B_308,A_309)
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2585,plain,(
    ! [B_308] :
      ( v1_tops_1(B_308,'#skF_3')
      | ~ v3_tex_2(B_308,'#skF_3')
      | ~ v3_pre_topc(B_308,'#skF_3')
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_2575])).

tff(c_2593,plain,(
    ! [B_308] :
      ( v1_tops_1(B_308,'#skF_3')
      | ~ v3_tex_2(B_308,'#skF_3')
      | ~ v3_pre_topc(B_308,'#skF_3')
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2585])).

tff(c_2610,plain,(
    ! [B_311] :
      ( v1_tops_1(B_311,'#skF_3')
      | ~ v3_tex_2(B_311,'#skF_3')
      | ~ v3_pre_topc(B_311,'#skF_3')
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2593])).

tff(c_2617,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_990,c_2610])).

tff(c_2625,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_975,c_2617])).

tff(c_2627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2118,c_2625])).

tff(c_2629,plain,(
    k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2068])).

tff(c_2692,plain,(
    ! [B_317,A_318] :
      ( v4_pre_topc(B_317,A_318)
      | k2_pre_topc(A_318,B_317) != B_317
      | ~ v2_pre_topc(A_318)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_318)))
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2702,plain,(
    ! [B_317] :
      ( v4_pre_topc(B_317,'#skF_3')
      | k2_pre_topc('#skF_3',B_317) != B_317
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(B_317,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_2692])).

tff(c_2712,plain,(
    ! [B_319] :
      ( v4_pre_topc(B_319,'#skF_3')
      | k2_pre_topc('#skF_3',B_319) != B_319
      | ~ m1_subset_1(B_319,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_2702])).

tff(c_2719,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_990,c_2712])).

tff(c_2726,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2629,c_2719])).

tff(c_2727,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2012,c_2726])).

tff(c_996,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(A_144,B_145)
      | ~ m1_subset_1(A_144,k1_zfmisc_1(B_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1007,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_990,c_996])).

tff(c_3527,plain,(
    ! [C_388,B_389,A_390] :
      ( C_388 = B_389
      | ~ r1_tarski(B_389,C_388)
      | ~ v2_tex_2(C_388,A_390)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ v3_tex_2(B_389,A_390)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ l1_pre_topc(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3537,plain,(
    ! [A_390] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_390)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ v3_tex_2('#skF_4',A_390)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ l1_pre_topc(A_390) ) ),
    inference(resolution,[status(thm)],[c_1007,c_3527])).

tff(c_3549,plain,(
    ! [A_391] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_391)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_391)))
      | ~ v3_tex_2('#skF_4',A_391)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_391)))
      | ~ l1_pre_topc(A_391) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2727,c_3537])).

tff(c_3555,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_3549])).

tff(c_3559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_990,c_988,c_975,c_71,c_1826,c_3555])).

tff(c_3560,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2008])).

tff(c_3610,plain,(
    ! [B_397] :
      ( v1_tops_1(B_397,'#skF_3')
      | k2_pre_topc('#skF_3',B_397) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_397,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_988,c_1979])).

tff(c_3617,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_990,c_3610])).

tff(c_3624,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_struct_0('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3560,c_3617])).

tff(c_3628,plain,(
    k2_struct_0('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3624])).

tff(c_3629,plain,(
    ! [A_398,B_399] :
      ( k2_pre_topc(A_398,B_399) = u1_struct_0(A_398)
      | ~ v1_tops_1(B_399,A_398)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ l1_pre_topc(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3639,plain,(
    ! [B_399] :
      ( k2_pre_topc('#skF_3',B_399) = u1_struct_0('#skF_3')
      | ~ v1_tops_1(B_399,'#skF_3')
      | ~ m1_subset_1(B_399,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_3629])).

tff(c_3672,plain,(
    ! [B_402] :
      ( k2_pre_topc('#skF_3',B_402) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(B_402,'#skF_3')
      | ~ m1_subset_1(B_402,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_988,c_3639])).

tff(c_3679,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_990,c_3672])).

tff(c_3686,plain,
    ( k2_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3560,c_3679])).

tff(c_3687,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3628,c_3686])).

tff(c_4147,plain,(
    ! [B_453,A_454] :
      ( v1_tops_1(B_453,A_454)
      | ~ v3_tex_2(B_453,A_454)
      | ~ v3_pre_topc(B_453,A_454)
      | ~ m1_subset_1(B_453,k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4157,plain,(
    ! [B_453] :
      ( v1_tops_1(B_453,'#skF_3')
      | ~ v3_tex_2(B_453,'#skF_3')
      | ~ v3_pre_topc(B_453,'#skF_3')
      | ~ m1_subset_1(B_453,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_4147])).

tff(c_4165,plain,(
    ! [B_453] :
      ( v1_tops_1(B_453,'#skF_3')
      | ~ v3_tex_2(B_453,'#skF_3')
      | ~ v3_pre_topc(B_453,'#skF_3')
      | ~ m1_subset_1(B_453,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_4157])).

tff(c_4168,plain,(
    ! [B_455] :
      ( v1_tops_1(B_455,'#skF_3')
      | ~ v3_tex_2(B_455,'#skF_3')
      | ~ v3_pre_topc(B_455,'#skF_3')
      | ~ m1_subset_1(B_455,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4165])).

tff(c_4175,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_990,c_4168])).

tff(c_4183,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_975,c_4175])).

tff(c_4185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3687,c_4183])).

tff(c_4187,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3624])).

tff(c_976,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_989,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_976])).

tff(c_4203,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4187,c_989])).

tff(c_4214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.99  
% 5.14/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.47/2.00  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.47/2.00  
% 5.47/2.00  %Foreground sorts:
% 5.47/2.00  
% 5.47/2.00  
% 5.47/2.00  %Background operators:
% 5.47/2.00  
% 5.47/2.00  
% 5.47/2.00  %Foreground operators:
% 5.47/2.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.47/2.00  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.47/2.00  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.47/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.47/2.00  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.47/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.47/2.00  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.47/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.47/2.00  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.47/2.00  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.47/2.00  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.47/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.47/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.47/2.00  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.47/2.00  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.47/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.47/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.47/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.47/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.47/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.47/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.47/2.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.47/2.00  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.47/2.00  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.47/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.47/2.00  
% 5.47/2.03  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.47/2.03  tff(f_32, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 5.47/2.03  tff(f_174, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 5.47/2.03  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.47/2.03  tff(f_40, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.47/2.03  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.47/2.03  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 5.47/2.03  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.47/2.03  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.47/2.03  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 5.47/2.03  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 5.47/2.03  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 5.47/2.03  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 5.47/2.03  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 5.47/2.03  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 5.47/2.03  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.47/2.03  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.47/2.03  tff(c_6, plain, (![A_3]: (~v1_subset_1(k2_subset_1(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.03  tff(c_72, plain, (![A_3]: (~v1_subset_1(A_3, A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 5.47/2.03  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.47/2.03  tff(c_14, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.47/2.03  tff(c_979, plain, (![A_140]: (u1_struct_0(A_140)=k2_struct_0(A_140) | ~l1_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.47/2.03  tff(c_984, plain, (![A_141]: (u1_struct_0(A_141)=k2_struct_0(A_141) | ~l1_pre_topc(A_141))), inference(resolution, [status(thm)], [c_14, c_979])).
% 5.47/2.03  tff(c_988, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_984])).
% 5.47/2.03  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.47/2.03  tff(c_990, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_988, c_54])).
% 5.47/2.03  tff(c_88, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.47/2.03  tff(c_93, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_14, c_88])).
% 5.47/2.03  tff(c_97, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_93])).
% 5.47/2.03  tff(c_70, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.47/2.03  tff(c_87, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 5.47/2.03  tff(c_98, plain, (~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_87])).
% 5.47/2.03  tff(c_64, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.47/2.03  tff(c_105, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_64])).
% 5.47/2.03  tff(c_106, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_98, c_105])).
% 5.47/2.03  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.47/2.03  tff(c_99, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_54])).
% 5.47/2.03  tff(c_122, plain, (![B_53, A_54]: (v1_subset_1(B_53, A_54) | B_53=A_54 | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.47/2.03  tff(c_125, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_99, c_122])).
% 5.47/2.03  tff(c_134, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_98, c_125])).
% 5.47/2.03  tff(c_16, plain, (![A_8]: (v4_pre_topc(k2_struct_0(A_8), A_8) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.47/2.03  tff(c_149, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_134, c_16])).
% 5.47/2.03  tff(c_153, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_149])).
% 5.47/2.03  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.47/2.03  tff(c_71, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.47/2.03  tff(c_143, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_97])).
% 5.47/2.03  tff(c_281, plain, (![A_71, B_72]: (k2_pre_topc(A_71, B_72)=B_72 | ~v4_pre_topc(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.47/2.03  tff(c_287, plain, (![B_72]: (k2_pre_topc('#skF_3', B_72)=B_72 | ~v4_pre_topc(B_72, '#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_281])).
% 5.47/2.03  tff(c_307, plain, (![B_74]: (k2_pre_topc('#skF_3', B_74)=B_74 | ~v4_pre_topc(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_287])).
% 5.47/2.03  tff(c_315, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_307])).
% 5.47/2.03  tff(c_319, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_315])).
% 5.47/2.03  tff(c_344, plain, (![B_77, A_78]: (v1_tops_1(B_77, A_78) | k2_pre_topc(A_78, B_77)!=u1_struct_0(A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.47/2.03  tff(c_350, plain, (![B_77]: (v1_tops_1(B_77, '#skF_3') | k2_pre_topc('#skF_3', B_77)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_77, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_344])).
% 5.47/2.03  tff(c_364, plain, (![B_79]: (v1_tops_1(B_79, '#skF_3') | k2_pre_topc('#skF_3', B_79)!='#skF_4' | ~m1_subset_1(B_79, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_143, c_350])).
% 5.47/2.03  tff(c_372, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_71, c_364])).
% 5.47/2.03  tff(c_376, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_372])).
% 5.47/2.03  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.47/2.03  tff(c_58, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.47/2.03  tff(c_527, plain, (![B_95, A_96]: (v2_tex_2(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v1_tdlat_3(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.47/2.03  tff(c_533, plain, (![B_95]: (v2_tex_2(B_95, '#skF_3') | ~m1_subset_1(B_95, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_527])).
% 5.47/2.03  tff(c_544, plain, (![B_95]: (v2_tex_2(B_95, '#skF_3') | ~m1_subset_1(B_95, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_533])).
% 5.47/2.03  tff(c_548, plain, (![B_97]: (v2_tex_2(B_97, '#skF_3') | ~m1_subset_1(B_97, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_544])).
% 5.47/2.03  tff(c_558, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_548])).
% 5.47/2.03  tff(c_939, plain, (![B_137, A_138]: (v3_tex_2(B_137, A_138) | ~v2_tex_2(B_137, A_138) | ~v1_tops_1(B_137, A_138) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.47/2.03  tff(c_945, plain, (![B_137]: (v3_tex_2(B_137, '#skF_3') | ~v2_tex_2(B_137, '#skF_3') | ~v1_tops_1(B_137, '#skF_3') | ~m1_subset_1(B_137, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_939])).
% 5.47/2.03  tff(c_956, plain, (![B_137]: (v3_tex_2(B_137, '#skF_3') | ~v2_tex_2(B_137, '#skF_3') | ~v1_tops_1(B_137, '#skF_3') | ~m1_subset_1(B_137, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_945])).
% 5.47/2.03  tff(c_960, plain, (![B_139]: (v3_tex_2(B_139, '#skF_3') | ~v2_tex_2(B_139, '#skF_3') | ~v1_tops_1(B_139, '#skF_3') | ~m1_subset_1(B_139, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_956])).
% 5.47/2.03  tff(c_968, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_71, c_960])).
% 5.47/2.03  tff(c_972, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_558, c_968])).
% 5.47/2.03  tff(c_974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_972])).
% 5.47/2.03  tff(c_975, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_70])).
% 5.47/2.03  tff(c_1058, plain, (![B_155, A_156]: (v2_tex_2(B_155, A_156) | ~v3_tex_2(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.47/2.03  tff(c_1078, plain, (![A_157]: (v2_tex_2(u1_struct_0(A_157), A_157) | ~v3_tex_2(u1_struct_0(A_157), A_157) | ~l1_pre_topc(A_157))), inference(resolution, [status(thm)], [c_71, c_1058])).
% 5.47/2.03  tff(c_1081, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_988, c_1078])).
% 5.47/2.03  tff(c_1083, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_988, c_1081])).
% 5.47/2.03  tff(c_1084, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1083])).
% 5.47/2.03  tff(c_1129, plain, (![A_162, B_163]: (k2_pre_topc(A_162, B_163)=B_163 | ~v4_pre_topc(B_163, A_162) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.47/2.03  tff(c_1149, plain, (![A_164]: (k2_pre_topc(A_164, u1_struct_0(A_164))=u1_struct_0(A_164) | ~v4_pre_topc(u1_struct_0(A_164), A_164) | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_71, c_1129])).
% 5.47/2.03  tff(c_1152, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_988, c_1149])).
% 5.47/2.03  tff(c_1154, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_988, c_988, c_1152])).
% 5.47/2.03  tff(c_1190, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1154])).
% 5.47/2.03  tff(c_1193, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1190])).
% 5.47/2.03  tff(c_1197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1193])).
% 5.47/2.03  tff(c_1198, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1154])).
% 5.47/2.03  tff(c_1222, plain, (![B_170, A_171]: (v1_tops_1(B_170, A_171) | k2_pre_topc(A_171, B_170)!=u1_struct_0(A_171) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.47/2.03  tff(c_1242, plain, (![A_172]: (v1_tops_1(u1_struct_0(A_172), A_172) | k2_pre_topc(A_172, u1_struct_0(A_172))!=u1_struct_0(A_172) | ~l1_pre_topc(A_172))), inference(resolution, [status(thm)], [c_71, c_1222])).
% 5.47/2.03  tff(c_1245, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_988, c_1242])).
% 5.47/2.03  tff(c_1247, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1198, c_988, c_988, c_1245])).
% 5.47/2.03  tff(c_1417, plain, (![B_189, A_190]: (v2_tex_2(B_189, A_190) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190) | ~v1_tdlat_3(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.47/2.03  tff(c_1427, plain, (![B_189]: (v2_tex_2(B_189, '#skF_3') | ~m1_subset_1(B_189, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_1417])).
% 5.47/2.03  tff(c_1435, plain, (![B_189]: (v2_tex_2(B_189, '#skF_3') | ~m1_subset_1(B_189, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1427])).
% 5.47/2.03  tff(c_1438, plain, (![B_191]: (v2_tex_2(B_191, '#skF_3') | ~m1_subset_1(B_191, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_1435])).
% 5.47/2.03  tff(c_1453, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_71, c_1438])).
% 5.47/2.03  tff(c_1784, plain, (![B_229, A_230]: (v3_tex_2(B_229, A_230) | ~v2_tex_2(B_229, A_230) | ~v1_tops_1(B_229, A_230) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_156])).
% 5.47/2.03  tff(c_1794, plain, (![B_229]: (v3_tex_2(B_229, '#skF_3') | ~v2_tex_2(B_229, '#skF_3') | ~v1_tops_1(B_229, '#skF_3') | ~m1_subset_1(B_229, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_1784])).
% 5.47/2.03  tff(c_1802, plain, (![B_229]: (v3_tex_2(B_229, '#skF_3') | ~v2_tex_2(B_229, '#skF_3') | ~v1_tops_1(B_229, '#skF_3') | ~m1_subset_1(B_229, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1794])).
% 5.47/2.03  tff(c_1805, plain, (![B_231]: (v3_tex_2(B_231, '#skF_3') | ~v2_tex_2(B_231, '#skF_3') | ~v1_tops_1(B_231, '#skF_3') | ~m1_subset_1(B_231, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_1802])).
% 5.47/2.03  tff(c_1816, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_71, c_1805])).
% 5.47/2.03  tff(c_1823, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_1453, c_1816])).
% 5.47/2.03  tff(c_1825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1084, c_1823])).
% 5.47/2.03  tff(c_1826, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1083])).
% 5.47/2.03  tff(c_1876, plain, (![A_236, B_237]: (k2_pre_topc(A_236, B_237)=B_237 | ~v4_pre_topc(B_237, A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.47/2.03  tff(c_1886, plain, (![B_237]: (k2_pre_topc('#skF_3', B_237)=B_237 | ~v4_pre_topc(B_237, '#skF_3') | ~m1_subset_1(B_237, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_1876])).
% 5.47/2.03  tff(c_1995, plain, (![B_247]: (k2_pre_topc('#skF_3', B_247)=B_247 | ~v4_pre_topc(B_247, '#skF_3') | ~m1_subset_1(B_247, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1886])).
% 5.47/2.03  tff(c_2008, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_990, c_1995])).
% 5.47/2.03  tff(c_2012, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_2008])).
% 5.47/2.03  tff(c_1969, plain, (![B_244, A_245]: (v1_tops_1(B_244, A_245) | k2_pre_topc(A_245, B_244)!=u1_struct_0(A_245) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.47/2.03  tff(c_1979, plain, (![B_244]: (v1_tops_1(B_244, '#skF_3') | k2_pre_topc('#skF_3', B_244)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_244, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_1969])).
% 5.47/2.03  tff(c_2055, plain, (![B_253]: (v1_tops_1(B_253, '#skF_3') | k2_pre_topc('#skF_3', B_253)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_253, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_988, c_1979])).
% 5.47/2.03  tff(c_2068, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_990, c_2055])).
% 5.47/2.03  tff(c_2092, plain, (k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2068])).
% 5.47/2.03  tff(c_2072, plain, (![A_254, B_255]: (k2_pre_topc(A_254, B_255)=u1_struct_0(A_254) | ~v1_tops_1(B_255, A_254) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.47/2.03  tff(c_2082, plain, (![B_255]: (k2_pre_topc('#skF_3', B_255)=u1_struct_0('#skF_3') | ~v1_tops_1(B_255, '#skF_3') | ~m1_subset_1(B_255, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_2072])).
% 5.47/2.03  tff(c_2103, plain, (![B_257]: (k2_pre_topc('#skF_3', B_257)=k2_struct_0('#skF_3') | ~v1_tops_1(B_257, '#skF_3') | ~m1_subset_1(B_257, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_988, c_2082])).
% 5.47/2.03  tff(c_2110, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_990, c_2103])).
% 5.47/2.03  tff(c_2118, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2092, c_2110])).
% 5.47/2.03  tff(c_1902, plain, (![B_239, A_240]: (v3_pre_topc(B_239, A_240) | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0(A_240))) | ~v1_tdlat_3(A_240) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.47/2.03  tff(c_1912, plain, (![B_239]: (v3_pre_topc(B_239, '#skF_3') | ~m1_subset_1(B_239, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_1902])).
% 5.47/2.03  tff(c_1922, plain, (![B_241]: (v3_pre_topc(B_241, '#skF_3') | ~m1_subset_1(B_241, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_1912])).
% 5.47/2.03  tff(c_1935, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_990, c_1922])).
% 5.47/2.03  tff(c_2575, plain, (![B_308, A_309]: (v1_tops_1(B_308, A_309) | ~v3_tex_2(B_308, A_309) | ~v3_pre_topc(B_308, A_309) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0(A_309))) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.47/2.03  tff(c_2585, plain, (![B_308]: (v1_tops_1(B_308, '#skF_3') | ~v3_tex_2(B_308, '#skF_3') | ~v3_pre_topc(B_308, '#skF_3') | ~m1_subset_1(B_308, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_2575])).
% 5.47/2.03  tff(c_2593, plain, (![B_308]: (v1_tops_1(B_308, '#skF_3') | ~v3_tex_2(B_308, '#skF_3') | ~v3_pre_topc(B_308, '#skF_3') | ~m1_subset_1(B_308, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2585])).
% 5.47/2.03  tff(c_2610, plain, (![B_311]: (v1_tops_1(B_311, '#skF_3') | ~v3_tex_2(B_311, '#skF_3') | ~v3_pre_topc(B_311, '#skF_3') | ~m1_subset_1(B_311, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_2593])).
% 5.47/2.03  tff(c_2617, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_990, c_2610])).
% 5.47/2.03  tff(c_2625, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1935, c_975, c_2617])).
% 5.47/2.03  tff(c_2627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2118, c_2625])).
% 5.47/2.03  tff(c_2629, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_2068])).
% 5.47/2.03  tff(c_2692, plain, (![B_317, A_318]: (v4_pre_topc(B_317, A_318) | k2_pre_topc(A_318, B_317)!=B_317 | ~v2_pre_topc(A_318) | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0(A_318))) | ~l1_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.47/2.03  tff(c_2702, plain, (![B_317]: (v4_pre_topc(B_317, '#skF_3') | k2_pre_topc('#skF_3', B_317)!=B_317 | ~v2_pre_topc('#skF_3') | ~m1_subset_1(B_317, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_2692])).
% 5.47/2.03  tff(c_2712, plain, (![B_319]: (v4_pre_topc(B_319, '#skF_3') | k2_pre_topc('#skF_3', B_319)!=B_319 | ~m1_subset_1(B_319, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_2702])).
% 5.47/2.03  tff(c_2719, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_990, c_2712])).
% 5.47/2.03  tff(c_2726, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2629, c_2719])).
% 5.47/2.03  tff(c_2727, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2012, c_2726])).
% 5.47/2.03  tff(c_996, plain, (![A_144, B_145]: (r1_tarski(A_144, B_145) | ~m1_subset_1(A_144, k1_zfmisc_1(B_145)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.47/2.03  tff(c_1007, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_990, c_996])).
% 5.47/2.03  tff(c_3527, plain, (![C_388, B_389, A_390]: (C_388=B_389 | ~r1_tarski(B_389, C_388) | ~v2_tex_2(C_388, A_390) | ~m1_subset_1(C_388, k1_zfmisc_1(u1_struct_0(A_390))) | ~v3_tex_2(B_389, A_390) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_390))) | ~l1_pre_topc(A_390))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.47/2.03  tff(c_3537, plain, (![A_390]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_390) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_390))) | ~v3_tex_2('#skF_4', A_390) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_390))) | ~l1_pre_topc(A_390))), inference(resolution, [status(thm)], [c_1007, c_3527])).
% 5.47/2.03  tff(c_3549, plain, (![A_391]: (~v2_tex_2(k2_struct_0('#skF_3'), A_391) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_391))) | ~v3_tex_2('#skF_4', A_391) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_391))) | ~l1_pre_topc(A_391))), inference(negUnitSimplification, [status(thm)], [c_2727, c_3537])).
% 5.47/2.03  tff(c_3555, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_988, c_3549])).
% 5.47/2.03  tff(c_3559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_990, c_988, c_975, c_71, c_1826, c_3555])).
% 5.47/2.03  tff(c_3560, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2008])).
% 5.47/2.03  tff(c_3610, plain, (![B_397]: (v1_tops_1(B_397, '#skF_3') | k2_pre_topc('#skF_3', B_397)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_397, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_988, c_1979])).
% 5.47/2.03  tff(c_3617, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_990, c_3610])).
% 5.47/2.03  tff(c_3624, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_struct_0('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3560, c_3617])).
% 5.47/2.03  tff(c_3628, plain, (k2_struct_0('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_3624])).
% 5.47/2.03  tff(c_3629, plain, (![A_398, B_399]: (k2_pre_topc(A_398, B_399)=u1_struct_0(A_398) | ~v1_tops_1(B_399, A_398) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_398))) | ~l1_pre_topc(A_398))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.47/2.03  tff(c_3639, plain, (![B_399]: (k2_pre_topc('#skF_3', B_399)=u1_struct_0('#skF_3') | ~v1_tops_1(B_399, '#skF_3') | ~m1_subset_1(B_399, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_3629])).
% 5.47/2.03  tff(c_3672, plain, (![B_402]: (k2_pre_topc('#skF_3', B_402)=k2_struct_0('#skF_3') | ~v1_tops_1(B_402, '#skF_3') | ~m1_subset_1(B_402, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_988, c_3639])).
% 5.47/2.03  tff(c_3679, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_990, c_3672])).
% 5.47/2.03  tff(c_3686, plain, (k2_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3560, c_3679])).
% 5.47/2.03  tff(c_3687, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_3628, c_3686])).
% 5.47/2.03  tff(c_4147, plain, (![B_453, A_454]: (v1_tops_1(B_453, A_454) | ~v3_tex_2(B_453, A_454) | ~v3_pre_topc(B_453, A_454) | ~m1_subset_1(B_453, k1_zfmisc_1(u1_struct_0(A_454))) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.47/2.03  tff(c_4157, plain, (![B_453]: (v1_tops_1(B_453, '#skF_3') | ~v3_tex_2(B_453, '#skF_3') | ~v3_pre_topc(B_453, '#skF_3') | ~m1_subset_1(B_453, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_988, c_4147])).
% 5.47/2.03  tff(c_4165, plain, (![B_453]: (v1_tops_1(B_453, '#skF_3') | ~v3_tex_2(B_453, '#skF_3') | ~v3_pre_topc(B_453, '#skF_3') | ~m1_subset_1(B_453, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_4157])).
% 5.47/2.03  tff(c_4168, plain, (![B_455]: (v1_tops_1(B_455, '#skF_3') | ~v3_tex_2(B_455, '#skF_3') | ~v3_pre_topc(B_455, '#skF_3') | ~m1_subset_1(B_455, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_4165])).
% 5.47/2.03  tff(c_4175, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_990, c_4168])).
% 5.47/2.03  tff(c_4183, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1935, c_975, c_4175])).
% 5.47/2.03  tff(c_4185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3687, c_4183])).
% 5.47/2.03  tff(c_4187, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_3624])).
% 5.47/2.03  tff(c_976, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_70])).
% 5.47/2.03  tff(c_989, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_988, c_976])).
% 5.47/2.03  tff(c_4203, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4187, c_989])).
% 5.47/2.03  tff(c_4214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_4203])).
% 5.47/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.47/2.03  
% 5.47/2.03  Inference rules
% 5.47/2.03  ----------------------
% 5.47/2.03  #Ref     : 0
% 5.47/2.03  #Sup     : 761
% 5.47/2.03  #Fact    : 0
% 5.47/2.03  #Define  : 0
% 5.47/2.03  #Split   : 9
% 5.47/2.03  #Chain   : 0
% 5.47/2.03  #Close   : 0
% 5.47/2.03  
% 5.47/2.03  Ordering : KBO
% 5.47/2.03  
% 5.47/2.03  Simplification rules
% 5.47/2.03  ----------------------
% 5.47/2.03  #Subsume      : 166
% 5.47/2.03  #Demod        : 873
% 5.47/2.03  #Tautology    : 261
% 5.47/2.03  #SimpNegUnit  : 66
% 5.47/2.03  #BackRed      : 25
% 5.47/2.03  
% 5.47/2.03  #Partial instantiations: 0
% 5.47/2.03  #Strategies tried      : 1
% 5.47/2.03  
% 5.47/2.03  Timing (in seconds)
% 5.47/2.03  ----------------------
% 5.47/2.03  Preprocessing        : 0.34
% 5.47/2.03  Parsing              : 0.18
% 5.47/2.03  CNF conversion       : 0.03
% 5.47/2.03  Main loop            : 0.90
% 5.47/2.03  Inferencing          : 0.35
% 5.47/2.03  Reduction            : 0.28
% 5.47/2.03  Demodulation         : 0.18
% 5.47/2.03  BG Simplification    : 0.04
% 5.47/2.03  Subsumption          : 0.18
% 5.47/2.03  Abstraction          : 0.04
% 5.47/2.03  MUC search           : 0.00
% 5.47/2.03  Cooper               : 0.00
% 5.47/2.03  Total                : 1.31
% 5.47/2.03  Index Insertion      : 0.00
% 5.47/2.03  Index Deletion       : 0.00
% 5.47/2.03  Index Matching       : 0.00
% 5.47/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
