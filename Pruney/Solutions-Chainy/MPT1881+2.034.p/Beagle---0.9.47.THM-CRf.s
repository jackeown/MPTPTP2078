%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:11 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 476 expanded)
%              Number of leaves         :   29 ( 171 expanded)
%              Depth                    :   12
%              Number of atoms          :  287 (1422 expanded)
%              Number of equality atoms :   16 ( 103 expanded)
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

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_119,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).

tff(f_71,axiom,(
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

tff(f_101,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_18,plain,(
    ! [B_9] :
      ( ~ v1_subset_1(B_9,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    ! [B_9] : ~ v1_subset_1(B_9,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_18])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1476,plain,(
    ! [B_197,A_198] :
      ( v2_tex_2(B_197,A_198)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198)
      | ~ v1_tdlat_3(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1497,plain,(
    ! [A_198] :
      ( v2_tex_2(u1_struct_0(A_198),A_198)
      | ~ l1_pre_topc(A_198)
      | ~ v1_tdlat_3(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(resolution,[status(thm)],[c_53,c_1476])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_68,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_71,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52])).

tff(c_92,plain,(
    ! [B_39,A_40] :
      ( v1_subset_1(B_39,A_40)
      | B_39 = A_40
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_92])).

tff(c_109,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_101])).

tff(c_12,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_1'(A_5),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_125,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_12])).

tff(c_131,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_125])).

tff(c_10,plain,(
    ! [A_5] :
      ( v1_tops_1('#skF_1'(A_5),A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_575,plain,(
    ! [B_88,A_89] :
      ( v2_tex_2(B_88,A_89)
      | ~ v3_tex_2(B_88,A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_578,plain,(
    ! [B_88] :
      ( v2_tex_2(B_88,'#skF_3')
      | ~ v3_tex_2(B_88,'#skF_3')
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_575])).

tff(c_611,plain,(
    ! [B_94] :
      ( v2_tex_2(B_94,'#skF_3')
      | ~ v3_tex_2(B_94,'#skF_3')
      | ~ m1_subset_1(B_94,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_578])).

tff(c_623,plain,
    ( v2_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v3_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_611])).

tff(c_626,plain,(
    ~ v3_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_623])).

tff(c_627,plain,(
    ! [B_95,A_96] :
      ( v2_tex_2(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v1_tdlat_3(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_630,plain,(
    ! [B_95] :
      ( v2_tex_2(B_95,'#skF_3')
      | ~ m1_subset_1(B_95,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_627])).

tff(c_643,plain,(
    ! [B_95] :
      ( v2_tex_2(B_95,'#skF_3')
      | ~ m1_subset_1(B_95,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_630])).

tff(c_648,plain,(
    ! [B_97] :
      ( v2_tex_2(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_643])).

tff(c_660,plain,(
    v2_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_648])).

tff(c_857,plain,(
    ! [B_122,A_123] :
      ( v3_tex_2(B_122,A_123)
      | ~ v2_tex_2(B_122,A_123)
      | ~ v1_tops_1(B_122,A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_860,plain,(
    ! [B_122] :
      ( v3_tex_2(B_122,'#skF_3')
      | ~ v2_tex_2(B_122,'#skF_3')
      | ~ v1_tops_1(B_122,'#skF_3')
      | ~ m1_subset_1(B_122,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_857])).

tff(c_873,plain,(
    ! [B_122] :
      ( v3_tex_2(B_122,'#skF_3')
      | ~ v2_tex_2(B_122,'#skF_3')
      | ~ v1_tops_1(B_122,'#skF_3')
      | ~ m1_subset_1(B_122,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_860])).

tff(c_878,plain,(
    ! [B_124] :
      ( v3_tex_2(B_124,'#skF_3')
      | ~ v2_tex_2(B_124,'#skF_3')
      | ~ v1_tops_1(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_873])).

tff(c_881,plain,
    ( v3_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v1_tops_1('#skF_1'('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_878])).

tff(c_892,plain,
    ( v3_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v1_tops_1('#skF_1'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_881])).

tff(c_893,plain,(
    ~ v1_tops_1('#skF_1'('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_892])).

tff(c_901,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_893])).

tff(c_905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_901])).

tff(c_907,plain,(
    v3_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_623])).

tff(c_943,plain,(
    ! [B_129,A_130] :
      ( v2_tex_2(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v1_tdlat_3(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_946,plain,(
    ! [B_129] :
      ( v2_tex_2(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_943])).

tff(c_959,plain,(
    ! [B_129] :
      ( v2_tex_2(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_946])).

tff(c_984,plain,(
    ! [B_133] :
      ( v2_tex_2(B_133,'#skF_3')
      | ~ m1_subset_1(B_133,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_959])).

tff(c_999,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_984])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( v1_subset_1(B_9,A_8)
      | B_9 = A_8
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_139,plain,
    ( v1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | '#skF_1'('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_131,c_16])).

tff(c_142,plain,(
    '#skF_1'('#skF_3') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_156,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_10])).

tff(c_164,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_156])).

tff(c_247,plain,(
    ! [B_52,A_53] :
      ( v2_tex_2(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v1_tdlat_3(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_250,plain,(
    ! [B_52] :
      ( v2_tex_2(B_52,'#skF_3')
      | ~ m1_subset_1(B_52,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_247])).

tff(c_263,plain,(
    ! [B_52] :
      ( v2_tex_2(B_52,'#skF_3')
      | ~ m1_subset_1(B_52,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_250])).

tff(c_288,plain,(
    ! [B_56] :
      ( v2_tex_2(B_56,'#skF_3')
      | ~ m1_subset_1(B_56,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_263])).

tff(c_298,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_288])).

tff(c_529,plain,(
    ! [B_85,A_86] :
      ( v3_tex_2(B_85,A_86)
      | ~ v2_tex_2(B_85,A_86)
      | ~ v1_tops_1(B_85,A_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_535,plain,(
    ! [B_85] :
      ( v3_tex_2(B_85,'#skF_3')
      | ~ v2_tex_2(B_85,'#skF_3')
      | ~ v1_tops_1(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_529])).

tff(c_549,plain,(
    ! [B_85] :
      ( v3_tex_2(B_85,'#skF_3')
      | ~ v2_tex_2(B_85,'#skF_3')
      | ~ v1_tops_1(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_535])).

tff(c_554,plain,(
    ! [B_87] :
      ( v3_tex_2(B_87,'#skF_3')
      | ~ v2_tex_2(B_87,'#skF_3')
      | ~ v1_tops_1(B_87,'#skF_3')
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_549])).

tff(c_565,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_554])).

tff(c_570,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_298,c_565])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_570])).

tff(c_574,plain,(
    '#skF_1'('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_85,plain,(
    ! [A_36] :
      ( m1_subset_1('#skF_1'(A_36),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [A_36] :
      ( r1_tarski('#skF_1'(A_36),u1_struct_0(A_36))
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_85,c_6])).

tff(c_122,plain,
    ( r1_tarski('#skF_1'('#skF_3'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_89])).

tff(c_129,plain,(
    r1_tarski('#skF_1'('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_122])).

tff(c_1273,plain,(
    ! [C_164,B_165,A_166] :
      ( C_164 = B_165
      | ~ r1_tarski(B_165,C_164)
      | ~ v2_tex_2(C_164,A_166)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v3_tex_2(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1281,plain,(
    ! [A_166] :
      ( '#skF_1'('#skF_3') = '#skF_4'
      | ~ v2_tex_2('#skF_4',A_166)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v3_tex_2('#skF_1'('#skF_3'),A_166)
      | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(resolution,[status(thm)],[c_129,c_1273])).

tff(c_1383,plain,(
    ! [A_179] :
      ( ~ v2_tex_2('#skF_4',A_179)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ v3_tex_2('#skF_1'('#skF_3'),A_179)
      | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_1281])).

tff(c_1386,plain,
    ( ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_1383])).

tff(c_1396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_131,c_907,c_53,c_109,c_999,c_1386])).

tff(c_1398,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1402,plain,(
    ! [A_183,B_184] :
      ( r1_tarski(A_183,B_184)
      | ~ m1_subset_1(A_183,k1_zfmisc_1(B_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1413,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_1402])).

tff(c_1712,plain,(
    ! [C_231,B_232,A_233] :
      ( C_231 = B_232
      | ~ r1_tarski(B_232,C_231)
      | ~ v2_tex_2(C_231,A_233)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ v3_tex_2(B_232,A_233)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1726,plain,(
    ! [A_233] :
      ( u1_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(u1_struct_0('#skF_3'),A_233)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ v3_tex_2('#skF_4',A_233)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_1413,c_1712])).

tff(c_1753,plain,(
    ! [A_236] :
      ( ~ v2_tex_2(u1_struct_0('#skF_3'),A_236)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ v3_tex_2('#skF_4',A_236)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(splitLeft,[status(thm)],[c_1726])).

tff(c_1760,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_1753])).

tff(c_1764,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1398,c_1760])).

tff(c_1767,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1497,c_1764])).

tff(c_1770,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_1767])).

tff(c_1772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1770])).

tff(c_1773,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1726])).

tff(c_1397,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1775,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1773,c_1397])).

tff(c_1779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_1775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.64  
% 3.90/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.64  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.90/1.64  
% 3.90/1.64  %Foreground sorts:
% 3.90/1.64  
% 3.90/1.64  
% 3.90/1.64  %Background operators:
% 3.90/1.64  
% 3.90/1.64  
% 3.90/1.64  %Foreground operators:
% 3.90/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.90/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.64  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.90/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.90/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.90/1.64  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.90/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.64  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.90/1.64  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.90/1.64  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.90/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.90/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.90/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.90/1.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.90/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.64  
% 3.90/1.67  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.90/1.67  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.90/1.67  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.90/1.67  tff(f_119, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 3.90/1.67  tff(f_85, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.90/1.67  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_tops_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_tops_1)).
% 3.90/1.67  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.90/1.67  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 3.90/1.67  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.90/1.67  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.90/1.67  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.90/1.67  tff(c_53, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.90/1.67  tff(c_18, plain, (![B_9]: (~v1_subset_1(B_9, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.67  tff(c_55, plain, (![B_9]: (~v1_subset_1(B_9, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_18])).
% 3.90/1.67  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/1.67  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/1.67  tff(c_40, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/1.67  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/1.67  tff(c_1476, plain, (![B_197, A_198]: (v2_tex_2(B_197, A_198) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198) | ~v1_tdlat_3(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/1.67  tff(c_1497, plain, (![A_198]: (v2_tex_2(u1_struct_0(A_198), A_198) | ~l1_pre_topc(A_198) | ~v1_tdlat_3(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198))), inference(resolution, [status(thm)], [c_53, c_1476])).
% 3.90/1.67  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/1.67  tff(c_46, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/1.67  tff(c_68, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.90/1.67  tff(c_52, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.90/1.67  tff(c_71, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_52])).
% 3.90/1.67  tff(c_92, plain, (![B_39, A_40]: (v1_subset_1(B_39, A_40) | B_39=A_40 | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.67  tff(c_101, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_92])).
% 3.90/1.67  tff(c_109, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_71, c_101])).
% 3.90/1.67  tff(c_12, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.90/1.67  tff(c_125, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_109, c_12])).
% 3.90/1.67  tff(c_131, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_125])).
% 3.90/1.67  tff(c_10, plain, (![A_5]: (v1_tops_1('#skF_1'(A_5), A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.90/1.67  tff(c_575, plain, (![B_88, A_89]: (v2_tex_2(B_88, A_89) | ~v3_tex_2(B_88, A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.67  tff(c_578, plain, (![B_88]: (v2_tex_2(B_88, '#skF_3') | ~v3_tex_2(B_88, '#skF_3') | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_575])).
% 3.90/1.67  tff(c_611, plain, (![B_94]: (v2_tex_2(B_94, '#skF_3') | ~v3_tex_2(B_94, '#skF_3') | ~m1_subset_1(B_94, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_578])).
% 3.90/1.67  tff(c_623, plain, (v2_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v3_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_131, c_611])).
% 3.90/1.67  tff(c_626, plain, (~v3_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_623])).
% 3.90/1.67  tff(c_627, plain, (![B_95, A_96]: (v2_tex_2(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v1_tdlat_3(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/1.67  tff(c_630, plain, (![B_95]: (v2_tex_2(B_95, '#skF_3') | ~m1_subset_1(B_95, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_627])).
% 3.90/1.67  tff(c_643, plain, (![B_95]: (v2_tex_2(B_95, '#skF_3') | ~m1_subset_1(B_95, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_630])).
% 3.90/1.67  tff(c_648, plain, (![B_97]: (v2_tex_2(B_97, '#skF_3') | ~m1_subset_1(B_97, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_643])).
% 3.90/1.67  tff(c_660, plain, (v2_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_131, c_648])).
% 3.90/1.67  tff(c_857, plain, (![B_122, A_123]: (v3_tex_2(B_122, A_123) | ~v2_tex_2(B_122, A_123) | ~v1_tops_1(B_122, A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.90/1.67  tff(c_860, plain, (![B_122]: (v3_tex_2(B_122, '#skF_3') | ~v2_tex_2(B_122, '#skF_3') | ~v1_tops_1(B_122, '#skF_3') | ~m1_subset_1(B_122, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_857])).
% 3.90/1.67  tff(c_873, plain, (![B_122]: (v3_tex_2(B_122, '#skF_3') | ~v2_tex_2(B_122, '#skF_3') | ~v1_tops_1(B_122, '#skF_3') | ~m1_subset_1(B_122, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_860])).
% 3.90/1.67  tff(c_878, plain, (![B_124]: (v3_tex_2(B_124, '#skF_3') | ~v2_tex_2(B_124, '#skF_3') | ~v1_tops_1(B_124, '#skF_3') | ~m1_subset_1(B_124, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_873])).
% 3.90/1.67  tff(c_881, plain, (v3_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v2_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v1_tops_1('#skF_1'('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_131, c_878])).
% 3.90/1.67  tff(c_892, plain, (v3_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v1_tops_1('#skF_1'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_660, c_881])).
% 3.90/1.67  tff(c_893, plain, (~v1_tops_1('#skF_1'('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_626, c_892])).
% 3.90/1.67  tff(c_901, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_893])).
% 3.90/1.67  tff(c_905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_901])).
% 3.90/1.67  tff(c_907, plain, (v3_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_623])).
% 3.90/1.67  tff(c_943, plain, (![B_129, A_130]: (v2_tex_2(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130) | ~v1_tdlat_3(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/1.67  tff(c_946, plain, (![B_129]: (v2_tex_2(B_129, '#skF_3') | ~m1_subset_1(B_129, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_943])).
% 3.90/1.67  tff(c_959, plain, (![B_129]: (v2_tex_2(B_129, '#skF_3') | ~m1_subset_1(B_129, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_946])).
% 3.90/1.67  tff(c_984, plain, (![B_133]: (v2_tex_2(B_133, '#skF_3') | ~m1_subset_1(B_133, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_959])).
% 3.90/1.67  tff(c_999, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_53, c_984])).
% 3.90/1.67  tff(c_16, plain, (![B_9, A_8]: (v1_subset_1(B_9, A_8) | B_9=A_8 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.67  tff(c_139, plain, (v1_subset_1('#skF_1'('#skF_3'), '#skF_4') | '#skF_1'('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_131, c_16])).
% 3.90/1.67  tff(c_142, plain, ('#skF_1'('#skF_3')='#skF_4'), inference(splitLeft, [status(thm)], [c_139])).
% 3.90/1.67  tff(c_156, plain, (v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_10])).
% 3.90/1.67  tff(c_164, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_156])).
% 3.90/1.67  tff(c_247, plain, (![B_52, A_53]: (v2_tex_2(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v1_tdlat_3(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/1.67  tff(c_250, plain, (![B_52]: (v2_tex_2(B_52, '#skF_3') | ~m1_subset_1(B_52, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_247])).
% 3.90/1.67  tff(c_263, plain, (![B_52]: (v2_tex_2(B_52, '#skF_3') | ~m1_subset_1(B_52, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_250])).
% 3.90/1.67  tff(c_288, plain, (![B_56]: (v2_tex_2(B_56, '#skF_3') | ~m1_subset_1(B_56, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_263])).
% 3.90/1.67  tff(c_298, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_53, c_288])).
% 3.90/1.67  tff(c_529, plain, (![B_85, A_86]: (v3_tex_2(B_85, A_86) | ~v2_tex_2(B_85, A_86) | ~v1_tops_1(B_85, A_86) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.90/1.67  tff(c_535, plain, (![B_85]: (v3_tex_2(B_85, '#skF_3') | ~v2_tex_2(B_85, '#skF_3') | ~v1_tops_1(B_85, '#skF_3') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_529])).
% 3.90/1.67  tff(c_549, plain, (![B_85]: (v3_tex_2(B_85, '#skF_3') | ~v2_tex_2(B_85, '#skF_3') | ~v1_tops_1(B_85, '#skF_3') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_535])).
% 3.90/1.67  tff(c_554, plain, (![B_87]: (v3_tex_2(B_87, '#skF_3') | ~v2_tex_2(B_87, '#skF_3') | ~v1_tops_1(B_87, '#skF_3') | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_549])).
% 3.90/1.67  tff(c_565, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_53, c_554])).
% 3.90/1.67  tff(c_570, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_298, c_565])).
% 3.90/1.67  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_570])).
% 3.90/1.67  tff(c_574, plain, ('#skF_1'('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_139])).
% 3.90/1.67  tff(c_85, plain, (![A_36]: (m1_subset_1('#skF_1'(A_36), k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.90/1.67  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.90/1.67  tff(c_89, plain, (![A_36]: (r1_tarski('#skF_1'(A_36), u1_struct_0(A_36)) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_85, c_6])).
% 3.90/1.67  tff(c_122, plain, (r1_tarski('#skF_1'('#skF_3'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_109, c_89])).
% 3.90/1.67  tff(c_129, plain, (r1_tarski('#skF_1'('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_122])).
% 3.90/1.67  tff(c_1273, plain, (![C_164, B_165, A_166]: (C_164=B_165 | ~r1_tarski(B_165, C_164) | ~v2_tex_2(C_164, A_166) | ~m1_subset_1(C_164, k1_zfmisc_1(u1_struct_0(A_166))) | ~v3_tex_2(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.67  tff(c_1281, plain, (![A_166]: ('#skF_1'('#skF_3')='#skF_4' | ~v2_tex_2('#skF_4', A_166) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_166))) | ~v3_tex_2('#skF_1'('#skF_3'), A_166) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(resolution, [status(thm)], [c_129, c_1273])).
% 3.90/1.67  tff(c_1383, plain, (![A_179]: (~v2_tex_2('#skF_4', A_179) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_179))) | ~v3_tex_2('#skF_1'('#skF_3'), A_179) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(negUnitSimplification, [status(thm)], [c_574, c_1281])).
% 3.90/1.67  tff(c_1386, plain, (~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_109, c_1383])).
% 3.90/1.67  tff(c_1396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_131, c_907, c_53, c_109, c_999, c_1386])).
% 3.90/1.67  tff(c_1398, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.90/1.67  tff(c_1402, plain, (![A_183, B_184]: (r1_tarski(A_183, B_184) | ~m1_subset_1(A_183, k1_zfmisc_1(B_184)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.90/1.67  tff(c_1413, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_1402])).
% 3.90/1.67  tff(c_1712, plain, (![C_231, B_232, A_233]: (C_231=B_232 | ~r1_tarski(B_232, C_231) | ~v2_tex_2(C_231, A_233) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0(A_233))) | ~v3_tex_2(B_232, A_233) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.67  tff(c_1726, plain, (![A_233]: (u1_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(u1_struct_0('#skF_3'), A_233) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_233))) | ~v3_tex_2('#skF_4', A_233) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_1413, c_1712])).
% 3.90/1.67  tff(c_1753, plain, (![A_236]: (~v2_tex_2(u1_struct_0('#skF_3'), A_236) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_236))) | ~v3_tex_2('#skF_4', A_236) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(splitLeft, [status(thm)], [c_1726])).
% 3.90/1.67  tff(c_1760, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_53, c_1753])).
% 3.90/1.67  tff(c_1764, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1398, c_1760])).
% 3.90/1.67  tff(c_1767, plain, (~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1497, c_1764])).
% 3.90/1.67  tff(c_1770, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_1767])).
% 3.90/1.67  tff(c_1772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1770])).
% 3.90/1.67  tff(c_1773, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1726])).
% 3.90/1.67  tff(c_1397, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 3.90/1.67  tff(c_1775, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1773, c_1397])).
% 3.90/1.67  tff(c_1779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_1775])).
% 3.90/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.67  
% 3.90/1.67  Inference rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Ref     : 0
% 3.90/1.67  #Sup     : 325
% 3.90/1.67  #Fact    : 0
% 3.90/1.67  #Define  : 0
% 3.90/1.67  #Split   : 4
% 3.90/1.67  #Chain   : 0
% 3.90/1.67  #Close   : 0
% 3.90/1.67  
% 3.90/1.67  Ordering : KBO
% 3.90/1.67  
% 3.90/1.67  Simplification rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Subsume      : 83
% 3.90/1.67  #Demod        : 327
% 3.90/1.67  #Tautology    : 70
% 3.90/1.67  #SimpNegUnit  : 53
% 3.90/1.67  #BackRed      : 8
% 3.90/1.67  
% 3.90/1.67  #Partial instantiations: 0
% 3.90/1.67  #Strategies tried      : 1
% 3.90/1.67  
% 3.90/1.67  Timing (in seconds)
% 3.90/1.67  ----------------------
% 3.90/1.67  Preprocessing        : 0.30
% 3.90/1.67  Parsing              : 0.16
% 3.90/1.67  CNF conversion       : 0.02
% 3.90/1.67  Main loop            : 0.58
% 3.90/1.67  Inferencing          : 0.23
% 3.90/1.67  Reduction            : 0.17
% 3.90/1.67  Demodulation         : 0.11
% 3.90/1.67  BG Simplification    : 0.02
% 3.90/1.67  Subsumption          : 0.12
% 3.90/1.67  Abstraction          : 0.02
% 3.90/1.67  MUC search           : 0.00
% 3.90/1.67  Cooper               : 0.00
% 3.90/1.67  Total                : 0.93
% 3.90/1.67  Index Insertion      : 0.00
% 3.90/1.67  Index Deletion       : 0.00
% 3.90/1.67  Index Matching       : 0.00
% 3.90/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
