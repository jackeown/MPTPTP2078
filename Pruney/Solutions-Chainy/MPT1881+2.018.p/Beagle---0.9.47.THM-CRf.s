%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:08 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :  184 (1207 expanded)
%              Number of leaves         :   36 ( 426 expanded)
%              Depth                    :   14
%              Number of atoms          :  437 (3094 expanded)
%              Number of equality atoms :   73 ( 513 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_62,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_102,axiom,(
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

tff(c_63,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_28,plain,(
    ! [B_16] :
      ( ~ v1_subset_1(B_16,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_65,plain,(
    ! [B_16] : ~ v1_subset_1(B_16,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_28])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_12,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_652,plain,(
    ! [A_111] :
      ( u1_struct_0(A_111) = k2_struct_0(A_111)
      | ~ l1_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_658,plain,(
    ! [A_114] :
      ( u1_struct_0(A_114) = k2_struct_0(A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_12,c_652])).

tff(c_662,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_658])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_664,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_46])).

tff(c_80,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_89,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_62,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_78,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_90,plain,(
    ~ v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_78])).

tff(c_56,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_96,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_56])).

tff(c_97,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_91,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_46])).

tff(c_114,plain,(
    ! [B_47,A_48] :
      ( v1_subset_1(B_47,A_48)
      | B_47 = A_48
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_120,plain,
    ( v1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_91,c_114])).

tff(c_127,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_120])).

tff(c_14,plain,(
    ! [A_7] :
      ( v4_pre_topc(k2_struct_0(A_7),A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_14])).

tff(c_161,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_157])).

tff(c_151,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_89])).

tff(c_211,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,B_59) = B_59
      | ~ v4_pre_topc(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_214,plain,(
    ! [B_59] :
      ( k2_pre_topc('#skF_2',B_59) = B_59
      | ~ v4_pre_topc(B_59,'#skF_2')
      | ~ m1_subset_1(B_59,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_211])).

tff(c_227,plain,(
    ! [B_60] :
      ( k2_pre_topc('#skF_2',B_60) = B_60
      | ~ v4_pre_topc(B_60,'#skF_2')
      | ~ m1_subset_1(B_60,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_214])).

tff(c_235,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_227])).

tff(c_239,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_235])).

tff(c_310,plain,(
    ! [B_70,A_71] :
      ( v1_tops_1(B_70,A_71)
      | k2_pre_topc(A_71,B_70) != u1_struct_0(A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_313,plain,(
    ! [B_70] :
      ( v1_tops_1(B_70,'#skF_2')
      | k2_pre_topc('#skF_2',B_70) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_70,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_310])).

tff(c_326,plain,(
    ! [B_72] :
      ( v1_tops_1(B_72,'#skF_2')
      | k2_pre_topc('#skF_2',B_72) != '#skF_3'
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_151,c_313])).

tff(c_334,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_63,c_326])).

tff(c_338,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_334])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_437,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v1_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_440,plain,(
    ! [B_83] :
      ( v2_tex_2(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_437])).

tff(c_450,plain,(
    ! [B_83] :
      ( v2_tex_2(B_83,'#skF_2')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_440])).

tff(c_454,plain,(
    ! [B_85] :
      ( v2_tex_2(B_85,'#skF_2')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_450])).

tff(c_464,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_454])).

tff(c_614,plain,(
    ! [B_107,A_108] :
      ( v3_tex_2(B_107,A_108)
      | ~ v2_tex_2(B_107,A_108)
      | ~ v1_tops_1(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_617,plain,(
    ! [B_107] :
      ( v3_tex_2(B_107,'#skF_2')
      | ~ v2_tex_2(B_107,'#skF_2')
      | ~ v1_tops_1(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_614])).

tff(c_627,plain,(
    ! [B_107] :
      ( v3_tex_2(B_107,'#skF_2')
      | ~ v2_tex_2(B_107,'#skF_2')
      | ~ v1_tops_1(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_617])).

tff(c_631,plain,(
    ! [B_109] :
      ( v3_tex_2(B_109,'#skF_2')
      | ~ v2_tex_2(B_109,'#skF_2')
      | ~ v1_tops_1(B_109,'#skF_2')
      | ~ m1_subset_1(B_109,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_627])).

tff(c_639,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_631])).

tff(c_643,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_464,c_639])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_643])).

tff(c_646,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_646])).

tff(c_649,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_712,plain,(
    ! [B_123,A_124] :
      ( v2_tex_2(B_123,A_124)
      | ~ v3_tex_2(B_123,A_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_728,plain,(
    ! [A_125] :
      ( v2_tex_2(u1_struct_0(A_125),A_125)
      | ~ v3_tex_2(u1_struct_0(A_125),A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_63,c_712])).

tff(c_731,plain,
    ( v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_728])).

tff(c_733,plain,
    ( v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_662,c_731])).

tff(c_734,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_733])).

tff(c_775,plain,(
    ! [A_130,B_131] :
      ( k2_pre_topc(A_130,B_131) = B_131
      | ~ v4_pre_topc(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_791,plain,(
    ! [A_132] :
      ( k2_pre_topc(A_132,u1_struct_0(A_132)) = u1_struct_0(A_132)
      | ~ v4_pre_topc(u1_struct_0(A_132),A_132)
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_63,c_775])).

tff(c_794,plain,
    ( k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_791])).

tff(c_796,plain,
    ( k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2')
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_662,c_662,c_794])).

tff(c_797,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_800,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_797])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_800])).

tff(c_805,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_829,plain,(
    ! [B_134,A_135] :
      ( v1_tops_1(B_134,A_135)
      | k2_pre_topc(A_135,B_134) != u1_struct_0(A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_857,plain,(
    ! [A_137] :
      ( v1_tops_1(u1_struct_0(A_137),A_137)
      | k2_pre_topc(A_137,u1_struct_0(A_137)) != u1_struct_0(A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_63,c_829])).

tff(c_860,plain,
    ( v1_tops_1(k2_struct_0('#skF_2'),'#skF_2')
    | k2_pre_topc('#skF_2',u1_struct_0('#skF_2')) != u1_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_857])).

tff(c_862,plain,(
    v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_805,c_662,c_662,c_860])).

tff(c_1032,plain,(
    ! [B_155,A_156] :
      ( v2_tex_2(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v1_tdlat_3(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1035,plain,(
    ! [B_155] :
      ( v2_tex_2(B_155,'#skF_2')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_1032])).

tff(c_1045,plain,(
    ! [B_155] :
      ( v2_tex_2(B_155,'#skF_2')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1035])).

tff(c_1049,plain,(
    ! [B_157] :
      ( v2_tex_2(B_157,'#skF_2')
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1045])).

tff(c_1064,plain,(
    v2_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_1049])).

tff(c_1297,plain,(
    ! [B_186,A_187] :
      ( v3_tex_2(B_186,A_187)
      | ~ v2_tex_2(B_186,A_187)
      | ~ v1_tops_1(B_186,A_187)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1300,plain,(
    ! [B_186] :
      ( v3_tex_2(B_186,'#skF_2')
      | ~ v2_tex_2(B_186,'#skF_2')
      | ~ v1_tops_1(B_186,'#skF_2')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_1297])).

tff(c_1310,plain,(
    ! [B_186] :
      ( v3_tex_2(B_186,'#skF_2')
      | ~ v2_tex_2(B_186,'#skF_2')
      | ~ v1_tops_1(B_186,'#skF_2')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1300])).

tff(c_1314,plain,(
    ! [B_188] :
      ( v3_tex_2(B_188,'#skF_2')
      | ~ v2_tex_2(B_188,'#skF_2')
      | ~ v1_tops_1(B_188,'#skF_2')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1310])).

tff(c_1325,plain,
    ( v3_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_1314])).

tff(c_1332,plain,(
    v3_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_1064,c_1325])).

tff(c_1334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_734,c_1332])).

tff(c_1335,plain,(
    v2_tex_2(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_733])).

tff(c_1337,plain,(
    ! [A_189,B_190] :
      ( k2_pre_topc(A_189,B_190) = B_190
      | ~ v4_pre_topc(B_190,A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1340,plain,(
    ! [B_190] :
      ( k2_pre_topc('#skF_2',B_190) = B_190
      | ~ v4_pre_topc(B_190,'#skF_2')
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_1337])).

tff(c_1372,plain,(
    ! [B_192] :
      ( k2_pre_topc('#skF_2',B_192) = B_192
      | ~ v4_pre_topc(B_192,'#skF_2')
      | ~ m1_subset_1(B_192,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1340])).

tff(c_1384,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_664,c_1372])).

tff(c_1387,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1384])).

tff(c_1398,plain,(
    ! [B_193,A_194] :
      ( v1_tops_1(B_193,A_194)
      | k2_pre_topc(A_194,B_193) != u1_struct_0(A_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1401,plain,(
    ! [B_193] :
      ( v1_tops_1(B_193,'#skF_2')
      | k2_pre_topc('#skF_2',B_193) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_1398])).

tff(c_1444,plain,(
    ! [B_197] :
      ( v1_tops_1(B_197,'#skF_2')
      | k2_pre_topc('#skF_2',B_197) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_662,c_1401])).

tff(c_1456,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_664,c_1444])).

tff(c_1461,plain,(
    k2_pre_topc('#skF_2','#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1456])).

tff(c_1479,plain,(
    ! [A_201,B_202] :
      ( k2_pre_topc(A_201,B_202) = u1_struct_0(A_201)
      | ~ v1_tops_1(B_202,A_201)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1482,plain,(
    ! [B_202] :
      ( k2_pre_topc('#skF_2',B_202) = u1_struct_0('#skF_2')
      | ~ v1_tops_1(B_202,'#skF_2')
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_1479])).

tff(c_1523,plain,(
    ! [B_206] :
      ( k2_pre_topc('#skF_2',B_206) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_206,'#skF_2')
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_662,c_1482])).

tff(c_1526,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_664,c_1523])).

tff(c_1537,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1461,c_1526])).

tff(c_671,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(A_115,B_116)
      | ~ m1_subset_1(A_115,k1_zfmisc_1(B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_681,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_664,c_671])).

tff(c_2159,plain,(
    ! [C_264,B_265,A_266] :
      ( C_264 = B_265
      | ~ r1_tarski(B_265,C_264)
      | ~ v2_tex_2(C_264,A_266)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ v3_tex_2(B_265,A_266)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2173,plain,(
    ! [A_266] :
      ( k2_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(k2_struct_0('#skF_2'),A_266)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ v3_tex_2('#skF_3',A_266)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(resolution,[status(thm)],[c_681,c_2159])).

tff(c_2207,plain,(
    ! [A_271] :
      ( ~ v2_tex_2(k2_struct_0('#skF_2'),A_271)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ v3_tex_2('#skF_3',A_271)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(splitLeft,[status(thm)],[c_2173])).

tff(c_2210,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_2207])).

tff(c_2216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_664,c_662,c_649,c_63,c_1335,c_2210])).

tff(c_2217,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2173])).

tff(c_1386,plain,
    ( k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2')
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_1372])).

tff(c_1388,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1386])).

tff(c_1391,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1388])).

tff(c_1395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1391])).

tff(c_1396,plain,(
    k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1386])).

tff(c_1455,plain,
    ( v1_tops_1(k2_struct_0('#skF_2'),'#skF_2')
    | k2_pre_topc('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_1444])).

tff(c_1460,plain,(
    v1_tops_1(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_1455])).

tff(c_2242,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2217,c_1460])).

tff(c_2255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1537,c_2242])).

tff(c_2257,plain,(
    k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1456])).

tff(c_2408,plain,(
    ! [B_291,A_292] :
      ( v4_pre_topc(B_291,A_292)
      | k2_pre_topc(A_292,B_291) != B_291
      | ~ v2_pre_topc(A_292)
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2411,plain,(
    ! [B_291] :
      ( v4_pre_topc(B_291,'#skF_2')
      | k2_pre_topc('#skF_2',B_291) != B_291
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_subset_1(B_291,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_2408])).

tff(c_2460,plain,(
    ! [B_296] :
      ( v4_pre_topc(B_296,'#skF_2')
      | k2_pre_topc('#skF_2',B_296) != B_296
      | ~ m1_subset_1(B_296,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_2411])).

tff(c_2463,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_664,c_2460])).

tff(c_2473,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_2463])).

tff(c_2474,plain,(
    k2_struct_0('#skF_2') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1387,c_2473])).

tff(c_2963,plain,(
    ! [C_339,B_340,A_341] :
      ( C_339 = B_340
      | ~ r1_tarski(B_340,C_339)
      | ~ v2_tex_2(C_339,A_341)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ v3_tex_2(B_340,A_341)
      | ~ m1_subset_1(B_340,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2971,plain,(
    ! [A_341] :
      ( k2_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(k2_struct_0('#skF_2'),A_341)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ v3_tex_2('#skF_3',A_341)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(resolution,[status(thm)],[c_681,c_2963])).

tff(c_2982,plain,(
    ! [A_342] :
      ( ~ v2_tex_2(k2_struct_0('#skF_2'),A_342)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ v3_tex_2('#skF_3',A_342)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ l1_pre_topc(A_342) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2474,c_2971])).

tff(c_2985,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_2982])).

tff(c_2991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_664,c_662,c_649,c_63,c_1335,c_2985])).

tff(c_2992,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1384])).

tff(c_2994,plain,(
    ! [B_343,A_344] :
      ( v1_tops_1(B_343,A_344)
      | k2_pre_topc(A_344,B_343) != u1_struct_0(A_344)
      | ~ m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2997,plain,(
    ! [B_343] :
      ( v1_tops_1(B_343,'#skF_2')
      | k2_pre_topc('#skF_2',B_343) != u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_343,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_2994])).

tff(c_3024,plain,(
    ! [B_345] :
      ( v1_tops_1(B_345,'#skF_2')
      | k2_pre_topc('#skF_2',B_345) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_345,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_662,c_2997])).

tff(c_3027,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_664,c_3024])).

tff(c_3037,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | k2_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2992,c_3027])).

tff(c_3044,plain,(
    k2_struct_0('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3037])).

tff(c_3752,plain,(
    ! [C_412,B_413,A_414] :
      ( C_412 = B_413
      | ~ r1_tarski(B_413,C_412)
      | ~ v2_tex_2(C_412,A_414)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ v3_tex_2(B_413,A_414)
      | ~ m1_subset_1(B_413,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ l1_pre_topc(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3760,plain,(
    ! [A_414] :
      ( k2_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(k2_struct_0('#skF_2'),A_414)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ v3_tex_2('#skF_3',A_414)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ l1_pre_topc(A_414) ) ),
    inference(resolution,[status(thm)],[c_681,c_3752])).

tff(c_3771,plain,(
    ! [A_415] :
      ( ~ v2_tex_2(k2_struct_0('#skF_2'),A_415)
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ v3_tex_2('#skF_3',A_415)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ l1_pre_topc(A_415) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3044,c_3760])).

tff(c_3774,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_3771])).

tff(c_3780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_664,c_662,c_649,c_63,c_1335,c_3774])).

tff(c_3782,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3037])).

tff(c_650,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_663,plain,(
    v1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_650])).

tff(c_3792,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3782,c_663])).

tff(c_3801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_3792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:15:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.96  
% 5.19/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.96  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.19/1.96  
% 5.19/1.96  %Foreground sorts:
% 5.19/1.96  
% 5.19/1.96  
% 5.19/1.96  %Background operators:
% 5.19/1.96  
% 5.19/1.96  
% 5.19/1.96  %Foreground operators:
% 5.19/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.19/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/1.96  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.19/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.19/1.96  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.19/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/1.96  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 5.19/1.96  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.19/1.96  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.19/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.19/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.19/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/1.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.19/1.96  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.19/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.19/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.19/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.19/1.96  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.19/1.96  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.19/1.96  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.19/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/1.96  
% 5.19/1.99  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.19/1.99  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.19/1.99  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 5.19/1.99  tff(f_150, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 5.19/1.99  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.19/1.99  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.19/1.99  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 5.19/1.99  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.19/1.99  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 5.19/1.99  tff(f_116, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 5.19/1.99  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 5.19/1.99  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.19/1.99  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.19/1.99  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.19/1.99  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.19/1.99  tff(c_63, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.19/1.99  tff(c_28, plain, (![B_16]: (~v1_subset_1(B_16, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.19/1.99  tff(c_65, plain, (![B_16]: (~v1_subset_1(B_16, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_28])).
% 5.19/1.99  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/1.99  tff(c_12, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.19/1.99  tff(c_652, plain, (![A_111]: (u1_struct_0(A_111)=k2_struct_0(A_111) | ~l1_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.19/1.99  tff(c_658, plain, (![A_114]: (u1_struct_0(A_114)=k2_struct_0(A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_12, c_652])).
% 5.19/1.99  tff(c_662, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_658])).
% 5.19/1.99  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/1.99  tff(c_664, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_46])).
% 5.19/1.99  tff(c_80, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.19/1.99  tff(c_85, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_12, c_80])).
% 5.19/1.99  tff(c_89, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_85])).
% 5.19/1.99  tff(c_62, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/1.99  tff(c_78, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 5.19/1.99  tff(c_90, plain, (~v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_78])).
% 5.19/1.99  tff(c_56, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/1.99  tff(c_96, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_56])).
% 5.19/1.99  tff(c_97, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_96])).
% 5.19/1.99  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/1.99  tff(c_91, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_46])).
% 5.19/1.99  tff(c_114, plain, (![B_47, A_48]: (v1_subset_1(B_47, A_48) | B_47=A_48 | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.19/1.99  tff(c_120, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_91, c_114])).
% 5.19/1.99  tff(c_127, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_90, c_120])).
% 5.19/1.99  tff(c_14, plain, (![A_7]: (v4_pre_topc(k2_struct_0(A_7), A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/1.99  tff(c_157, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_127, c_14])).
% 5.19/1.99  tff(c_161, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_157])).
% 5.19/1.99  tff(c_151, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_89])).
% 5.19/1.99  tff(c_211, plain, (![A_58, B_59]: (k2_pre_topc(A_58, B_59)=B_59 | ~v4_pre_topc(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.19/1.99  tff(c_214, plain, (![B_59]: (k2_pre_topc('#skF_2', B_59)=B_59 | ~v4_pre_topc(B_59, '#skF_2') | ~m1_subset_1(B_59, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_211])).
% 5.19/1.99  tff(c_227, plain, (![B_60]: (k2_pre_topc('#skF_2', B_60)=B_60 | ~v4_pre_topc(B_60, '#skF_2') | ~m1_subset_1(B_60, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_214])).
% 5.19/1.99  tff(c_235, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_63, c_227])).
% 5.19/1.99  tff(c_239, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_235])).
% 5.19/1.99  tff(c_310, plain, (![B_70, A_71]: (v1_tops_1(B_70, A_71) | k2_pre_topc(A_71, B_70)!=u1_struct_0(A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.19/1.99  tff(c_313, plain, (![B_70]: (v1_tops_1(B_70, '#skF_2') | k2_pre_topc('#skF_2', B_70)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_70, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_310])).
% 5.19/1.99  tff(c_326, plain, (![B_72]: (v1_tops_1(B_72, '#skF_2') | k2_pre_topc('#skF_2', B_72)!='#skF_3' | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_151, c_313])).
% 5.19/1.99  tff(c_334, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_63, c_326])).
% 5.19/1.99  tff(c_338, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_334])).
% 5.19/1.99  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/1.99  tff(c_50, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.19/1.99  tff(c_437, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v1_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.19/1.99  tff(c_440, plain, (![B_83]: (v2_tex_2(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_437])).
% 5.19/1.99  tff(c_450, plain, (![B_83]: (v2_tex_2(B_83, '#skF_2') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_440])).
% 5.19/1.99  tff(c_454, plain, (![B_85]: (v2_tex_2(B_85, '#skF_2') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_450])).
% 5.19/1.99  tff(c_464, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_63, c_454])).
% 5.19/1.99  tff(c_614, plain, (![B_107, A_108]: (v3_tex_2(B_107, A_108) | ~v2_tex_2(B_107, A_108) | ~v1_tops_1(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.19/1.99  tff(c_617, plain, (![B_107]: (v3_tex_2(B_107, '#skF_2') | ~v2_tex_2(B_107, '#skF_2') | ~v1_tops_1(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_614])).
% 5.19/1.99  tff(c_627, plain, (![B_107]: (v3_tex_2(B_107, '#skF_2') | ~v2_tex_2(B_107, '#skF_2') | ~v1_tops_1(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_617])).
% 5.19/1.99  tff(c_631, plain, (![B_109]: (v3_tex_2(B_109, '#skF_2') | ~v2_tex_2(B_109, '#skF_2') | ~v1_tops_1(B_109, '#skF_2') | ~m1_subset_1(B_109, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_627])).
% 5.19/1.99  tff(c_639, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_63, c_631])).
% 5.19/1.99  tff(c_643, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_464, c_639])).
% 5.19/1.99  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_643])).
% 5.19/1.99  tff(c_646, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_96])).
% 5.19/1.99  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_646])).
% 5.19/1.99  tff(c_649, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 5.19/1.99  tff(c_712, plain, (![B_123, A_124]: (v2_tex_2(B_123, A_124) | ~v3_tex_2(B_123, A_124) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.19/1.99  tff(c_728, plain, (![A_125]: (v2_tex_2(u1_struct_0(A_125), A_125) | ~v3_tex_2(u1_struct_0(A_125), A_125) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_63, c_712])).
% 5.19/1.99  tff(c_731, plain, (v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_662, c_728])).
% 5.19/1.99  tff(c_733, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_662, c_731])).
% 5.19/1.99  tff(c_734, plain, (~v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_733])).
% 5.19/1.99  tff(c_775, plain, (![A_130, B_131]: (k2_pre_topc(A_130, B_131)=B_131 | ~v4_pre_topc(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.19/1.99  tff(c_791, plain, (![A_132]: (k2_pre_topc(A_132, u1_struct_0(A_132))=u1_struct_0(A_132) | ~v4_pre_topc(u1_struct_0(A_132), A_132) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_63, c_775])).
% 5.19/1.99  tff(c_794, plain, (k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_662, c_791])).
% 5.19/1.99  tff(c_796, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_662, c_662, c_794])).
% 5.19/1.99  tff(c_797, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_796])).
% 5.19/1.99  tff(c_800, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_797])).
% 5.19/1.99  tff(c_804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_800])).
% 5.19/1.99  tff(c_805, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_796])).
% 5.19/1.99  tff(c_829, plain, (![B_134, A_135]: (v1_tops_1(B_134, A_135) | k2_pre_topc(A_135, B_134)!=u1_struct_0(A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.19/1.99  tff(c_857, plain, (![A_137]: (v1_tops_1(u1_struct_0(A_137), A_137) | k2_pre_topc(A_137, u1_struct_0(A_137))!=u1_struct_0(A_137) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_63, c_829])).
% 5.19/1.99  tff(c_860, plain, (v1_tops_1(k2_struct_0('#skF_2'), '#skF_2') | k2_pre_topc('#skF_2', u1_struct_0('#skF_2'))!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_662, c_857])).
% 5.19/1.99  tff(c_862, plain, (v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_805, c_662, c_662, c_860])).
% 5.19/1.99  tff(c_1032, plain, (![B_155, A_156]: (v2_tex_2(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v1_tdlat_3(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.19/1.99  tff(c_1035, plain, (![B_155]: (v2_tex_2(B_155, '#skF_2') | ~m1_subset_1(B_155, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_1032])).
% 5.19/1.99  tff(c_1045, plain, (![B_155]: (v2_tex_2(B_155, '#skF_2') | ~m1_subset_1(B_155, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1035])).
% 5.19/1.99  tff(c_1049, plain, (![B_157]: (v2_tex_2(B_157, '#skF_2') | ~m1_subset_1(B_157, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1045])).
% 5.19/1.99  tff(c_1064, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_63, c_1049])).
% 5.19/1.99  tff(c_1297, plain, (![B_186, A_187]: (v3_tex_2(B_186, A_187) | ~v2_tex_2(B_186, A_187) | ~v1_tops_1(B_186, A_187) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.19/1.99  tff(c_1300, plain, (![B_186]: (v3_tex_2(B_186, '#skF_2') | ~v2_tex_2(B_186, '#skF_2') | ~v1_tops_1(B_186, '#skF_2') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_1297])).
% 5.19/1.99  tff(c_1310, plain, (![B_186]: (v3_tex_2(B_186, '#skF_2') | ~v2_tex_2(B_186, '#skF_2') | ~v1_tops_1(B_186, '#skF_2') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1300])).
% 5.19/1.99  tff(c_1314, plain, (![B_188]: (v3_tex_2(B_188, '#skF_2') | ~v2_tex_2(B_188, '#skF_2') | ~v1_tops_1(B_188, '#skF_2') | ~m1_subset_1(B_188, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1310])).
% 5.19/1.99  tff(c_1325, plain, (v3_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_63, c_1314])).
% 5.19/1.99  tff(c_1332, plain, (v3_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_1064, c_1325])).
% 5.19/1.99  tff(c_1334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_734, c_1332])).
% 5.19/1.99  tff(c_1335, plain, (v2_tex_2(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_733])).
% 5.19/1.99  tff(c_1337, plain, (![A_189, B_190]: (k2_pre_topc(A_189, B_190)=B_190 | ~v4_pre_topc(B_190, A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.19/1.99  tff(c_1340, plain, (![B_190]: (k2_pre_topc('#skF_2', B_190)=B_190 | ~v4_pre_topc(B_190, '#skF_2') | ~m1_subset_1(B_190, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_1337])).
% 5.19/1.99  tff(c_1372, plain, (![B_192]: (k2_pre_topc('#skF_2', B_192)=B_192 | ~v4_pre_topc(B_192, '#skF_2') | ~m1_subset_1(B_192, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1340])).
% 5.19/1.99  tff(c_1384, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_664, c_1372])).
% 5.19/1.99  tff(c_1387, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1384])).
% 5.19/1.99  tff(c_1398, plain, (![B_193, A_194]: (v1_tops_1(B_193, A_194) | k2_pre_topc(A_194, B_193)!=u1_struct_0(A_194) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.19/1.99  tff(c_1401, plain, (![B_193]: (v1_tops_1(B_193, '#skF_2') | k2_pre_topc('#skF_2', B_193)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_193, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_1398])).
% 5.19/1.99  tff(c_1444, plain, (![B_197]: (v1_tops_1(B_197, '#skF_2') | k2_pre_topc('#skF_2', B_197)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_197, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_662, c_1401])).
% 5.19/1.99  tff(c_1456, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_664, c_1444])).
% 5.19/1.99  tff(c_1461, plain, (k2_pre_topc('#skF_2', '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1456])).
% 5.19/1.99  tff(c_1479, plain, (![A_201, B_202]: (k2_pre_topc(A_201, B_202)=u1_struct_0(A_201) | ~v1_tops_1(B_202, A_201) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.19/1.99  tff(c_1482, plain, (![B_202]: (k2_pre_topc('#skF_2', B_202)=u1_struct_0('#skF_2') | ~v1_tops_1(B_202, '#skF_2') | ~m1_subset_1(B_202, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_1479])).
% 5.19/1.99  tff(c_1523, plain, (![B_206]: (k2_pre_topc('#skF_2', B_206)=k2_struct_0('#skF_2') | ~v1_tops_1(B_206, '#skF_2') | ~m1_subset_1(B_206, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_662, c_1482])).
% 5.19/1.99  tff(c_1526, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_664, c_1523])).
% 5.19/1.99  tff(c_1537, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1461, c_1526])).
% 5.19/1.99  tff(c_671, plain, (![A_115, B_116]: (r1_tarski(A_115, B_116) | ~m1_subset_1(A_115, k1_zfmisc_1(B_116)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.19/1.99  tff(c_681, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_664, c_671])).
% 5.19/1.99  tff(c_2159, plain, (![C_264, B_265, A_266]: (C_264=B_265 | ~r1_tarski(B_265, C_264) | ~v2_tex_2(C_264, A_266) | ~m1_subset_1(C_264, k1_zfmisc_1(u1_struct_0(A_266))) | ~v3_tex_2(B_265, A_266) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.19/1.99  tff(c_2173, plain, (![A_266]: (k2_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(k2_struct_0('#skF_2'), A_266) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_266))) | ~v3_tex_2('#skF_3', A_266) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(resolution, [status(thm)], [c_681, c_2159])).
% 5.19/1.99  tff(c_2207, plain, (![A_271]: (~v2_tex_2(k2_struct_0('#skF_2'), A_271) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_271))) | ~v3_tex_2('#skF_3', A_271) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(splitLeft, [status(thm)], [c_2173])).
% 5.19/1.99  tff(c_2210, plain, (~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_662, c_2207])).
% 5.19/1.99  tff(c_2216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_664, c_662, c_649, c_63, c_1335, c_2210])).
% 5.19/1.99  tff(c_2217, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2173])).
% 5.19/1.99  tff(c_1386, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2') | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_63, c_1372])).
% 5.19/1.99  tff(c_1388, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1386])).
% 5.19/1.99  tff(c_1391, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_1388])).
% 5.19/1.99  tff(c_1395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1391])).
% 5.19/1.99  tff(c_1396, plain, (k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1386])).
% 5.19/1.99  tff(c_1455, plain, (v1_tops_1(k2_struct_0('#skF_2'), '#skF_2') | k2_pre_topc('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_63, c_1444])).
% 5.19/1.99  tff(c_1460, plain, (v1_tops_1(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_1455])).
% 5.19/1.99  tff(c_2242, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2217, c_1460])).
% 5.19/1.99  tff(c_2255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1537, c_2242])).
% 5.19/1.99  tff(c_2257, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1456])).
% 5.19/1.99  tff(c_2408, plain, (![B_291, A_292]: (v4_pre_topc(B_291, A_292) | k2_pre_topc(A_292, B_291)!=B_291 | ~v2_pre_topc(A_292) | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.19/1.99  tff(c_2411, plain, (![B_291]: (v4_pre_topc(B_291, '#skF_2') | k2_pre_topc('#skF_2', B_291)!=B_291 | ~v2_pre_topc('#skF_2') | ~m1_subset_1(B_291, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_2408])).
% 5.19/1.99  tff(c_2460, plain, (![B_296]: (v4_pre_topc(B_296, '#skF_2') | k2_pre_topc('#skF_2', B_296)!=B_296 | ~m1_subset_1(B_296, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_2411])).
% 5.19/1.99  tff(c_2463, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_664, c_2460])).
% 5.19/1.99  tff(c_2473, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_2463])).
% 5.19/1.99  tff(c_2474, plain, (k2_struct_0('#skF_2')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1387, c_2473])).
% 5.19/1.99  tff(c_2963, plain, (![C_339, B_340, A_341]: (C_339=B_340 | ~r1_tarski(B_340, C_339) | ~v2_tex_2(C_339, A_341) | ~m1_subset_1(C_339, k1_zfmisc_1(u1_struct_0(A_341))) | ~v3_tex_2(B_340, A_341) | ~m1_subset_1(B_340, k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.19/1.99  tff(c_2971, plain, (![A_341]: (k2_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(k2_struct_0('#skF_2'), A_341) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_341))) | ~v3_tex_2('#skF_3', A_341) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341))), inference(resolution, [status(thm)], [c_681, c_2963])).
% 5.19/1.99  tff(c_2982, plain, (![A_342]: (~v2_tex_2(k2_struct_0('#skF_2'), A_342) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_342))) | ~v3_tex_2('#skF_3', A_342) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_342))) | ~l1_pre_topc(A_342))), inference(negUnitSimplification, [status(thm)], [c_2474, c_2971])).
% 5.19/1.99  tff(c_2985, plain, (~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_662, c_2982])).
% 5.19/1.99  tff(c_2991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_664, c_662, c_649, c_63, c_1335, c_2985])).
% 5.19/1.99  tff(c_2992, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1384])).
% 5.19/1.99  tff(c_2994, plain, (![B_343, A_344]: (v1_tops_1(B_343, A_344) | k2_pre_topc(A_344, B_343)!=u1_struct_0(A_344) | ~m1_subset_1(B_343, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.19/1.99  tff(c_2997, plain, (![B_343]: (v1_tops_1(B_343, '#skF_2') | k2_pre_topc('#skF_2', B_343)!=u1_struct_0('#skF_2') | ~m1_subset_1(B_343, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_2994])).
% 5.19/1.99  tff(c_3024, plain, (![B_345]: (v1_tops_1(B_345, '#skF_2') | k2_pre_topc('#skF_2', B_345)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_345, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_662, c_2997])).
% 5.19/1.99  tff(c_3027, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_664, c_3024])).
% 5.19/1.99  tff(c_3037, plain, (v1_tops_1('#skF_3', '#skF_2') | k2_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2992, c_3027])).
% 5.19/1.99  tff(c_3044, plain, (k2_struct_0('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_3037])).
% 5.19/1.99  tff(c_3752, plain, (![C_412, B_413, A_414]: (C_412=B_413 | ~r1_tarski(B_413, C_412) | ~v2_tex_2(C_412, A_414) | ~m1_subset_1(C_412, k1_zfmisc_1(u1_struct_0(A_414))) | ~v3_tex_2(B_413, A_414) | ~m1_subset_1(B_413, k1_zfmisc_1(u1_struct_0(A_414))) | ~l1_pre_topc(A_414))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.19/1.99  tff(c_3760, plain, (![A_414]: (k2_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(k2_struct_0('#skF_2'), A_414) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_414))) | ~v3_tex_2('#skF_3', A_414) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_414))) | ~l1_pre_topc(A_414))), inference(resolution, [status(thm)], [c_681, c_3752])).
% 5.19/1.99  tff(c_3771, plain, (![A_415]: (~v2_tex_2(k2_struct_0('#skF_2'), A_415) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_415))) | ~v3_tex_2('#skF_3', A_415) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_415))) | ~l1_pre_topc(A_415))), inference(negUnitSimplification, [status(thm)], [c_3044, c_3760])).
% 5.19/1.99  tff(c_3774, plain, (~v2_tex_2(k2_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_662, c_3771])).
% 5.19/1.99  tff(c_3780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_664, c_662, c_649, c_63, c_1335, c_3774])).
% 5.19/1.99  tff(c_3782, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_3037])).
% 5.19/1.99  tff(c_650, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_62])).
% 5.19/1.99  tff(c_663, plain, (v1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_650])).
% 5.19/1.99  tff(c_3792, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3782, c_663])).
% 5.19/1.99  tff(c_3801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_3792])).
% 5.19/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.99  
% 5.19/1.99  Inference rules
% 5.19/1.99  ----------------------
% 5.19/1.99  #Ref     : 0
% 5.19/1.99  #Sup     : 685
% 5.19/1.99  #Fact    : 0
% 5.19/1.99  #Define  : 0
% 5.19/1.99  #Split   : 12
% 5.19/1.99  #Chain   : 0
% 5.19/1.99  #Close   : 0
% 5.19/1.99  
% 5.19/1.99  Ordering : KBO
% 5.19/1.99  
% 5.19/1.99  Simplification rules
% 5.19/1.99  ----------------------
% 5.19/1.99  #Subsume      : 144
% 5.19/1.99  #Demod        : 804
% 5.19/1.99  #Tautology    : 215
% 5.19/1.99  #SimpNegUnit  : 61
% 5.19/1.99  #BackRed      : 54
% 5.19/1.99  
% 5.19/1.99  #Partial instantiations: 0
% 5.19/1.99  #Strategies tried      : 1
% 5.19/1.99  
% 5.19/1.99  Timing (in seconds)
% 5.19/1.99  ----------------------
% 5.19/2.00  Preprocessing        : 0.33
% 5.19/2.00  Parsing              : 0.18
% 5.19/2.00  CNF conversion       : 0.02
% 5.19/2.00  Main loop            : 0.85
% 5.19/2.00  Inferencing          : 0.32
% 5.19/2.00  Reduction            : 0.26
% 5.19/2.00  Demodulation         : 0.18
% 5.19/2.00  BG Simplification    : 0.03
% 5.19/2.00  Subsumption          : 0.17
% 5.19/2.00  Abstraction          : 0.04
% 5.19/2.00  MUC search           : 0.00
% 5.19/2.00  Cooper               : 0.00
% 5.19/2.00  Total                : 1.24
% 5.19/2.00  Index Insertion      : 0.00
% 5.19/2.00  Index Deletion       : 0.00
% 5.19/2.00  Index Matching       : 0.00
% 5.19/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
