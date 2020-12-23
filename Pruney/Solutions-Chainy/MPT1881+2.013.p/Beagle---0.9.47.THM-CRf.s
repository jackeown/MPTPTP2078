%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:07 EST 2020

% Result     : Theorem 7.00s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 627 expanded)
%              Number of leaves         :   38 ( 229 expanded)
%              Depth                    :   13
%              Number of atoms          :  287 (1573 expanded)
%              Number of equality atoms :   36 ( 232 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_146,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_128,axiom,(
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

tff(f_98,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_12] : ~ v1_subset_1(k2_subset_1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_461,plain,(
    ! [A_122] :
      ( u1_struct_0(A_122) = k2_struct_0(A_122)
      | ~ l1_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_466,plain,(
    ! [A_123] :
      ( u1_struct_0(A_123) = k2_struct_0(A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_18,c_461])).

tff(c_470,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_466])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_472,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_48])).

tff(c_58,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_79,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_81,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_86,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_18,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_64,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_96,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64])).

tff(c_97,plain,(
    ~ v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_96])).

tff(c_91,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_48])).

tff(c_115,plain,(
    ! [B_52,A_53] :
      ( v1_subset_1(B_52,A_53)
      | B_52 = A_53
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_118,plain,
    ( v1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_91,c_115])).

tff(c_124,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_118])).

tff(c_20,plain,(
    ! [A_15] :
      ( k2_pre_topc(A_15,k2_struct_0(A_15)) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = k2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_20])).

tff(c_140,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_124,c_136])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_131,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_90])).

tff(c_215,plain,(
    ! [B_76,A_77] :
      ( v1_tops_1(B_76,A_77)
      | k2_pre_topc(A_77,B_76) != u1_struct_0(A_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_218,plain,(
    ! [B_76] :
      ( v1_tops_1(B_76,'#skF_3')
      | k2_pre_topc('#skF_3',B_76) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_215])).

tff(c_237,plain,(
    ! [B_80] :
      ( v1_tops_1(B_80,'#skF_3')
      | k2_pre_topc('#skF_3',B_80) != '#skF_4'
      | ~ m1_subset_1(B_80,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_131,c_218])).

tff(c_241,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_237])).

tff(c_244,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_241])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_253,plain,(
    ! [B_82,A_83] :
      ( v2_tex_2(B_82,A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v1_tdlat_3(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_256,plain,(
    ! [B_82] :
      ( v2_tex_2(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_253])).

tff(c_262,plain,(
    ! [B_82] :
      ( v2_tex_2(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_256])).

tff(c_265,plain,(
    ! [B_84] :
      ( v2_tex_2(B_84,'#skF_3')
      | ~ m1_subset_1(B_84,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_262])).

tff(c_270,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_265])).

tff(c_434,plain,(
    ! [B_118,A_119] :
      ( v3_tex_2(B_118,A_119)
      | ~ v2_tex_2(B_118,A_119)
      | ~ v1_tops_1(B_118,A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_437,plain,(
    ! [B_118] :
      ( v3_tex_2(B_118,'#skF_3')
      | ~ v2_tex_2(B_118,'#skF_3')
      | ~ v1_tops_1(B_118,'#skF_3')
      | ~ m1_subset_1(B_118,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_434])).

tff(c_443,plain,(
    ! [B_118] :
      ( v3_tex_2(B_118,'#skF_3')
      | ~ v2_tex_2(B_118,'#skF_3')
      | ~ v1_tops_1(B_118,'#skF_3')
      | ~ m1_subset_1(B_118,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_437])).

tff(c_446,plain,(
    ! [B_120] :
      ( v3_tex_2(B_120,'#skF_3')
      | ~ v2_tex_2(B_120,'#skF_3')
      | ~ v1_tops_1(B_120,'#skF_3')
      | ~ m1_subset_1(B_120,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_443])).

tff(c_450,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_446])).

tff(c_453,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_270,c_450])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_453])).

tff(c_457,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_539,plain,(
    ! [B_144,A_145] :
      ( v2_tex_2(B_144,A_145)
      | ~ v3_tex_2(B_144,A_145)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_560,plain,(
    ! [A_148] :
      ( v2_tex_2(u1_struct_0(A_148),A_148)
      | ~ v3_tex_2(u1_struct_0(A_148),A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_66,c_539])).

tff(c_563,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_560])).

tff(c_565,plain,
    ( v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_470,c_563])).

tff(c_566,plain,(
    ~ v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_598,plain,(
    ! [A_156,B_157] :
      ( k2_pre_topc(A_156,B_157) = u1_struct_0(A_156)
      | ~ v1_tops_1(B_157,A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_613,plain,(
    ! [A_159] :
      ( k2_pre_topc(A_159,u1_struct_0(A_159)) = u1_struct_0(A_159)
      | ~ v1_tops_1(u1_struct_0(A_159),A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_66,c_598])).

tff(c_616,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_613])).

tff(c_618,plain,
    ( k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_470,c_470,c_616])).

tff(c_619,plain,(
    ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_631,plain,(
    ! [B_161,A_162] :
      ( v1_tops_1(B_161,A_162)
      | k2_pre_topc(A_162,B_161) != u1_struct_0(A_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_634,plain,(
    ! [B_161] :
      ( v1_tops_1(B_161,'#skF_3')
      | k2_pre_topc('#skF_3',B_161) != u1_struct_0('#skF_3')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_631])).

tff(c_672,plain,(
    ! [B_167] :
      ( v1_tops_1(B_167,'#skF_3')
      | k2_pre_topc('#skF_3',B_167) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_470,c_634])).

tff(c_679,plain,
    ( v1_tops_1(k2_struct_0('#skF_3'),'#skF_3')
    | k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_672])).

tff(c_685,plain,(
    k2_pre_topc('#skF_3',k2_struct_0('#skF_3')) != k2_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_679])).

tff(c_688,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_685])).

tff(c_692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_688])).

tff(c_694,plain,(
    v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_795,plain,(
    ! [B_184,A_185] :
      ( v2_tex_2(B_184,A_185)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185)
      | ~ v1_tdlat_3(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_798,plain,(
    ! [B_184] :
      ( v2_tex_2(B_184,'#skF_3')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_795])).

tff(c_804,plain,(
    ! [B_184] :
      ( v2_tex_2(B_184,'#skF_3')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_798])).

tff(c_807,plain,(
    ! [B_186] :
      ( v2_tex_2(B_186,'#skF_3')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_804])).

tff(c_817,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_807])).

tff(c_1558,plain,(
    ! [B_266,A_267] :
      ( v3_tex_2(B_266,A_267)
      | ~ v2_tex_2(B_266,A_267)
      | ~ v1_tops_1(B_266,A_267)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1564,plain,(
    ! [B_266] :
      ( v3_tex_2(B_266,'#skF_3')
      | ~ v2_tex_2(B_266,'#skF_3')
      | ~ v1_tops_1(B_266,'#skF_3')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_1558])).

tff(c_1571,plain,(
    ! [B_266] :
      ( v3_tex_2(B_266,'#skF_3')
      | ~ v2_tex_2(B_266,'#skF_3')
      | ~ v1_tops_1(B_266,'#skF_3')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1564])).

tff(c_1649,plain,(
    ! [B_272] :
      ( v3_tex_2(B_272,'#skF_3')
      | ~ v2_tex_2(B_272,'#skF_3')
      | ~ v1_tops_1(B_272,'#skF_3')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1571])).

tff(c_1659,plain,
    ( v3_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tops_1(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1649])).

tff(c_1666,plain,(
    v3_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_817,c_1659])).

tff(c_1668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_1666])).

tff(c_1669,plain,(
    v2_tex_2(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_511,plain,(
    ! [C_135,A_136,B_137] :
      ( r2_hidden(C_135,A_136)
      | ~ r2_hidden(C_135,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_527,plain,(
    ! [A_141,B_142,A_143] :
      ( r2_hidden('#skF_1'(A_141,B_142),A_143)
      | ~ m1_subset_1(A_141,k1_zfmisc_1(A_143))
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_6,c_511])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_550,plain,(
    ! [A_146,A_147] :
      ( ~ m1_subset_1(A_146,k1_zfmisc_1(A_147))
      | r1_tarski(A_146,A_147) ) ),
    inference(resolution,[status(thm)],[c_527,c_4])).

tff(c_557,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_472,c_550])).

tff(c_5367,plain,(
    ! [C_738,B_739,A_740] :
      ( C_738 = B_739
      | ~ r1_tarski(B_739,C_738)
      | ~ v2_tex_2(C_738,A_740)
      | ~ m1_subset_1(C_738,k1_zfmisc_1(u1_struct_0(A_740)))
      | ~ v3_tex_2(B_739,A_740)
      | ~ m1_subset_1(B_739,k1_zfmisc_1(u1_struct_0(A_740)))
      | ~ l1_pre_topc(A_740) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5393,plain,(
    ! [A_740] :
      ( k2_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(k2_struct_0('#skF_3'),A_740)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_740)))
      | ~ v3_tex_2('#skF_4',A_740)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_740)))
      | ~ l1_pre_topc(A_740) ) ),
    inference(resolution,[status(thm)],[c_557,c_5367])).

tff(c_5645,plain,(
    ! [A_773] :
      ( ~ v2_tex_2(k2_struct_0('#skF_3'),A_773)
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_773)))
      | ~ v3_tex_2('#skF_4',A_773)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_773)))
      | ~ l1_pre_topc(A_773) ) ),
    inference(splitLeft,[status(thm)],[c_5393])).

tff(c_5648,plain,
    ( ~ v2_tex_2(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_5645])).

tff(c_5651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_472,c_470,c_457,c_66,c_1669,c_5648])).

tff(c_5652,plain,(
    k2_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5393])).

tff(c_456,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_471,plain,(
    v1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_456])).

tff(c_5711,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5652,c_471])).

tff(c_5720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_5711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.00/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.57  
% 7.00/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.00/2.57  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.00/2.57  
% 7.00/2.57  %Foreground sorts:
% 7.00/2.57  
% 7.00/2.57  
% 7.00/2.57  %Background operators:
% 7.00/2.57  
% 7.00/2.57  
% 7.00/2.57  %Foreground operators:
% 7.00/2.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.00/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.00/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.00/2.57  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.00/2.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.00/2.57  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.00/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.00/2.57  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 7.00/2.57  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.00/2.57  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.00/2.57  tff('#skF_3', type, '#skF_3': $i).
% 7.00/2.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.00/2.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.00/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.00/2.57  tff('#skF_4', type, '#skF_4': $i).
% 7.00/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.00/2.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.00/2.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.00/2.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.00/2.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.00/2.57  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.00/2.57  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.00/2.57  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.00/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.00/2.57  
% 7.37/2.59  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.37/2.59  tff(f_46, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 7.37/2.59  tff(f_146, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 7.37/2.59  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.37/2.59  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.37/2.59  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 7.37/2.59  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 7.37/2.59  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.37/2.59  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 7.37/2.59  tff(f_112, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 7.37/2.59  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 7.37/2.59  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 7.37/2.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.37/2.59  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.37/2.59  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.37/2.59  tff(c_14, plain, (![A_12]: (~v1_subset_1(k2_subset_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.37/2.59  tff(c_65, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 7.37/2.59  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.37/2.59  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.37/2.59  tff(c_461, plain, (![A_122]: (u1_struct_0(A_122)=k2_struct_0(A_122) | ~l1_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.37/2.59  tff(c_466, plain, (![A_123]: (u1_struct_0(A_123)=k2_struct_0(A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_18, c_461])).
% 7.37/2.59  tff(c_470, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_466])).
% 7.37/2.59  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.37/2.59  tff(c_472, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_48])).
% 7.37/2.59  tff(c_58, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.37/2.59  tff(c_79, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 7.37/2.59  tff(c_81, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.37/2.59  tff(c_86, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_18, c_81])).
% 7.37/2.59  tff(c_90, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_86])).
% 7.37/2.59  tff(c_64, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.37/2.59  tff(c_96, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64])).
% 7.37/2.59  tff(c_97, plain, (~v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_79, c_96])).
% 7.37/2.59  tff(c_91, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_48])).
% 7.37/2.59  tff(c_115, plain, (![B_52, A_53]: (v1_subset_1(B_52, A_53) | B_52=A_53 | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.37/2.59  tff(c_118, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_91, c_115])).
% 7.37/2.59  tff(c_124, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_97, c_118])).
% 7.37/2.59  tff(c_20, plain, (![A_15]: (k2_pre_topc(A_15, k2_struct_0(A_15))=k2_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.37/2.59  tff(c_136, plain, (k2_pre_topc('#skF_3', '#skF_4')=k2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_20])).
% 7.37/2.59  tff(c_140, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_124, c_136])).
% 7.37/2.59  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.37/2.59  tff(c_66, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 7.37/2.59  tff(c_131, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_90])).
% 7.37/2.59  tff(c_215, plain, (![B_76, A_77]: (v1_tops_1(B_76, A_77) | k2_pre_topc(A_77, B_76)!=u1_struct_0(A_77) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.37/2.59  tff(c_218, plain, (![B_76]: (v1_tops_1(B_76, '#skF_3') | k2_pre_topc('#skF_3', B_76)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_215])).
% 7.37/2.59  tff(c_237, plain, (![B_80]: (v1_tops_1(B_80, '#skF_3') | k2_pre_topc('#skF_3', B_80)!='#skF_4' | ~m1_subset_1(B_80, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_131, c_218])).
% 7.37/2.59  tff(c_241, plain, (v1_tops_1('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_66, c_237])).
% 7.37/2.59  tff(c_244, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_241])).
% 7.37/2.59  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.37/2.59  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.37/2.59  tff(c_52, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.37/2.59  tff(c_253, plain, (![B_82, A_83]: (v2_tex_2(B_82, A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v1_tdlat_3(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.37/2.59  tff(c_256, plain, (![B_82]: (v2_tex_2(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_253])).
% 7.37/2.59  tff(c_262, plain, (![B_82]: (v2_tex_2(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_256])).
% 7.37/2.59  tff(c_265, plain, (![B_84]: (v2_tex_2(B_84, '#skF_3') | ~m1_subset_1(B_84, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_262])).
% 7.37/2.59  tff(c_270, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_265])).
% 7.37/2.59  tff(c_434, plain, (![B_118, A_119]: (v3_tex_2(B_118, A_119) | ~v2_tex_2(B_118, A_119) | ~v1_tops_1(B_118, A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.37/2.59  tff(c_437, plain, (![B_118]: (v3_tex_2(B_118, '#skF_3') | ~v2_tex_2(B_118, '#skF_3') | ~v1_tops_1(B_118, '#skF_3') | ~m1_subset_1(B_118, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_434])).
% 7.37/2.59  tff(c_443, plain, (![B_118]: (v3_tex_2(B_118, '#skF_3') | ~v2_tex_2(B_118, '#skF_3') | ~v1_tops_1(B_118, '#skF_3') | ~m1_subset_1(B_118, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_437])).
% 7.37/2.59  tff(c_446, plain, (![B_120]: (v3_tex_2(B_120, '#skF_3') | ~v2_tex_2(B_120, '#skF_3') | ~v1_tops_1(B_120, '#skF_3') | ~m1_subset_1(B_120, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_443])).
% 7.37/2.59  tff(c_450, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_446])).
% 7.37/2.59  tff(c_453, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_270, c_450])).
% 7.37/2.59  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_453])).
% 7.37/2.59  tff(c_457, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 7.37/2.59  tff(c_539, plain, (![B_144, A_145]: (v2_tex_2(B_144, A_145) | ~v3_tex_2(B_144, A_145) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.37/2.59  tff(c_560, plain, (![A_148]: (v2_tex_2(u1_struct_0(A_148), A_148) | ~v3_tex_2(u1_struct_0(A_148), A_148) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_66, c_539])).
% 7.37/2.59  tff(c_563, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_470, c_560])).
% 7.37/2.59  tff(c_565, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_470, c_563])).
% 7.37/2.59  tff(c_566, plain, (~v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_565])).
% 7.37/2.59  tff(c_598, plain, (![A_156, B_157]: (k2_pre_topc(A_156, B_157)=u1_struct_0(A_156) | ~v1_tops_1(B_157, A_156) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.37/2.59  tff(c_613, plain, (![A_159]: (k2_pre_topc(A_159, u1_struct_0(A_159))=u1_struct_0(A_159) | ~v1_tops_1(u1_struct_0(A_159), A_159) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_66, c_598])).
% 7.37/2.59  tff(c_616, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_470, c_613])).
% 7.37/2.59  tff(c_618, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_470, c_470, c_616])).
% 7.37/2.59  tff(c_619, plain, (~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_618])).
% 7.37/2.59  tff(c_631, plain, (![B_161, A_162]: (v1_tops_1(B_161, A_162) | k2_pre_topc(A_162, B_161)!=u1_struct_0(A_162) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.37/2.59  tff(c_634, plain, (![B_161]: (v1_tops_1(B_161, '#skF_3') | k2_pre_topc('#skF_3', B_161)!=u1_struct_0('#skF_3') | ~m1_subset_1(B_161, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_470, c_631])).
% 7.37/2.59  tff(c_672, plain, (![B_167]: (v1_tops_1(B_167, '#skF_3') | k2_pre_topc('#skF_3', B_167)!=k2_struct_0('#skF_3') | ~m1_subset_1(B_167, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_470, c_634])).
% 7.37/2.59  tff(c_679, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3') | k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_672])).
% 7.37/2.59  tff(c_685, plain, (k2_pre_topc('#skF_3', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_619, c_679])).
% 7.37/2.59  tff(c_688, plain, (~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_685])).
% 7.37/2.59  tff(c_692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_688])).
% 7.37/2.59  tff(c_694, plain, (v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_618])).
% 7.37/2.59  tff(c_795, plain, (![B_184, A_185]: (v2_tex_2(B_184, A_185) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185) | ~v1_tdlat_3(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.37/2.59  tff(c_798, plain, (![B_184]: (v2_tex_2(B_184, '#skF_3') | ~m1_subset_1(B_184, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_470, c_795])).
% 7.37/2.59  tff(c_804, plain, (![B_184]: (v2_tex_2(B_184, '#skF_3') | ~m1_subset_1(B_184, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_798])).
% 7.37/2.59  tff(c_807, plain, (![B_186]: (v2_tex_2(B_186, '#skF_3') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_804])).
% 7.37/2.59  tff(c_817, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_66, c_807])).
% 7.37/2.59  tff(c_1558, plain, (![B_266, A_267]: (v3_tex_2(B_266, A_267) | ~v2_tex_2(B_266, A_267) | ~v1_tops_1(B_266, A_267) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.37/2.59  tff(c_1564, plain, (![B_266]: (v3_tex_2(B_266, '#skF_3') | ~v2_tex_2(B_266, '#skF_3') | ~v1_tops_1(B_266, '#skF_3') | ~m1_subset_1(B_266, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_470, c_1558])).
% 7.37/2.59  tff(c_1571, plain, (![B_266]: (v3_tex_2(B_266, '#skF_3') | ~v2_tex_2(B_266, '#skF_3') | ~v1_tops_1(B_266, '#skF_3') | ~m1_subset_1(B_266, k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1564])).
% 7.37/2.59  tff(c_1649, plain, (![B_272]: (v3_tex_2(B_272, '#skF_3') | ~v2_tex_2(B_272, '#skF_3') | ~v1_tops_1(B_272, '#skF_3') | ~m1_subset_1(B_272, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_1571])).
% 7.37/2.59  tff(c_1659, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~v1_tops_1(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_66, c_1649])).
% 7.37/2.59  tff(c_1666, plain, (v3_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_694, c_817, c_1659])).
% 7.37/2.59  tff(c_1668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_566, c_1666])).
% 7.37/2.59  tff(c_1669, plain, (v2_tex_2(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_565])).
% 7.37/2.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.37/2.59  tff(c_511, plain, (![C_135, A_136, B_137]: (r2_hidden(C_135, A_136) | ~r2_hidden(C_135, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.37/2.59  tff(c_527, plain, (![A_141, B_142, A_143]: (r2_hidden('#skF_1'(A_141, B_142), A_143) | ~m1_subset_1(A_141, k1_zfmisc_1(A_143)) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_6, c_511])).
% 7.37/2.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.37/2.59  tff(c_550, plain, (![A_146, A_147]: (~m1_subset_1(A_146, k1_zfmisc_1(A_147)) | r1_tarski(A_146, A_147))), inference(resolution, [status(thm)], [c_527, c_4])).
% 7.37/2.59  tff(c_557, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_472, c_550])).
% 7.37/2.59  tff(c_5367, plain, (![C_738, B_739, A_740]: (C_738=B_739 | ~r1_tarski(B_739, C_738) | ~v2_tex_2(C_738, A_740) | ~m1_subset_1(C_738, k1_zfmisc_1(u1_struct_0(A_740))) | ~v3_tex_2(B_739, A_740) | ~m1_subset_1(B_739, k1_zfmisc_1(u1_struct_0(A_740))) | ~l1_pre_topc(A_740))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.37/2.59  tff(c_5393, plain, (![A_740]: (k2_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(k2_struct_0('#skF_3'), A_740) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_740))) | ~v3_tex_2('#skF_4', A_740) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_740))) | ~l1_pre_topc(A_740))), inference(resolution, [status(thm)], [c_557, c_5367])).
% 7.37/2.59  tff(c_5645, plain, (![A_773]: (~v2_tex_2(k2_struct_0('#skF_3'), A_773) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_773))) | ~v3_tex_2('#skF_4', A_773) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_773))) | ~l1_pre_topc(A_773))), inference(splitLeft, [status(thm)], [c_5393])).
% 7.37/2.59  tff(c_5648, plain, (~v2_tex_2(k2_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_470, c_5645])).
% 7.37/2.59  tff(c_5651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_472, c_470, c_457, c_66, c_1669, c_5648])).
% 7.37/2.59  tff(c_5652, plain, (k2_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_5393])).
% 7.37/2.59  tff(c_456, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 7.37/2.59  tff(c_471, plain, (v1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_456])).
% 7.37/2.59  tff(c_5711, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5652, c_471])).
% 7.37/2.59  tff(c_5720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_5711])).
% 7.37/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.37/2.59  
% 7.37/2.59  Inference rules
% 7.37/2.59  ----------------------
% 7.37/2.59  #Ref     : 0
% 7.37/2.59  #Sup     : 1255
% 7.37/2.59  #Fact    : 0
% 7.37/2.59  #Define  : 0
% 7.37/2.59  #Split   : 18
% 7.37/2.59  #Chain   : 0
% 7.37/2.59  #Close   : 0
% 7.37/2.59  
% 7.37/2.59  Ordering : KBO
% 7.37/2.59  
% 7.37/2.59  Simplification rules
% 7.37/2.59  ----------------------
% 7.37/2.59  #Subsume      : 533
% 7.37/2.59  #Demod        : 921
% 7.37/2.59  #Tautology    : 218
% 7.37/2.59  #SimpNegUnit  : 54
% 7.37/2.59  #BackRed      : 208
% 7.37/2.59  
% 7.37/2.59  #Partial instantiations: 0
% 7.37/2.59  #Strategies tried      : 1
% 7.37/2.59  
% 7.37/2.59  Timing (in seconds)
% 7.37/2.59  ----------------------
% 7.37/2.59  Preprocessing        : 0.36
% 7.37/2.59  Parsing              : 0.20
% 7.37/2.59  CNF conversion       : 0.02
% 7.37/2.59  Main loop            : 1.43
% 7.37/2.59  Inferencing          : 0.42
% 7.37/2.59  Reduction            : 0.40
% 7.37/2.59  Demodulation         : 0.26
% 7.37/2.59  BG Simplification    : 0.04
% 7.37/2.59  Subsumption          : 0.47
% 7.37/2.59  Abstraction          : 0.06
% 7.37/2.59  MUC search           : 0.00
% 7.37/2.59  Cooper               : 0.00
% 7.37/2.59  Total                : 1.84
% 7.37/2.59  Index Insertion      : 0.00
% 7.37/2.59  Index Deletion       : 0.00
% 7.37/2.59  Index Matching       : 0.00
% 7.37/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
