%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:56 EST 2020

% Result     : Theorem 40.74s
% Output     : CNFRefutation 40.99s
% Verified   : 
% Statistics : Number of formulae       :  165 (3905 expanded)
%              Number of leaves         :   35 (1308 expanded)
%              Depth                    :   26
%              Number of atoms          :  424 (11250 expanded)
%              Number of equality atoms :   17 (1010 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v1_tdlat_3(A) )
             => v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

tff(f_182,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_176,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_170,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_158,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_56,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_52,plain,(
    ! [A_69] :
      ( k9_setfam_1(u1_struct_0(A_69)) = u1_pre_topc(A_69)
      | ~ v1_tdlat_3(A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_54,plain,(
    ~ v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_40,plain,(
    ! [A_53] :
      ( m1_pre_topc(A_53,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_551,plain,(
    ! [A_132,B_133] :
      ( m1_pre_topc(A_132,g1_pre_topc(u1_struct_0(B_133),u1_pre_topc(B_133)))
      | ~ m1_pre_topc(A_132,B_133)
      | ~ l1_pre_topc(B_133)
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_575,plain,(
    ! [A_132] :
      ( m1_pre_topc(A_132,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_132,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_551])).

tff(c_658,plain,(
    ! [A_139] :
      ( m1_pre_topc(A_139,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_139,'#skF_2')
      | ~ l1_pre_topc(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_575])).

tff(c_16,plain,(
    ! [B_13,A_11] :
      ( m1_pre_topc(B_13,A_11)
      | ~ m1_pre_topc(B_13,g1_pre_topc(u1_struct_0(A_11),u1_pre_topc(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_670,plain,(
    ! [A_139] :
      ( m1_pre_topc(A_139,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_139,'#skF_2')
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_658,c_16])).

tff(c_731,plain,(
    ! [A_141] :
      ( m1_pre_topc(A_141,'#skF_1')
      | ~ m1_pre_topc(A_141,'#skF_2')
      | ~ l1_pre_topc(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_670])).

tff(c_749,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_731])).

tff(c_762,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_749])).

tff(c_20,plain,(
    ! [A_14,B_16] :
      ( m1_pre_topc(A_14,g1_pre_topc(u1_struct_0(B_16),u1_pre_topc(B_16)))
      | ~ m1_pre_topc(A_14,B_16)
      | ~ l1_pre_topc(B_16)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    ! [A_68] :
      ( v2_pre_topc(A_68)
      | ~ v1_tdlat_3(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_198,plain,(
    ! [B_97,A_98] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_97),u1_pre_topc(B_97)),A_98)
      | ~ m1_pre_topc(B_97,A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v2_pre_topc(B_5)
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_337,plain,(
    ! [B_110,A_111] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(B_110),u1_pre_topc(B_110)))
      | ~ v2_pre_topc(A_111)
      | ~ m1_pre_topc(B_110,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_198,c_8])).

tff(c_352,plain,(
    ! [A_112] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_112),u1_pre_topc(A_112)))
      | ~ v2_pre_topc(A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_40,c_337])).

tff(c_104,plain,(
    ! [A_84] :
      ( v2_pre_topc(A_84)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_84),u1_pre_topc(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_104])).

tff(c_112,plain,
    ( v2_pre_topc('#skF_2')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_107])).

tff(c_114,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_355,plain,
    ( ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_352,c_114])).

tff(c_364,plain,(
    ~ v2_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_355])).

tff(c_371,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_364])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_371])).

tff(c_377,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_411,plain,(
    ! [B_119,A_120] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_119),u1_pre_topc(B_119)),A_120)
      | ~ m1_pre_topc(B_119,A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10,plain,(
    ! [B_8,A_6] :
      ( l1_pre_topc(B_8)
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_436,plain,(
    ! [B_121,A_122] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_121),u1_pre_topc(B_121)))
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_411,c_10])).

tff(c_450,plain,(
    ! [A_126] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_126),u1_pre_topc(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(resolution,[status(thm)],[c_40,c_436])).

tff(c_453,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_450])).

tff(c_455,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_453])).

tff(c_46,plain,(
    ! [C_67,A_61,B_65] :
      ( m1_pre_topc(C_67,A_61)
      | ~ m1_pre_topc(C_67,B_65)
      | ~ m1_pre_topc(B_65,A_61)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_842,plain,(
    ! [A_144] :
      ( m1_pre_topc('#skF_2',A_144)
      | ~ m1_pre_topc('#skF_1',A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_762,c_46])).

tff(c_388,plain,(
    ! [B_115,A_116] :
      ( m1_pre_topc(B_115,A_116)
      | ~ m1_pre_topc(B_115,g1_pre_topc(u1_struct_0(A_116),u1_pre_topc(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_391,plain,(
    ! [B_115] :
      ( m1_pre_topc(B_115,'#skF_2')
      | ~ m1_pre_topc(B_115,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_388])).

tff(c_397,plain,(
    ! [B_115] :
      ( m1_pre_topc(B_115,'#skF_2')
      | ~ m1_pre_topc(B_115,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_391])).

tff(c_864,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_842,c_397])).

tff(c_893,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_455,c_864])).

tff(c_901,plain,(
    ~ m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_893])).

tff(c_907,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_901])).

tff(c_913,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_907])).

tff(c_923,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_913])).

tff(c_927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_923])).

tff(c_929,plain,(
    m1_pre_topc('#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_893])).

tff(c_999,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_929,c_397])).

tff(c_14,plain,(
    ! [A_10] :
      ( v2_pre_topc(A_10)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(A_10),u1_pre_topc(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_384,plain,
    ( v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_377,c_14])).

tff(c_387,plain,(
    v2_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_384])).

tff(c_983,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_929,c_16])).

tff(c_1002,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_983])).

tff(c_1274,plain,(
    ! [B_154,C_155,A_156] :
      ( r1_tarski(u1_struct_0(B_154),u1_struct_0(C_155))
      | ~ m1_pre_topc(B_154,C_155)
      | ~ m1_pre_topc(C_155,A_156)
      | ~ m1_pre_topc(B_154,A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1278,plain,(
    ! [B_154] :
      ( r1_tarski(u1_struct_0(B_154),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_154,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1002,c_1274])).

tff(c_1310,plain,(
    ! [B_154] :
      ( r1_tarski(u1_struct_0(B_154),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_154,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_62,c_1278])).

tff(c_376,plain,(
    v2_pre_topc('#skF_2') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_928,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_893])).

tff(c_1284,plain,(
    ! [B_154] :
      ( r1_tarski(u1_struct_0(B_154),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_154,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_928,c_1274])).

tff(c_1340,plain,(
    ! [B_157] :
      ( r1_tarski(u1_struct_0(B_157),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_157,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_60,c_1284])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1384,plain,(
    ! [B_162] :
      ( u1_struct_0(B_162) = u1_struct_0('#skF_2')
      | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0(B_162))
      | ~ m1_pre_topc(B_162,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1340,c_2])).

tff(c_1392,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1310,c_1384])).

tff(c_1404,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_999,c_1392])).

tff(c_50,plain,(
    ! [A_69] :
      ( v1_tdlat_3(A_69)
      | k9_setfam_1(u1_struct_0(A_69)) != u1_pre_topc(A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1466,plain,
    ( v1_tdlat_3('#skF_2')
    | k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_50])).

tff(c_1502,plain,
    ( v1_tdlat_3('#skF_2')
    | k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1466])).

tff(c_1503,plain,(
    k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1502])).

tff(c_1526,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1503])).

tff(c_1528,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_1526])).

tff(c_12,plain,(
    ! [A_9] :
      ( m1_subset_1(u1_pre_topc(A_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1469,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_12])).

tff(c_1505,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1469])).

tff(c_26,plain,(
    ! [B_41,A_39] :
      ( v1_tops_2(B_41,A_39)
      | ~ r1_tarski(B_41,u1_pre_topc(A_39))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1546,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1505,c_26])).

tff(c_1553,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1546])).

tff(c_1578,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1553])).

tff(c_28,plain,(
    ! [B_41,A_39] :
      ( r1_tarski(B_41,u1_pre_topc(A_39))
      | ~ v1_tops_2(B_41,A_39)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1543,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1505,c_28])).

tff(c_1550,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1543])).

tff(c_1611,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1578,c_1550])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1442,plain,(
    ! [B_41] :
      ( v1_tops_2(B_41,'#skF_2')
      | ~ r1_tarski(B_41,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_26])).

tff(c_58774,plain,(
    ! [B_709] :
      ( v1_tops_2(B_709,'#skF_2')
      | ~ r1_tarski(B_709,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_709,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1442])).

tff(c_58787,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1505,c_58774])).

tff(c_58803,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_58787])).

tff(c_22,plain,(
    ! [C_23,A_17,B_21] :
      ( m1_subset_1(C_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_21))))
      | ~ m1_pre_topc(B_21,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_72000,plain,(
    ! [C_865,A_866] :
      ( m1_subset_1(C_865,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_866))))
      | ~ m1_subset_1(C_865,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc('#skF_2',A_866)
      | ~ l1_pre_topc(A_866) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_22])).

tff(c_72057,plain,(
    ! [A_866] :
      ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_866))))
      | ~ m1_pre_topc('#skF_2',A_866)
      | ~ l1_pre_topc(A_866) ) ),
    inference(resolution,[status(thm)],[c_1505,c_72000])).

tff(c_1054,plain,(
    ! [C_145,A_146,B_147] :
      ( m1_subset_1(C_145,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_146))))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_147))))
      | ~ m1_pre_topc(B_147,A_146)
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1057,plain,(
    ! [A_9,A_146] :
      ( m1_subset_1(u1_pre_topc(A_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_146))))
      | ~ m1_pre_topc(A_9,A_146)
      | ~ l1_pre_topc(A_146)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_1054])).

tff(c_1554,plain,(
    ! [D_166,C_167,A_168] :
      ( v1_tops_2(D_166,C_167)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_167))))
      | ~ v1_tops_2(D_166,A_168)
      | ~ m1_pre_topc(C_167,A_168)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_168))))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_69435,plain,(
    ! [A_835,A_836,A_837] :
      ( v1_tops_2(u1_pre_topc(A_835),A_836)
      | ~ v1_tops_2(u1_pre_topc(A_835),A_837)
      | ~ m1_pre_topc(A_836,A_837)
      | ~ m1_subset_1(u1_pre_topc(A_835),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_837))))
      | ~ l1_pre_topc(A_837)
      | ~ m1_pre_topc(A_835,A_836)
      | ~ l1_pre_topc(A_836)
      | ~ l1_pre_topc(A_835) ) ),
    inference(resolution,[status(thm)],[c_1057,c_1554])).

tff(c_69515,plain,(
    ! [A_835] :
      ( v1_tops_2(u1_pre_topc(A_835),'#skF_1')
      | ~ v1_tops_2(u1_pre_topc(A_835),'#skF_2')
      | ~ m1_subset_1(u1_pre_topc(A_835),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_835,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_835) ) ),
    inference(resolution,[status(thm)],[c_999,c_69435])).

tff(c_113201,plain,(
    ! [A_1178] :
      ( v1_tops_2(u1_pre_topc(A_1178),'#skF_1')
      | ~ v1_tops_2(u1_pre_topc(A_1178),'#skF_2')
      | ~ m1_subset_1(u1_pre_topc(A_1178),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_1178,'#skF_1')
      | ~ l1_pre_topc(A_1178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1404,c_69515])).

tff(c_113231,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72057,c_113201])).

tff(c_113308,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_762,c_60,c_58803,c_113231])).

tff(c_113310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1611,c_113308])).

tff(c_113312,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1553])).

tff(c_113314,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_113312,c_2])).

tff(c_113317,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1528,c_113314])).

tff(c_1436,plain,(
    ! [B_41] :
      ( r1_tarski(B_41,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_41,'#skF_2')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_28])).

tff(c_114382,plain,(
    ! [B_1200] :
      ( r1_tarski(B_1200,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_1200,'#skF_2')
      | ~ m1_subset_1(B_1200,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1436])).

tff(c_114403,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_114382])).

tff(c_114416,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_114403])).

tff(c_114417,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_113317,c_114416])).

tff(c_1428,plain,(
    ! [A_9] :
      ( m1_subset_1(u1_pre_topc(A_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_9,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_1057])).

tff(c_114276,plain,(
    ! [A_1197] :
      ( m1_subset_1(u1_pre_topc(A_1197),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_1197,'#skF_2')
      | ~ l1_pre_topc(A_1197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1428])).

tff(c_114286,plain,(
    ! [A_1197] :
      ( v1_tops_2(u1_pre_topc(A_1197),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_1197),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_1197,'#skF_2')
      | ~ l1_pre_topc(A_1197) ) ),
    inference(resolution,[status(thm)],[c_114276,c_26])).

tff(c_118808,plain,(
    ! [A_1268] :
      ( v1_tops_2(u1_pre_topc(A_1268),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_1268),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc(A_1268,'#skF_2')
      | ~ l1_pre_topc(A_1268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_114286])).

tff(c_118818,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_118808])).

tff(c_118825,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_999,c_118818])).

tff(c_561,plain,(
    ! [A_132] :
      ( m1_pre_topc(A_132,'#skF_2')
      | ~ m1_pre_topc(A_132,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_551,c_397])).

tff(c_581,plain,(
    ! [A_132] :
      ( m1_pre_topc(A_132,'#skF_2')
      | ~ m1_pre_topc(A_132,'#skF_1')
      | ~ l1_pre_topc(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_561])).

tff(c_1261,plain,(
    ! [A_152,A_153] :
      ( m1_subset_1(u1_pre_topc(A_152),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153))))
      | ~ m1_pre_topc(A_152,A_153)
      | ~ l1_pre_topc(A_153)
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_12,c_1054])).

tff(c_120531,plain,(
    ! [A_1292,A_1293,A_1294] :
      ( m1_subset_1(u1_pre_topc(A_1292),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1293))))
      | ~ m1_pre_topc(A_1294,A_1293)
      | ~ l1_pre_topc(A_1293)
      | ~ m1_pre_topc(A_1292,A_1294)
      | ~ l1_pre_topc(A_1294)
      | ~ l1_pre_topc(A_1292) ) ),
    inference(resolution,[status(thm)],[c_1261,c_22])).

tff(c_120605,plain,(
    ! [A_1292,A_132] :
      ( m1_subset_1(u1_pre_topc(A_1292),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_1292,A_132)
      | ~ l1_pre_topc(A_1292)
      | ~ m1_pre_topc(A_132,'#skF_1')
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_581,c_120531])).

tff(c_127522,plain,(
    ! [A_1369,A_1370] :
      ( m1_subset_1(u1_pre_topc(A_1369),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_1369,A_1370)
      | ~ l1_pre_topc(A_1369)
      | ~ m1_pre_topc(A_1370,'#skF_1')
      | ~ l1_pre_topc(A_1370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1404,c_120605])).

tff(c_127602,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1002,c_127522])).

tff(c_127720,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1002,c_127602])).

tff(c_129370,plain,(
    ! [C_1389,A_1390] :
      ( m1_subset_1(C_1389,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1390))))
      | ~ m1_subset_1(C_1389,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc('#skF_2',A_1390)
      | ~ l1_pre_topc(A_1390) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_22])).

tff(c_129412,plain,(
    ! [A_1390] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1390))))
      | ~ m1_pre_topc('#skF_2',A_1390)
      | ~ l1_pre_topc(A_1390) ) ),
    inference(resolution,[status(thm)],[c_127720,c_129370])).

tff(c_126161,plain,(
    ! [A_1353,A_1354,A_1355] :
      ( v1_tops_2(u1_pre_topc(A_1353),A_1354)
      | ~ v1_tops_2(u1_pre_topc(A_1353),A_1355)
      | ~ m1_pre_topc(A_1354,A_1355)
      | ~ m1_subset_1(u1_pre_topc(A_1353),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1355))))
      | ~ l1_pre_topc(A_1355)
      | ~ m1_pre_topc(A_1353,A_1354)
      | ~ l1_pre_topc(A_1354)
      | ~ l1_pre_topc(A_1353) ) ),
    inference(resolution,[status(thm)],[c_1057,c_1554])).

tff(c_126249,plain,(
    ! [A_1353] :
      ( v1_tops_2(u1_pre_topc(A_1353),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_1353),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_1353),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_1353,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1353) ) ),
    inference(resolution,[status(thm)],[c_762,c_126161])).

tff(c_169407,plain,(
    ! [A_1690] :
      ( v1_tops_2(u1_pre_topc(A_1690),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_1690),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_1690),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_1690,'#skF_2')
      | ~ l1_pre_topc(A_1690) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_126249])).

tff(c_169438,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_129412,c_169407])).

tff(c_169513,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_762,c_999,c_118825,c_169438])).

tff(c_169515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114417,c_169513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:38:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.74/28.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.85/28.13  
% 40.85/28.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.85/28.13  %$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 40.85/28.13  
% 40.85/28.13  %Foreground sorts:
% 40.85/28.13  
% 40.85/28.13  
% 40.85/28.13  %Background operators:
% 40.85/28.13  
% 40.85/28.13  
% 40.85/28.13  %Foreground operators:
% 40.85/28.13  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 40.85/28.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.85/28.13  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 40.85/28.13  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 40.85/28.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 40.85/28.13  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 40.85/28.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.85/28.13  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 40.85/28.13  tff('#skF_2', type, '#skF_2': $i).
% 40.85/28.13  tff('#skF_1', type, '#skF_1': $i).
% 40.85/28.13  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 40.85/28.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 40.85/28.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.85/28.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.85/28.13  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 40.85/28.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 40.85/28.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 40.85/28.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 40.85/28.13  
% 40.99/28.16  tff(f_194, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v1_tdlat_3(A)) => v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tex_2)).
% 40.99/28.16  tff(f_182, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) <=> (u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tdlat_3)).
% 40.99/28.16  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 40.99/28.16  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 40.99/28.16  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 40.99/28.16  tff(f_176, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 40.99/28.16  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 40.99/28.16  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 40.99/28.16  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_pre_topc)).
% 40.99/28.16  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 40.99/28.16  tff(f_170, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 40.99/28.16  tff(f_158, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 40.99/28.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 40.99/28.16  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 40.99/28.16  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 40.99/28.16  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 40.99/28.16  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 40.99/28.16  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 40.99/28.16  tff(c_56, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_194])).
% 40.99/28.16  tff(c_52, plain, (![A_69]: (k9_setfam_1(u1_struct_0(A_69))=u1_pre_topc(A_69) | ~v1_tdlat_3(A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_182])).
% 40.99/28.16  tff(c_54, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 40.99/28.16  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 40.99/28.16  tff(c_40, plain, (![A_53]: (m1_pre_topc(A_53, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_144])).
% 40.99/28.16  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 40.99/28.16  tff(c_551, plain, (![A_132, B_133]: (m1_pre_topc(A_132, g1_pre_topc(u1_struct_0(B_133), u1_pre_topc(B_133))) | ~m1_pre_topc(A_132, B_133) | ~l1_pre_topc(B_133) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_73])).
% 40.99/28.16  tff(c_575, plain, (![A_132]: (m1_pre_topc(A_132, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_132, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_132))), inference(superposition, [status(thm), theory('equality')], [c_58, c_551])).
% 40.99/28.16  tff(c_658, plain, (![A_139]: (m1_pre_topc(A_139, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_139, '#skF_2') | ~l1_pre_topc(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_575])).
% 40.99/28.16  tff(c_16, plain, (![B_13, A_11]: (m1_pre_topc(B_13, A_11) | ~m1_pre_topc(B_13, g1_pre_topc(u1_struct_0(A_11), u1_pre_topc(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 40.99/28.16  tff(c_670, plain, (![A_139]: (m1_pre_topc(A_139, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_139, '#skF_2') | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_658, c_16])).
% 40.99/28.16  tff(c_731, plain, (![A_141]: (m1_pre_topc(A_141, '#skF_1') | ~m1_pre_topc(A_141, '#skF_2') | ~l1_pre_topc(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_670])).
% 40.99/28.16  tff(c_749, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_731])).
% 40.99/28.16  tff(c_762, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_749])).
% 40.99/28.16  tff(c_20, plain, (![A_14, B_16]: (m1_pre_topc(A_14, g1_pre_topc(u1_struct_0(B_16), u1_pre_topc(B_16))) | ~m1_pre_topc(A_14, B_16) | ~l1_pre_topc(B_16) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 40.99/28.16  tff(c_48, plain, (![A_68]: (v2_pre_topc(A_68) | ~v1_tdlat_3(A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_176])).
% 40.99/28.16  tff(c_198, plain, (![B_97, A_98]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_97), u1_pre_topc(B_97)), A_98) | ~m1_pre_topc(B_97, A_98) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_122])).
% 40.99/28.16  tff(c_8, plain, (![B_5, A_3]: (v2_pre_topc(B_5) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 40.99/28.16  tff(c_337, plain, (![B_110, A_111]: (v2_pre_topc(g1_pre_topc(u1_struct_0(B_110), u1_pre_topc(B_110))) | ~v2_pre_topc(A_111) | ~m1_pre_topc(B_110, A_111) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_198, c_8])).
% 40.99/28.16  tff(c_352, plain, (![A_112]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_112), u1_pre_topc(A_112))) | ~v2_pre_topc(A_112) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_40, c_337])).
% 40.99/28.16  tff(c_104, plain, (![A_84]: (v2_pre_topc(A_84) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_84), u1_pre_topc(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.99/28.16  tff(c_107, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_104])).
% 40.99/28.16  tff(c_112, plain, (v2_pre_topc('#skF_2') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_107])).
% 40.99/28.16  tff(c_114, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_112])).
% 40.99/28.16  tff(c_355, plain, (~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_352, c_114])).
% 40.99/28.16  tff(c_364, plain, (~v2_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_355])).
% 40.99/28.16  tff(c_371, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_364])).
% 40.99/28.16  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_371])).
% 40.99/28.16  tff(c_377, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_112])).
% 40.99/28.16  tff(c_411, plain, (![B_119, A_120]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_119), u1_pre_topc(B_119)), A_120) | ~m1_pre_topc(B_119, A_120) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_122])).
% 40.99/28.16  tff(c_10, plain, (![B_8, A_6]: (l1_pre_topc(B_8) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 40.99/28.16  tff(c_436, plain, (![B_121, A_122]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_121), u1_pre_topc(B_121))) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122))), inference(resolution, [status(thm)], [c_411, c_10])).
% 40.99/28.16  tff(c_450, plain, (![A_126]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_126), u1_pre_topc(A_126))) | ~l1_pre_topc(A_126))), inference(resolution, [status(thm)], [c_40, c_436])).
% 40.99/28.16  tff(c_453, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_450])).
% 40.99/28.16  tff(c_455, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_453])).
% 40.99/28.16  tff(c_46, plain, (![C_67, A_61, B_65]: (m1_pre_topc(C_67, A_61) | ~m1_pre_topc(C_67, B_65) | ~m1_pre_topc(B_65, A_61) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_170])).
% 40.99/28.16  tff(c_842, plain, (![A_144]: (m1_pre_topc('#skF_2', A_144) | ~m1_pre_topc('#skF_1', A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(resolution, [status(thm)], [c_762, c_46])).
% 40.99/28.16  tff(c_388, plain, (![B_115, A_116]: (m1_pre_topc(B_115, A_116) | ~m1_pre_topc(B_115, g1_pre_topc(u1_struct_0(A_116), u1_pre_topc(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_64])).
% 40.99/28.16  tff(c_391, plain, (![B_115]: (m1_pre_topc(B_115, '#skF_2') | ~m1_pre_topc(B_115, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_388])).
% 40.99/28.16  tff(c_397, plain, (![B_115]: (m1_pre_topc(B_115, '#skF_2') | ~m1_pre_topc(B_115, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_391])).
% 40.99/28.16  tff(c_864, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_842, c_397])).
% 40.99/28.16  tff(c_893, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_377, c_455, c_864])).
% 40.99/28.16  tff(c_901, plain, (~m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_893])).
% 40.99/28.16  tff(c_907, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_901])).
% 40.99/28.16  tff(c_913, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_907])).
% 40.99/28.16  tff(c_923, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_913])).
% 40.99/28.16  tff(c_927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_923])).
% 40.99/28.16  tff(c_929, plain, (m1_pre_topc('#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_893])).
% 40.99/28.16  tff(c_999, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_929, c_397])).
% 40.99/28.16  tff(c_14, plain, (![A_10]: (v2_pre_topc(A_10) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(A_10), u1_pre_topc(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 40.99/28.16  tff(c_384, plain, (v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_377, c_14])).
% 40.99/28.16  tff(c_387, plain, (v2_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_384])).
% 40.99/28.16  tff(c_983, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_929, c_16])).
% 40.99/28.16  tff(c_1002, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_983])).
% 40.99/28.16  tff(c_1274, plain, (![B_154, C_155, A_156]: (r1_tarski(u1_struct_0(B_154), u1_struct_0(C_155)) | ~m1_pre_topc(B_154, C_155) | ~m1_pre_topc(C_155, A_156) | ~m1_pre_topc(B_154, A_156) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_158])).
% 40.99/28.16  tff(c_1278, plain, (![B_154]: (r1_tarski(u1_struct_0(B_154), u1_struct_0('#skF_1')) | ~m1_pre_topc(B_154, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1002, c_1274])).
% 40.99/28.16  tff(c_1310, plain, (![B_154]: (r1_tarski(u1_struct_0(B_154), u1_struct_0('#skF_1')) | ~m1_pre_topc(B_154, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_62, c_1278])).
% 40.99/28.16  tff(c_376, plain, (v2_pre_topc('#skF_2')), inference(splitRight, [status(thm)], [c_112])).
% 40.99/28.16  tff(c_928, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_893])).
% 40.99/28.16  tff(c_1284, plain, (![B_154]: (r1_tarski(u1_struct_0(B_154), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_154, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_928, c_1274])).
% 40.99/28.16  tff(c_1340, plain, (![B_157]: (r1_tarski(u1_struct_0(B_157), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_157, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_60, c_1284])).
% 40.99/28.16  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 40.99/28.16  tff(c_1384, plain, (![B_162]: (u1_struct_0(B_162)=u1_struct_0('#skF_2') | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0(B_162)) | ~m1_pre_topc(B_162, '#skF_2'))), inference(resolution, [status(thm)], [c_1340, c_2])).
% 40.99/28.16  tff(c_1392, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1310, c_1384])).
% 40.99/28.16  tff(c_1404, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_762, c_999, c_1392])).
% 40.99/28.16  tff(c_50, plain, (![A_69]: (v1_tdlat_3(A_69) | k9_setfam_1(u1_struct_0(A_69))!=u1_pre_topc(A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_182])).
% 40.99/28.16  tff(c_1466, plain, (v1_tdlat_3('#skF_2') | k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1404, c_50])).
% 40.99/28.16  tff(c_1502, plain, (v1_tdlat_3('#skF_2') | k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1466])).
% 40.99/28.16  tff(c_1503, plain, (k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_1502])).
% 40.99/28.16  tff(c_1526, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_52, c_1503])).
% 40.99/28.16  tff(c_1528, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_1526])).
% 40.99/28.16  tff(c_12, plain, (![A_9]: (m1_subset_1(u1_pre_topc(A_9), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 40.99/28.16  tff(c_1469, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1404, c_12])).
% 40.99/28.16  tff(c_1505, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1469])).
% 40.99/28.16  tff(c_26, plain, (![B_41, A_39]: (v1_tops_2(B_41, A_39) | ~r1_tarski(B_41, u1_pre_topc(A_39)) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39)))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_109])).
% 40.99/28.16  tff(c_1546, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1505, c_26])).
% 40.99/28.16  tff(c_1553, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1546])).
% 40.99/28.16  tff(c_1578, plain, (~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_1553])).
% 40.99/28.16  tff(c_28, plain, (![B_41, A_39]: (r1_tarski(B_41, u1_pre_topc(A_39)) | ~v1_tops_2(B_41, A_39) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39)))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_109])).
% 40.99/28.16  tff(c_1543, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1505, c_28])).
% 40.99/28.16  tff(c_1550, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1543])).
% 40.99/28.16  tff(c_1611, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1578, c_1550])).
% 40.99/28.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 40.99/28.16  tff(c_1442, plain, (![B_41]: (v1_tops_2(B_41, '#skF_2') | ~r1_tarski(B_41, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1404, c_26])).
% 40.99/28.16  tff(c_58774, plain, (![B_709]: (v1_tops_2(B_709, '#skF_2') | ~r1_tarski(B_709, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_709, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1442])).
% 40.99/28.16  tff(c_58787, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1505, c_58774])).
% 40.99/28.16  tff(c_58803, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_58787])).
% 40.99/28.16  tff(c_22, plain, (![C_23, A_17, B_21]: (m1_subset_1(C_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17)))) | ~m1_subset_1(C_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_21)))) | ~m1_pre_topc(B_21, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 40.99/28.16  tff(c_72000, plain, (![C_865, A_866]: (m1_subset_1(C_865, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_866)))) | ~m1_subset_1(C_865, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', A_866) | ~l1_pre_topc(A_866))), inference(superposition, [status(thm), theory('equality')], [c_1404, c_22])).
% 40.99/28.16  tff(c_72057, plain, (![A_866]: (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_866)))) | ~m1_pre_topc('#skF_2', A_866) | ~l1_pre_topc(A_866))), inference(resolution, [status(thm)], [c_1505, c_72000])).
% 40.99/28.16  tff(c_1054, plain, (![C_145, A_146, B_147]: (m1_subset_1(C_145, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_146)))) | ~m1_subset_1(C_145, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_147)))) | ~m1_pre_topc(B_147, A_146) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_83])).
% 40.99/28.16  tff(c_1057, plain, (![A_9, A_146]: (m1_subset_1(u1_pre_topc(A_9), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_146)))) | ~m1_pre_topc(A_9, A_146) | ~l1_pre_topc(A_146) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_12, c_1054])).
% 40.99/28.16  tff(c_1554, plain, (![D_166, C_167, A_168]: (v1_tops_2(D_166, C_167) | ~m1_subset_1(D_166, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_167)))) | ~v1_tops_2(D_166, A_168) | ~m1_pre_topc(C_167, A_168) | ~m1_subset_1(D_166, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_168)))) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_100])).
% 40.99/28.16  tff(c_69435, plain, (![A_835, A_836, A_837]: (v1_tops_2(u1_pre_topc(A_835), A_836) | ~v1_tops_2(u1_pre_topc(A_835), A_837) | ~m1_pre_topc(A_836, A_837) | ~m1_subset_1(u1_pre_topc(A_835), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_837)))) | ~l1_pre_topc(A_837) | ~m1_pre_topc(A_835, A_836) | ~l1_pre_topc(A_836) | ~l1_pre_topc(A_835))), inference(resolution, [status(thm)], [c_1057, c_1554])).
% 40.99/28.16  tff(c_69515, plain, (![A_835]: (v1_tops_2(u1_pre_topc(A_835), '#skF_1') | ~v1_tops_2(u1_pre_topc(A_835), '#skF_2') | ~m1_subset_1(u1_pre_topc(A_835), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_835, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_835))), inference(resolution, [status(thm)], [c_999, c_69435])).
% 40.99/28.16  tff(c_113201, plain, (![A_1178]: (v1_tops_2(u1_pre_topc(A_1178), '#skF_1') | ~v1_tops_2(u1_pre_topc(A_1178), '#skF_2') | ~m1_subset_1(u1_pre_topc(A_1178), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_1178, '#skF_1') | ~l1_pre_topc(A_1178))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1404, c_69515])).
% 40.99/28.16  tff(c_113231, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72057, c_113201])).
% 40.99/28.16  tff(c_113308, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_762, c_60, c_58803, c_113231])).
% 40.99/28.16  tff(c_113310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1611, c_113308])).
% 40.99/28.16  tff(c_113312, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_1553])).
% 40.99/28.16  tff(c_113314, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_113312, c_2])).
% 40.99/28.16  tff(c_113317, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1528, c_113314])).
% 40.99/28.16  tff(c_1436, plain, (![B_41]: (r1_tarski(B_41, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_41, '#skF_2') | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1404, c_28])).
% 40.99/28.16  tff(c_114382, plain, (![B_1200]: (r1_tarski(B_1200, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_1200, '#skF_2') | ~m1_subset_1(B_1200, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1436])).
% 40.99/28.16  tff(c_114403, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_114382])).
% 40.99/28.16  tff(c_114416, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_114403])).
% 40.99/28.16  tff(c_114417, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_113317, c_114416])).
% 40.99/28.16  tff(c_1428, plain, (![A_9]: (m1_subset_1(u1_pre_topc(A_9), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_9, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_9))), inference(superposition, [status(thm), theory('equality')], [c_1404, c_1057])).
% 40.99/28.16  tff(c_114276, plain, (![A_1197]: (m1_subset_1(u1_pre_topc(A_1197), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_1197, '#skF_2') | ~l1_pre_topc(A_1197))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1428])).
% 40.99/28.16  tff(c_114286, plain, (![A_1197]: (v1_tops_2(u1_pre_topc(A_1197), '#skF_1') | ~r1_tarski(u1_pre_topc(A_1197), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_1197, '#skF_2') | ~l1_pre_topc(A_1197))), inference(resolution, [status(thm)], [c_114276, c_26])).
% 40.99/28.16  tff(c_118808, plain, (![A_1268]: (v1_tops_2(u1_pre_topc(A_1268), '#skF_1') | ~r1_tarski(u1_pre_topc(A_1268), u1_pre_topc('#skF_1')) | ~m1_pre_topc(A_1268, '#skF_2') | ~l1_pre_topc(A_1268))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_114286])).
% 40.99/28.16  tff(c_118818, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_118808])).
% 40.99/28.16  tff(c_118825, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_999, c_118818])).
% 40.99/28.16  tff(c_561, plain, (![A_132]: (m1_pre_topc(A_132, '#skF_2') | ~m1_pre_topc(A_132, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_551, c_397])).
% 40.99/28.16  tff(c_581, plain, (![A_132]: (m1_pre_topc(A_132, '#skF_2') | ~m1_pre_topc(A_132, '#skF_1') | ~l1_pre_topc(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_561])).
% 40.99/28.16  tff(c_1261, plain, (![A_152, A_153]: (m1_subset_1(u1_pre_topc(A_152), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153)))) | ~m1_pre_topc(A_152, A_153) | ~l1_pre_topc(A_153) | ~l1_pre_topc(A_152))), inference(resolution, [status(thm)], [c_12, c_1054])).
% 40.99/28.16  tff(c_120531, plain, (![A_1292, A_1293, A_1294]: (m1_subset_1(u1_pre_topc(A_1292), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1293)))) | ~m1_pre_topc(A_1294, A_1293) | ~l1_pre_topc(A_1293) | ~m1_pre_topc(A_1292, A_1294) | ~l1_pre_topc(A_1294) | ~l1_pre_topc(A_1292))), inference(resolution, [status(thm)], [c_1261, c_22])).
% 40.99/28.16  tff(c_120605, plain, (![A_1292, A_132]: (m1_subset_1(u1_pre_topc(A_1292), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_1292, A_132) | ~l1_pre_topc(A_1292) | ~m1_pre_topc(A_132, '#skF_1') | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_581, c_120531])).
% 40.99/28.16  tff(c_127522, plain, (![A_1369, A_1370]: (m1_subset_1(u1_pre_topc(A_1369), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_1369, A_1370) | ~l1_pre_topc(A_1369) | ~m1_pre_topc(A_1370, '#skF_1') | ~l1_pre_topc(A_1370))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1404, c_120605])).
% 40.99/28.16  tff(c_127602, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1002, c_127522])).
% 40.99/28.16  tff(c_127720, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1002, c_127602])).
% 40.99/28.16  tff(c_129370, plain, (![C_1389, A_1390]: (m1_subset_1(C_1389, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1390)))) | ~m1_subset_1(C_1389, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', A_1390) | ~l1_pre_topc(A_1390))), inference(superposition, [status(thm), theory('equality')], [c_1404, c_22])).
% 40.99/28.16  tff(c_129412, plain, (![A_1390]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1390)))) | ~m1_pre_topc('#skF_2', A_1390) | ~l1_pre_topc(A_1390))), inference(resolution, [status(thm)], [c_127720, c_129370])).
% 40.99/28.16  tff(c_126161, plain, (![A_1353, A_1354, A_1355]: (v1_tops_2(u1_pre_topc(A_1353), A_1354) | ~v1_tops_2(u1_pre_topc(A_1353), A_1355) | ~m1_pre_topc(A_1354, A_1355) | ~m1_subset_1(u1_pre_topc(A_1353), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1355)))) | ~l1_pre_topc(A_1355) | ~m1_pre_topc(A_1353, A_1354) | ~l1_pre_topc(A_1354) | ~l1_pre_topc(A_1353))), inference(resolution, [status(thm)], [c_1057, c_1554])).
% 40.99/28.16  tff(c_126249, plain, (![A_1353]: (v1_tops_2(u1_pre_topc(A_1353), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_1353), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_1353), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_1353, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_1353))), inference(resolution, [status(thm)], [c_762, c_126161])).
% 40.99/28.16  tff(c_169407, plain, (![A_1690]: (v1_tops_2(u1_pre_topc(A_1690), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_1690), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_1690), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_1690, '#skF_2') | ~l1_pre_topc(A_1690))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_126249])).
% 40.99/28.16  tff(c_169438, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_129412, c_169407])).
% 40.99/28.16  tff(c_169513, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_762, c_999, c_118825, c_169438])).
% 40.99/28.16  tff(c_169515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114417, c_169513])).
% 40.99/28.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.99/28.16  
% 40.99/28.16  Inference rules
% 40.99/28.16  ----------------------
% 40.99/28.16  #Ref     : 0
% 40.99/28.16  #Sup     : 35950
% 40.99/28.16  #Fact    : 0
% 40.99/28.16  #Define  : 0
% 40.99/28.16  #Split   : 57
% 40.99/28.16  #Chain   : 0
% 40.99/28.16  #Close   : 0
% 40.99/28.16  
% 40.99/28.16  Ordering : KBO
% 40.99/28.16  
% 40.99/28.16  Simplification rules
% 40.99/28.16  ----------------------
% 40.99/28.16  #Subsume      : 8653
% 40.99/28.16  #Demod        : 93622
% 40.99/28.16  #Tautology    : 11977
% 40.99/28.16  #SimpNegUnit  : 290
% 40.99/28.16  #BackRed      : 13
% 40.99/28.16  
% 40.99/28.16  #Partial instantiations: 0
% 40.99/28.16  #Strategies tried      : 1
% 40.99/28.16  
% 40.99/28.16  Timing (in seconds)
% 40.99/28.16  ----------------------
% 40.99/28.16  Preprocessing        : 0.41
% 40.99/28.16  Parsing              : 0.23
% 40.99/28.16  CNF conversion       : 0.03
% 40.99/28.16  Main loop            : 26.88
% 40.99/28.16  Inferencing          : 3.23
% 40.99/28.16  Reduction            : 9.88
% 40.99/28.16  Demodulation         : 8.20
% 40.99/28.16  BG Simplification    : 0.42
% 40.99/28.16  Subsumption          : 12.25
% 40.99/28.16  Abstraction          : 0.95
% 40.99/28.16  MUC search           : 0.00
% 40.99/28.16  Cooper               : 0.00
% 40.99/28.17  Total                : 27.35
% 40.99/28.17  Index Insertion      : 0.00
% 40.99/28.17  Index Deletion       : 0.00
% 40.99/28.17  Index Matching       : 0.00
% 40.99/28.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
