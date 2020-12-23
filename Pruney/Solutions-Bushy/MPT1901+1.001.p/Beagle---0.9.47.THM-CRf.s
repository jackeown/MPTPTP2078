%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:39 EST 2020

% Result     : Theorem 16.97s
% Output     : CNFRefutation 16.97s
% Verified   : 
% Statistics : Number of formulae       :  146 (1503 expanded)
%              Number of leaves         :   53 ( 537 expanded)
%              Depth                    :   23
%              Number of atoms          :  296 (3446 expanded)
%              Number of equality atoms :   30 ( 863 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k6_relat_1 > k6_partfun1 > k2_subset_1 > k1_zfmisc_1 > k1_compts_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k1_compts_1,type,(
    k1_compts_1: $i > $i )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( ! [B] :
              ( ( ~ v2_struct_0(B)
                & v2_pre_topc(B)
                & l1_pre_topc(B) )
             => ! [C] :
                  ( ( v1_funct_1(C)
                    & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                    & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                 => v5_pre_topc(C,A,B) ) )
         => v1_tdlat_3(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tex_2)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A] : l1_pre_topc(k1_compts_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_compts_1)).

tff(f_107,axiom,(
    ! [A] : v1_tdlat_3(k1_compts_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tex_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

tff(f_118,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_124,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_69,axiom,(
    ! [A] : k1_compts_1(A) = g1_pre_topc(A,k2_subset_1(k9_setfam_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_compts_1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_116,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

tff(f_93,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ~ v2_struct_0(k1_compts_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_compts_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_32,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_62,plain,(
    ~ v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_24,plain,(
    ! [A_31] : l1_pre_topc(k1_compts_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [A_38] : v1_tdlat_3(k1_compts_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_5] :
      ( v2_pre_topc(A_5)
      | ~ v1_tdlat_3(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    ! [A_37] : v1_funct_1(k6_relat_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_71,plain,(
    ! [A_37] : v1_funct_1(k6_partfun1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40])).

tff(c_28,plain,(
    ! [A_33] : v1_partfun1(k6_partfun1(A_33),A_33) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_551,plain,(
    ! [C_136,A_137,B_138] :
      ( v1_funct_2(C_136,A_137,B_138)
      | ~ v1_partfun1(C_136,A_137)
      | ~ v1_funct_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_554,plain,(
    ! [A_33] :
      ( v1_funct_2(k6_partfun1(A_33),A_33,A_33)
      | ~ v1_partfun1(k6_partfun1(A_33),A_33)
      | ~ v1_funct_1(k6_partfun1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_30,c_551])).

tff(c_561,plain,(
    ! [A_33] : v1_funct_2(k6_partfun1(A_33),A_33,A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_28,c_554])).

tff(c_117,plain,(
    ! [A_78] : m1_subset_1(k6_partfun1(A_78),k1_zfmisc_1(k2_zfmisc_1(A_78,A_78))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_64,plain,(
    ! [C_62,B_60] :
      ( v5_pre_topc(C_62,'#skF_3',B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_60))))
      | ~ v1_funct_2(C_62,u1_struct_0('#skF_3'),u1_struct_0(B_60))
      | ~ v1_funct_1(C_62)
      | ~ l1_pre_topc(B_60)
      | ~ v2_pre_topc(B_60)
      | v2_struct_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_121,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),'#skF_3','#skF_3')
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_64])).

tff(c_124,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),'#skF_3','#skF_3')
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_71,c_121])).

tff(c_125,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),'#skF_3','#skF_3')
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_124])).

tff(c_126,plain,(
    ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_126])).

tff(c_567,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_52,plain,(
    ! [A_50] : k9_setfam_1(A_50) = k1_zfmisc_1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_18,plain,(
    ! [A_28] : g1_pre_topc(A_28,k2_subset_1(k9_setfam_1(A_28))) = k1_compts_1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_73,plain,(
    ! [A_28] : g1_pre_topc(A_28,k2_subset_1(k1_zfmisc_1(A_28))) = k1_compts_1(A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_26,plain,(
    ! [A_32] : m1_subset_1(k2_subset_1(A_32),k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_576,plain,(
    ! [A_142,B_143] :
      ( v1_pre_topc(g1_pre_topc(A_142,B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k1_zfmisc_1(A_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_580,plain,(
    ! [A_142] : v1_pre_topc(g1_pre_topc(A_142,k2_subset_1(k1_zfmisc_1(A_142)))) ),
    inference(resolution,[status(thm)],[c_26,c_576])).

tff(c_582,plain,(
    ! [A_142] : v1_pre_topc(k1_compts_1(A_142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_580])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_633,plain,(
    ! [C_155,A_156,D_157,B_158] :
      ( C_155 = A_156
      | g1_pre_topc(C_155,D_157) != g1_pre_topc(A_156,B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k1_zfmisc_1(A_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_641,plain,(
    ! [C_155,A_28,D_157] :
      ( C_155 = A_28
      | k1_compts_1(A_28) != g1_pre_topc(C_155,D_157)
      | ~ m1_subset_1(k2_subset_1(k1_zfmisc_1(A_28)),k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_633])).

tff(c_644,plain,(
    ! [C_159,A_160,D_161] :
      ( C_159 = A_160
      | k1_compts_1(A_160) != g1_pre_topc(C_159,D_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_641])).

tff(c_647,plain,(
    ! [A_1,A_160] :
      ( u1_struct_0(A_1) = A_160
      | k1_compts_1(A_160) != A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_644])).

tff(c_664,plain,(
    ! [A_160] :
      ( u1_struct_0(k1_compts_1(A_160)) = A_160
      | ~ v1_pre_topc(k1_compts_1(A_160))
      | ~ l1_pre_topc(k1_compts_1(A_160)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_647])).

tff(c_666,plain,(
    ! [A_160] : u1_struct_0(k1_compts_1(A_160)) = A_160 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_582,c_664])).

tff(c_668,plain,(
    ! [A_169] : u1_struct_0(k1_compts_1(A_169)) = A_169 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_582,c_664])).

tff(c_689,plain,(
    ! [C_62,A_169] :
      ( v5_pre_topc(C_62,'#skF_3',k1_compts_1(A_169))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),A_169)))
      | ~ v1_funct_2(C_62,u1_struct_0('#skF_3'),u1_struct_0(k1_compts_1(A_169)))
      | ~ v1_funct_1(C_62)
      | ~ l1_pre_topc(k1_compts_1(A_169))
      | ~ v2_pre_topc(k1_compts_1(A_169))
      | v2_struct_0(k1_compts_1(A_169)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_64])).

tff(c_757,plain,(
    ! [C_178,A_179] :
      ( v5_pre_topc(C_178,'#skF_3',k1_compts_1(A_179))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),A_179)))
      | ~ v1_funct_2(C_178,u1_struct_0('#skF_3'),A_179)
      | ~ v1_funct_1(C_178)
      | ~ v2_pre_topc(k1_compts_1(A_179))
      | v2_struct_0(k1_compts_1(A_179)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_666,c_689])).

tff(c_761,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),'#skF_3',k1_compts_1(u1_struct_0('#skF_3')))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | ~ v2_pre_topc(k1_compts_1(u1_struct_0('#skF_3')))
    | v2_struct_0(k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_30,c_757])).

tff(c_768,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),'#skF_3',k1_compts_1(u1_struct_0('#skF_3')))
    | ~ v2_pre_topc(k1_compts_1(u1_struct_0('#skF_3')))
    | v2_struct_0(k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_567,c_761])).

tff(c_1264,plain,(
    ~ v2_pre_topc(k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_768])).

tff(c_1267,plain,
    ( ~ v1_tdlat_3(k1_compts_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc(k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_8,c_1264])).

tff(c_1271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42,c_1267])).

tff(c_1273,plain,(
    v2_pre_topc(k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_768])).

tff(c_60,plain,(
    ! [A_53] :
      ( m1_subset_1('#skF_2'(A_53),k1_zfmisc_1(u1_struct_0(A_53)))
      | v1_tdlat_3(A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_705,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k8_relset_1(A_170,B_171,C_172,D_173) = k10_relat_1(C_172,D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_711,plain,(
    ! [A_33,D_173] : k8_relset_1(A_33,A_33,k6_partfun1(A_33),D_173) = k10_relat_1(k6_partfun1(A_33),D_173) ),
    inference(resolution,[status(thm)],[c_30,c_705])).

tff(c_54,plain,(
    ! [A_51,B_52] :
      ( k8_relset_1(A_51,A_51,k6_partfun1(A_51),B_52) = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_780,plain,(
    ! [A_181,B_182] :
      ( k10_relat_1(k6_partfun1(A_181),B_182) = B_182
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_181)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_54])).

tff(c_790,plain,(
    ! [A_53] :
      ( k10_relat_1(k6_partfun1(u1_struct_0(A_53)),'#skF_2'(A_53)) = '#skF_2'(A_53)
      | v1_tdlat_3(A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_60,c_780])).

tff(c_1272,plain,
    ( v2_struct_0(k1_compts_1(u1_struct_0('#skF_3')))
    | v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),'#skF_3',k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_768])).

tff(c_1274,plain,(
    v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),'#skF_3',k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1272])).

tff(c_1034,plain,(
    ! [C_201,A_202,B_203] :
      ( v1_funct_2(C_201,A_202,B_203)
      | ~ v1_partfun1(C_201,A_202)
      | ~ v1_funct_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1037,plain,(
    ! [A_33] :
      ( v1_funct_2(k6_partfun1(A_33),A_33,A_33)
      | ~ v1_partfun1(k6_partfun1(A_33),A_33)
      | ~ v1_funct_1(k6_partfun1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1034])).

tff(c_1044,plain,(
    ! [A_33] : v1_funct_2(k6_partfun1(A_33),A_33,A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_28,c_1037])).

tff(c_1305,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_235),u1_struct_0(B_236),C_237,D_238),A_235)
      | ~ v4_pre_topc(D_238,B_236)
      | ~ m1_subset_1(D_238,k1_zfmisc_1(u1_struct_0(B_236)))
      | ~ v5_pre_topc(C_237,A_235,B_236)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),u1_struct_0(B_236))))
      | ~ v1_funct_2(C_237,u1_struct_0(A_235),u1_struct_0(B_236))
      | ~ v1_funct_1(C_237)
      | ~ l1_pre_topc(B_236)
      | ~ l1_pre_topc(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1309,plain,(
    ! [A_235,A_160,C_237,D_238] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_235),u1_struct_0(k1_compts_1(A_160)),C_237,D_238),A_235)
      | ~ v4_pre_topc(D_238,k1_compts_1(A_160))
      | ~ m1_subset_1(D_238,k1_zfmisc_1(u1_struct_0(k1_compts_1(A_160))))
      | ~ v5_pre_topc(C_237,A_235,k1_compts_1(A_160))
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),A_160)))
      | ~ v1_funct_2(C_237,u1_struct_0(A_235),u1_struct_0(k1_compts_1(A_160)))
      | ~ v1_funct_1(C_237)
      | ~ l1_pre_topc(k1_compts_1(A_160))
      | ~ l1_pre_topc(A_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_1305])).

tff(c_11513,plain,(
    ! [A_875,A_876,C_877,D_878] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_875),A_876,C_877,D_878),A_875)
      | ~ v4_pre_topc(D_878,k1_compts_1(A_876))
      | ~ m1_subset_1(D_878,k1_zfmisc_1(A_876))
      | ~ v5_pre_topc(C_877,A_875,k1_compts_1(A_876))
      | ~ m1_subset_1(C_877,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_875),A_876)))
      | ~ v1_funct_2(C_877,u1_struct_0(A_875),A_876)
      | ~ v1_funct_1(C_877)
      | ~ l1_pre_topc(A_875) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_666,c_666,c_666,c_1309])).

tff(c_11529,plain,(
    ! [A_875,D_878] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_875),u1_struct_0(A_875),k6_partfun1(u1_struct_0(A_875)),D_878),A_875)
      | ~ v4_pre_topc(D_878,k1_compts_1(u1_struct_0(A_875)))
      | ~ m1_subset_1(D_878,k1_zfmisc_1(u1_struct_0(A_875)))
      | ~ v5_pre_topc(k6_partfun1(u1_struct_0(A_875)),A_875,k1_compts_1(u1_struct_0(A_875)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_875)),u1_struct_0(A_875),u1_struct_0(A_875))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_875)))
      | ~ l1_pre_topc(A_875) ) ),
    inference(resolution,[status(thm)],[c_30,c_11513])).

tff(c_19694,plain,(
    ! [A_1482,D_1483] :
      ( v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(A_1482)),D_1483),A_1482)
      | ~ v4_pre_topc(D_1483,k1_compts_1(u1_struct_0(A_1482)))
      | ~ m1_subset_1(D_1483,k1_zfmisc_1(u1_struct_0(A_1482)))
      | ~ v5_pre_topc(k6_partfun1(u1_struct_0(A_1482)),A_1482,k1_compts_1(u1_struct_0(A_1482)))
      | ~ l1_pre_topc(A_1482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1044,c_711,c_11529])).

tff(c_19716,plain,(
    ! [D_1483] :
      ( v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0('#skF_3')),D_1483),'#skF_3')
      | ~ v4_pre_topc(D_1483,k1_compts_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_1483,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1274,c_19694])).

tff(c_19728,plain,(
    ! [D_1484] :
      ( v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0('#skF_3')),D_1484),'#skF_3')
      | ~ v4_pre_topc(D_1484,k1_compts_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_1484,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_19716])).

tff(c_19748,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ v4_pre_topc('#skF_2'('#skF_3'),k1_compts_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_19728])).

tff(c_19761,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ v4_pre_topc('#skF_2'('#skF_3'),k1_compts_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_19748])).

tff(c_19762,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ v4_pre_topc('#skF_2'('#skF_3'),k1_compts_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_19761])).

tff(c_19778,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_19762])).

tff(c_19781,plain,
    ( v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_19778])).

tff(c_19784,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_19781])).

tff(c_19786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_19784])).

tff(c_19788,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_19762])).

tff(c_854,plain,(
    ! [B_186,A_187] :
      ( v4_pre_topc(B_186,A_187)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ v1_tdlat_3(A_187)
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_857,plain,(
    ! [B_186,A_160] :
      ( v4_pre_topc(B_186,k1_compts_1(A_160))
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_160))
      | ~ v1_tdlat_3(k1_compts_1(A_160))
      | ~ l1_pre_topc(k1_compts_1(A_160))
      | ~ v2_pre_topc(k1_compts_1(A_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_854])).

tff(c_866,plain,(
    ! [B_186,A_160] :
      ( v4_pre_topc(B_186,k1_compts_1(A_160))
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_160))
      | ~ v2_pre_topc(k1_compts_1(A_160)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42,c_857])).

tff(c_19787,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_3'),k1_compts_1(u1_struct_0('#skF_3')))
    | v4_pre_topc('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_19762])).

tff(c_19837,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_3'),k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_19787])).

tff(c_19840,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_pre_topc(k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_866,c_19837])).

tff(c_19844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_19788,c_19840])).

tff(c_19845,plain,(
    v4_pre_topc('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_19787])).

tff(c_58,plain,(
    ! [A_53] :
      ( ~ v4_pre_topc('#skF_2'(A_53),A_53)
      | v1_tdlat_3(A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_19888,plain,
    ( v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_19845,c_58])).

tff(c_19891,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_19888])).

tff(c_19893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_19891])).

tff(c_19894,plain,(
    v2_struct_0(k1_compts_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1272])).

tff(c_34,plain,(
    ! [A_35] :
      ( ~ v2_struct_0(k1_compts_1(A_35))
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_19899,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_19894,c_34])).

tff(c_36,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_19902,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_19899,c_36])).

tff(c_19905,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_19902])).

tff(c_19908,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_19905])).

tff(c_19912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_19908])).

%------------------------------------------------------------------------------
