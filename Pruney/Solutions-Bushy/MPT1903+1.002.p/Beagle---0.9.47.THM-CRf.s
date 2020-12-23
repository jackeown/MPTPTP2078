%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1903+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:40 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 838 expanded)
%              Number of leaves         :   48 ( 315 expanded)
%              Depth                    :   19
%              Number of atoms          :  273 (2176 expanded)
%              Number of equality atoms :   41 ( 490 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v1_partfun1 > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_relat_1 > k6_partfun1 > k2_tex_1 > k1_zfmisc_1 > k1_tex_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tex_1,type,(
    k2_tex_1: $i > $i )).

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

tff(k1_tex_1,type,(
    k1_tex_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
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
                    & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                 => v5_pre_topc(C,B,A) ) )
         => v2_tdlat_3(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tex_2)).

tff(f_132,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v2_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( v4_pre_topc(B,A)
                & B != k1_xboole_0
                & B != u1_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tdlat_3)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_110,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( v1_pre_topc(k2_tex_1(A))
      & v2_pre_topc(k2_tex_1(A))
      & v2_tdlat_3(k2_tex_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_1)).

tff(f_67,axiom,(
    ! [A] : l1_pre_topc(k2_tex_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tex_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k1_tex_1(A),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_1)).

tff(f_63,axiom,(
    ! [A] : k2_tex_1(A) = g1_pre_topc(A,k1_tex_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ~ v2_struct_0(k2_tex_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_tex_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_114,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_61,axiom,(
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

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_290,plain,(
    ! [A_106] :
      ( '#skF_2'(A_106) != k1_xboole_0
      | v2_tdlat_3(A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_60,plain,(
    ~ v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_293,plain,
    ( '#skF_2'('#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_290,c_60])).

tff(c_296,plain,(
    '#skF_2'('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_293])).

tff(c_297,plain,(
    ! [A_107] :
      ( u1_struct_0(A_107) != '#skF_2'(A_107)
      | v2_tdlat_3(A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_300,plain,
    ( u1_struct_0('#skF_3') != '#skF_2'('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_297,c_60])).

tff(c_303,plain,(
    u1_struct_0('#skF_3') != '#skF_2'('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_300])).

tff(c_58,plain,(
    ! [A_45] :
      ( m1_subset_1('#skF_2'(A_45),k1_zfmisc_1(u1_struct_0(A_45)))
      | v2_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26,plain,(
    ! [A_31] :
      ( l1_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    ! [A_34] : v1_funct_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    ! [A_34] : v1_funct_1(k6_partfun1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_22,plain,(
    ! [A_30] : v1_partfun1(k6_partfun1(A_30),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_388,plain,(
    ! [C_132,A_133,B_134] :
      ( v1_funct_2(C_132,A_133,B_134)
      | ~ v1_partfun1(C_132,A_133)
      | ~ v1_funct_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_391,plain,(
    ! [A_30] :
      ( v1_funct_2(k6_partfun1(A_30),A_30,A_30)
      | ~ v1_partfun1(k6_partfun1(A_30),A_30)
      | ~ v1_funct_1(k6_partfun1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_24,c_388])).

tff(c_394,plain,(
    ! [A_30] : v1_funct_2(k6_partfun1(A_30),A_30,A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_22,c_391])).

tff(c_32,plain,(
    ! [A_33] : v2_pre_topc(k2_tex_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    ! [A_29] : l1_pre_topc(k2_tex_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_33] : v1_pre_topc(k2_tex_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_18,plain,(
    ! [A_28] : m1_subset_1(k1_tex_1(A_28),k1_zfmisc_1(k1_zfmisc_1(A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_27] : g1_pre_topc(A_27,k1_tex_1(A_27)) = k2_tex_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_360,plain,(
    ! [C_121,A_122,D_123,B_124] :
      ( C_121 = A_122
      | g1_pre_topc(C_121,D_123) != g1_pre_topc(A_122,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k1_zfmisc_1(A_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_368,plain,(
    ! [C_121,A_27,D_123] :
      ( C_121 = A_27
      | k2_tex_1(A_27) != g1_pre_topc(C_121,D_123)
      | ~ m1_subset_1(k1_tex_1(A_27),k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_360])).

tff(c_371,plain,(
    ! [C_125,A_126,D_127] :
      ( C_125 = A_126
      | k2_tex_1(A_126) != g1_pre_topc(C_125,D_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_368])).

tff(c_374,plain,(
    ! [A_1,A_126] :
      ( u1_struct_0(A_1) = A_126
      | k2_tex_1(A_126) != A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_371])).

tff(c_400,plain,(
    ! [A_126] :
      ( u1_struct_0(k2_tex_1(A_126)) = A_126
      | ~ v1_pre_topc(k2_tex_1(A_126))
      | ~ l1_pre_topc(k2_tex_1(A_126)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_374])).

tff(c_402,plain,(
    ! [A_126] : u1_struct_0(k2_tex_1(A_126)) = A_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_400])).

tff(c_404,plain,(
    ! [A_138] : u1_struct_0(k2_tex_1(A_138)) = A_138 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_400])).

tff(c_62,plain,(
    ! [C_54,B_52] :
      ( v5_pre_topc(C_54,B_52,'#skF_3')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_52),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_54,u1_struct_0(B_52),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_54)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_419,plain,(
    ! [C_54,A_138] :
      ( v5_pre_topc(C_54,k2_tex_1(A_138),'#skF_3')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_138,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_54,u1_struct_0(k2_tex_1(A_138)),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_54)
      | ~ l1_pre_topc(k2_tex_1(A_138))
      | ~ v2_pre_topc(k2_tex_1(A_138))
      | v2_struct_0(k2_tex_1(A_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_62])).

tff(c_497,plain,(
    ! [C_148,A_149] :
      ( v5_pre_topc(C_148,k2_tex_1(A_149),'#skF_3')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_148,A_149,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_148)
      | v2_struct_0(k2_tex_1(A_149)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_20,c_402,c_419])).

tff(c_501,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),k2_tex_1(u1_struct_0('#skF_3')),'#skF_3')
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | v2_struct_0(k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_24,c_497])).

tff(c_504,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),k2_tex_1(u1_struct_0('#skF_3')),'#skF_3')
    | v2_struct_0(k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_394,c_501])).

tff(c_513,plain,(
    v2_struct_0(k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_40,plain,(
    ! [A_35] :
      ( ~ v2_struct_0(k2_tex_1(A_35))
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_517,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_513,c_40])).

tff(c_28,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_520,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_517,c_28])).

tff(c_523,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_520])).

tff(c_541,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_523])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_541])).

tff(c_546,plain,(
    v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),k2_tex_1(u1_struct_0('#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_321,plain,(
    ! [A_112] :
      ( m1_subset_1('#skF_2'(A_112),k1_zfmisc_1(u1_struct_0(A_112)))
      | v2_tdlat_3(A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ! [A_43,B_44] :
      ( k8_relset_1(A_43,A_43,k6_partfun1(A_43),B_44) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_324,plain,(
    ! [A_112] :
      ( k8_relset_1(u1_struct_0(A_112),u1_struct_0(A_112),k6_partfun1(u1_struct_0(A_112)),'#skF_2'(A_112)) = '#skF_2'(A_112)
      | v2_tdlat_3(A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_321,c_48])).

tff(c_723,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_181),u1_struct_0(B_182),C_183,D_184),A_181)
      | ~ v4_pre_topc(D_184,B_182)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(u1_struct_0(B_182)))
      | ~ v5_pre_topc(C_183,A_181,B_182)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0(B_182))))
      | ~ v1_funct_2(C_183,u1_struct_0(A_181),u1_struct_0(B_182))
      | ~ v1_funct_1(C_183)
      | ~ l1_pre_topc(B_182)
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_725,plain,(
    ! [A_126,B_182,C_183,D_184] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(k2_tex_1(A_126)),u1_struct_0(B_182),C_183,D_184),k2_tex_1(A_126))
      | ~ v4_pre_topc(D_184,B_182)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(u1_struct_0(B_182)))
      | ~ v5_pre_topc(C_183,k2_tex_1(A_126),B_182)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_126,u1_struct_0(B_182))))
      | ~ v1_funct_2(C_183,u1_struct_0(k2_tex_1(A_126)),u1_struct_0(B_182))
      | ~ v1_funct_1(C_183)
      | ~ l1_pre_topc(B_182)
      | ~ l1_pre_topc(k2_tex_1(A_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_723])).

tff(c_1498,plain,(
    ! [A_270,B_271,C_272,D_273] :
      ( v4_pre_topc(k8_relset_1(A_270,u1_struct_0(B_271),C_272,D_273),k2_tex_1(A_270))
      | ~ v4_pre_topc(D_273,B_271)
      | ~ m1_subset_1(D_273,k1_zfmisc_1(u1_struct_0(B_271)))
      | ~ v5_pre_topc(C_272,k2_tex_1(A_270),B_271)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0(B_271))))
      | ~ v1_funct_2(C_272,A_270,u1_struct_0(B_271))
      | ~ v1_funct_1(C_272)
      | ~ l1_pre_topc(B_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_402,c_402,c_725])).

tff(c_1519,plain,(
    ! [A_112] :
      ( v4_pre_topc('#skF_2'(A_112),k2_tex_1(u1_struct_0(A_112)))
      | ~ v4_pre_topc('#skF_2'(A_112),A_112)
      | ~ m1_subset_1('#skF_2'(A_112),k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v5_pre_topc(k6_partfun1(u1_struct_0(A_112)),k2_tex_1(u1_struct_0(A_112)),A_112)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(A_112)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112),u1_struct_0(A_112))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_112)),u1_struct_0(A_112),u1_struct_0(A_112))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | v2_tdlat_3(A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_1498])).

tff(c_1534,plain,(
    ! [A_274] :
      ( v4_pre_topc('#skF_2'(A_274),k2_tex_1(u1_struct_0(A_274)))
      | ~ v4_pre_topc('#skF_2'(A_274),A_274)
      | ~ m1_subset_1('#skF_2'(A_274),k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ v5_pre_topc(k6_partfun1(u1_struct_0(A_274)),k2_tex_1(u1_struct_0(A_274)),A_274)
      | v2_tdlat_3(A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_394,c_24,c_1519])).

tff(c_1537,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_546,c_1534])).

tff(c_1546,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1537])).

tff(c_1547,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1546])).

tff(c_1552,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1547])).

tff(c_1555,plain,
    ( v2_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1552])).

tff(c_1558,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1555])).

tff(c_1560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1558])).

tff(c_1562,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1547])).

tff(c_56,plain,(
    ! [A_45] :
      ( v4_pre_topc('#skF_2'(A_45),A_45)
      | v2_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1561,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1547])).

tff(c_1573,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1561])).

tff(c_1576,plain,
    ( v2_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1573])).

tff(c_1579,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1576])).

tff(c_1581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1579])).

tff(c_1582,plain,(
    v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1561])).

tff(c_34,plain,(
    ! [A_33] : v2_tdlat_3(k2_tex_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_459,plain,(
    ! [A_141,B_142] :
      ( u1_struct_0(A_141) = B_142
      | k1_xboole_0 = B_142
      | ~ v4_pre_topc(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v2_tdlat_3(A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_462,plain,(
    ! [A_126,B_142] :
      ( u1_struct_0(k2_tex_1(A_126)) = B_142
      | k1_xboole_0 = B_142
      | ~ v4_pre_topc(B_142,k2_tex_1(A_126))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_126))
      | ~ v2_tdlat_3(k2_tex_1(A_126))
      | ~ l1_pre_topc(k2_tex_1(A_126))
      | ~ v2_pre_topc(k2_tex_1(A_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_459])).

tff(c_467,plain,(
    ! [B_142,A_126] :
      ( B_142 = A_126
      | k1_xboole_0 = B_142
      | ~ v4_pre_topc(B_142,k2_tex_1(A_126))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_126)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_20,c_34,c_402,c_462])).

tff(c_1586,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1582,c_467])).

tff(c_1589,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_1586])).

tff(c_1591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_303,c_1589])).

%------------------------------------------------------------------------------
