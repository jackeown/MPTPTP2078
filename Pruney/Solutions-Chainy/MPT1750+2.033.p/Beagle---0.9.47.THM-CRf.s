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
% DateTime   : Thu Dec  3 10:26:56 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 557 expanded)
%              Number of leaves         :   44 ( 203 expanded)
%              Depth                    :   19
%              Number of atoms          :  241 (1977 expanded)
%              Number of equality atoms :   35 ( 216 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_22,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_75,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_75])).

tff(c_81,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_91,plain,(
    ! [C_71,A_72,B_73] :
      ( v4_relat_1(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_95,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_91])).

tff(c_103,plain,(
    ! [B_77,A_78] :
      ( k1_relat_1(B_77) = A_78
      | ~ v1_partfun1(B_77,A_78)
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_106,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_103])).

tff(c_109,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_106])).

tff(c_110,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_154,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_partfun1(C_96,A_97)
      | ~ v1_funct_2(C_96,A_97,B_98)
      | ~ v1_funct_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | v1_xboole_0(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_157,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_154])).

tff(c_160,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_157])).

tff(c_161,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_160])).

tff(c_26,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_164,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_161,c_26])).

tff(c_167,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_164])).

tff(c_170,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_167])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_170])).

tff(c_175,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_180,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_44])).

tff(c_179,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_42])).

tff(c_375,plain,(
    ! [C_128,F_127,B_125,A_126,D_124] :
      ( r1_funct_2(A_126,B_125,C_128,D_124,F_127,F_127)
      | ~ m1_subset_1(F_127,k1_zfmisc_1(k2_zfmisc_1(C_128,D_124)))
      | ~ v1_funct_2(F_127,C_128,D_124)
      | ~ m1_subset_1(F_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2(F_127,A_126,B_125)
      | ~ v1_funct_1(F_127)
      | v1_xboole_0(D_124)
      | v1_xboole_0(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_377,plain,(
    ! [A_126,B_125] :
      ( r1_funct_2(A_126,B_125,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2('#skF_4',A_126,B_125)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_125) ) ),
    inference(resolution,[status(thm)],[c_179,c_375])).

tff(c_380,plain,(
    ! [A_126,B_125] :
      ( r1_funct_2(A_126,B_125,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2('#skF_4',A_126,B_125)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_180,c_377])).

tff(c_381,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_384,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_381,c_26])).

tff(c_387,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_384])).

tff(c_391,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_387])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_391])).

tff(c_397,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_396,plain,(
    ! [A_126,B_125] :
      ( r1_funct_2(A_126,B_125,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2('#skF_4',A_126,B_125)
      | v1_xboole_0(B_125) ) ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_24,plain,(
    ! [A_21] :
      ( m1_subset_1(u1_pre_topc(A_21),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21))))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_187,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_24])).

tff(c_196,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_187])).

tff(c_40,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_178,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_40])).

tff(c_263,plain,(
    ! [C_103,A_104,D_105,B_106] :
      ( C_103 = A_104
      | g1_pre_topc(C_103,D_105) != g1_pre_topc(A_104,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_283,plain,(
    ! [A_112,B_113] :
      ( u1_struct_0('#skF_3') = A_112
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(A_112))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_263])).

tff(c_290,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_283])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_268,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k2_partfun1(A_107,B_108,C_109,D_110) = k7_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_270,plain,(
    ! [D_110] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_110) = k7_relat_1('#skF_4',D_110)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_179,c_268])).

tff(c_273,plain,(
    ! [D_110] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_110) = k7_relat_1('#skF_4',D_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_270])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_407,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k2_partfun1(u1_struct_0(A_143),u1_struct_0(B_144),C_145,u1_struct_0(D_146)) = k2_tmap_1(A_143,B_144,C_145,D_146)
      | ~ m1_pre_topc(D_146,A_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_143),u1_struct_0(B_144))))
      | ~ v1_funct_2(C_145,u1_struct_0(A_143),u1_struct_0(B_144))
      | ~ v1_funct_1(C_145)
      | ~ l1_pre_topc(B_144)
      | ~ v2_pre_topc(B_144)
      | v2_struct_0(B_144)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_413,plain,(
    ! [B_144,C_145,D_146] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_144),C_145,u1_struct_0(D_146)) = k2_tmap_1('#skF_2',B_144,C_145,D_146)
      | ~ m1_pre_topc(D_146,'#skF_2')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_144))))
      | ~ v1_funct_2(C_145,u1_struct_0('#skF_2'),u1_struct_0(B_144))
      | ~ v1_funct_1(C_145)
      | ~ l1_pre_topc(B_144)
      | ~ v2_pre_topc(B_144)
      | v2_struct_0(B_144)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_407])).

tff(c_421,plain,(
    ! [B_144,C_145,D_146] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_144),C_145,u1_struct_0(D_146)) = k2_tmap_1('#skF_2',B_144,C_145,D_146)
      | ~ m1_pre_topc(D_146,'#skF_2')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_144))))
      | ~ v1_funct_2(C_145,k1_relat_1('#skF_4'),u1_struct_0(B_144))
      | ~ v1_funct_1(C_145)
      | ~ l1_pre_topc(B_144)
      | ~ v2_pre_topc(B_144)
      | v2_struct_0(B_144)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_175,c_175,c_413])).

tff(c_426,plain,(
    ! [B_147,C_148,D_149] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_147),C_148,u1_struct_0(D_149)) = k2_tmap_1('#skF_2',B_147,C_148,D_149)
      | ~ m1_pre_topc(D_149,'#skF_2')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_147))))
      | ~ v1_funct_2(C_148,k1_relat_1('#skF_4'),u1_struct_0(B_147))
      | ~ v1_funct_1(C_148)
      | ~ l1_pre_topc(B_147)
      | ~ v2_pre_topc(B_147)
      | v2_struct_0(B_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_421])).

tff(c_430,plain,(
    ! [D_149] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_149)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_149)
      | ~ m1_pre_topc(D_149,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_179,c_426])).

tff(c_437,plain,(
    ! [D_149] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_149)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_149)
      | ~ m1_pre_topc(D_149,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_46,c_180,c_273,c_430])).

tff(c_442,plain,(
    ! [D_150] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_150)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_150)
      | ~ m1_pre_topc(D_150,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_437])).

tff(c_451,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_442])).

tff(c_458,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_451])).

tff(c_6,plain,(
    ! [A_6] :
      ( k7_relat_1(A_6,k1_relat_1(A_6)) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_462,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_6])).

tff(c_469,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_462])).

tff(c_38,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_199,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_38])).

tff(c_303,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_199])).

tff(c_474,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_303])).

tff(c_508,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_396,c_474])).

tff(c_511,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_179,c_508])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.43  
% 2.99/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.43  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.99/1.43  
% 2.99/1.43  %Foreground sorts:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Background operators:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Foreground operators:
% 2.99/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.99/1.43  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.99/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.43  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.99/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.99/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.99/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.99/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.99/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.43  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.99/1.43  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.99/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.99/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.99/1.43  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.99/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.43  
% 3.12/1.45  tff(f_179, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.12/1.45  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.12/1.45  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.12/1.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.12/1.45  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.12/1.45  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.12/1.45  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.12/1.45  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.12/1.45  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.12/1.45  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.12/1.45  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.12/1.45  tff(f_72, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.12/1.45  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.12/1.45  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 3.12/1.45  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_22, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.12/1.45  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.12/1.45  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_75, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.45  tff(c_78, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_75])).
% 3.12/1.45  tff(c_81, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_78])).
% 3.12/1.45  tff(c_91, plain, (![C_71, A_72, B_73]: (v4_relat_1(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.12/1.45  tff(c_95, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_91])).
% 3.12/1.45  tff(c_103, plain, (![B_77, A_78]: (k1_relat_1(B_77)=A_78 | ~v1_partfun1(B_77, A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.12/1.45  tff(c_106, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_95, c_103])).
% 3.12/1.45  tff(c_109, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_106])).
% 3.12/1.45  tff(c_110, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_109])).
% 3.12/1.45  tff(c_44, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_154, plain, (![C_96, A_97, B_98]: (v1_partfun1(C_96, A_97) | ~v1_funct_2(C_96, A_97, B_98) | ~v1_funct_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | v1_xboole_0(B_98))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.45  tff(c_157, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_154])).
% 3.12/1.45  tff(c_160, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_157])).
% 3.12/1.45  tff(c_161, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_110, c_160])).
% 3.12/1.45  tff(c_26, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.12/1.45  tff(c_164, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_161, c_26])).
% 3.12/1.45  tff(c_167, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_164])).
% 3.12/1.45  tff(c_170, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_167])).
% 3.12/1.45  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_170])).
% 3.12/1.45  tff(c_175, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_109])).
% 3.12/1.45  tff(c_180, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_44])).
% 3.12/1.45  tff(c_179, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_42])).
% 3.12/1.45  tff(c_375, plain, (![C_128, F_127, B_125, A_126, D_124]: (r1_funct_2(A_126, B_125, C_128, D_124, F_127, F_127) | ~m1_subset_1(F_127, k1_zfmisc_1(k2_zfmisc_1(C_128, D_124))) | ~v1_funct_2(F_127, C_128, D_124) | ~m1_subset_1(F_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2(F_127, A_126, B_125) | ~v1_funct_1(F_127) | v1_xboole_0(D_124) | v1_xboole_0(B_125))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.12/1.45  tff(c_377, plain, (![A_126, B_125]: (r1_funct_2(A_126, B_125, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2('#skF_4', A_126, B_125) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_125))), inference(resolution, [status(thm)], [c_179, c_375])).
% 3.12/1.45  tff(c_380, plain, (![A_126, B_125]: (r1_funct_2(A_126, B_125, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2('#skF_4', A_126, B_125) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_180, c_377])).
% 3.12/1.45  tff(c_381, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_380])).
% 3.12/1.45  tff(c_384, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_381, c_26])).
% 3.12/1.45  tff(c_387, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_384])).
% 3.12/1.45  tff(c_391, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_387])).
% 3.12/1.45  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_391])).
% 3.12/1.45  tff(c_397, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_380])).
% 3.12/1.45  tff(c_396, plain, (![A_126, B_125]: (r1_funct_2(A_126, B_125, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2('#skF_4', A_126, B_125) | v1_xboole_0(B_125))), inference(splitRight, [status(thm)], [c_380])).
% 3.12/1.45  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_24, plain, (![A_21]: (m1_subset_1(u1_pre_topc(A_21), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21)))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.12/1.45  tff(c_187, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_175, c_24])).
% 3.12/1.45  tff(c_196, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_187])).
% 3.12/1.45  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_178, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_40])).
% 3.12/1.45  tff(c_263, plain, (![C_103, A_104, D_105, B_106]: (C_103=A_104 | g1_pre_topc(C_103, D_105)!=g1_pre_topc(A_104, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.45  tff(c_283, plain, (![A_112, B_113]: (u1_struct_0('#skF_3')=A_112 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(A_112))))), inference(superposition, [status(thm), theory('equality')], [c_178, c_263])).
% 3.12/1.45  tff(c_290, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_196, c_283])).
% 3.12/1.45  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_268, plain, (![A_107, B_108, C_109, D_110]: (k2_partfun1(A_107, B_108, C_109, D_110)=k7_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(C_109))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.12/1.45  tff(c_270, plain, (![D_110]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_110)=k7_relat_1('#skF_4', D_110) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_179, c_268])).
% 3.12/1.45  tff(c_273, plain, (![D_110]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_110)=k7_relat_1('#skF_4', D_110))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_270])).
% 3.12/1.45  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_407, plain, (![A_143, B_144, C_145, D_146]: (k2_partfun1(u1_struct_0(A_143), u1_struct_0(B_144), C_145, u1_struct_0(D_146))=k2_tmap_1(A_143, B_144, C_145, D_146) | ~m1_pre_topc(D_146, A_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_143), u1_struct_0(B_144)))) | ~v1_funct_2(C_145, u1_struct_0(A_143), u1_struct_0(B_144)) | ~v1_funct_1(C_145) | ~l1_pre_topc(B_144) | ~v2_pre_topc(B_144) | v2_struct_0(B_144) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.12/1.45  tff(c_413, plain, (![B_144, C_145, D_146]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_144), C_145, u1_struct_0(D_146))=k2_tmap_1('#skF_2', B_144, C_145, D_146) | ~m1_pre_topc(D_146, '#skF_2') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_144)))) | ~v1_funct_2(C_145, u1_struct_0('#skF_2'), u1_struct_0(B_144)) | ~v1_funct_1(C_145) | ~l1_pre_topc(B_144) | ~v2_pre_topc(B_144) | v2_struct_0(B_144) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_407])).
% 3.12/1.45  tff(c_421, plain, (![B_144, C_145, D_146]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_144), C_145, u1_struct_0(D_146))=k2_tmap_1('#skF_2', B_144, C_145, D_146) | ~m1_pre_topc(D_146, '#skF_2') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_144)))) | ~v1_funct_2(C_145, k1_relat_1('#skF_4'), u1_struct_0(B_144)) | ~v1_funct_1(C_145) | ~l1_pre_topc(B_144) | ~v2_pre_topc(B_144) | v2_struct_0(B_144) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_175, c_175, c_413])).
% 3.12/1.45  tff(c_426, plain, (![B_147, C_148, D_149]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_147), C_148, u1_struct_0(D_149))=k2_tmap_1('#skF_2', B_147, C_148, D_149) | ~m1_pre_topc(D_149, '#skF_2') | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_147)))) | ~v1_funct_2(C_148, k1_relat_1('#skF_4'), u1_struct_0(B_147)) | ~v1_funct_1(C_148) | ~l1_pre_topc(B_147) | ~v2_pre_topc(B_147) | v2_struct_0(B_147))), inference(negUnitSimplification, [status(thm)], [c_56, c_421])).
% 3.12/1.45  tff(c_430, plain, (![D_149]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_149))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_149) | ~m1_pre_topc(D_149, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_179, c_426])).
% 3.12/1.45  tff(c_437, plain, (![D_149]: (k7_relat_1('#skF_4', u1_struct_0(D_149))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_149) | ~m1_pre_topc(D_149, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_46, c_180, c_273, c_430])).
% 3.12/1.45  tff(c_442, plain, (![D_150]: (k7_relat_1('#skF_4', u1_struct_0(D_150))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_150) | ~m1_pre_topc(D_150, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_437])).
% 3.12/1.45  tff(c_451, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_290, c_442])).
% 3.12/1.45  tff(c_458, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_451])).
% 3.12/1.45  tff(c_6, plain, (![A_6]: (k7_relat_1(A_6, k1_relat_1(A_6))=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.12/1.45  tff(c_462, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_458, c_6])).
% 3.12/1.45  tff(c_469, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_462])).
% 3.12/1.45  tff(c_38, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.12/1.45  tff(c_199, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_38])).
% 3.12/1.45  tff(c_303, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_199])).
% 3.12/1.45  tff(c_474, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_303])).
% 3.12/1.45  tff(c_508, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_396, c_474])).
% 3.12/1.45  tff(c_511, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_179, c_508])).
% 3.12/1.45  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_511])).
% 3.12/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.45  
% 3.12/1.45  Inference rules
% 3.12/1.45  ----------------------
% 3.12/1.45  #Ref     : 6
% 3.12/1.45  #Sup     : 87
% 3.12/1.45  #Fact    : 0
% 3.12/1.45  #Define  : 0
% 3.12/1.45  #Split   : 4
% 3.12/1.45  #Chain   : 0
% 3.12/1.45  #Close   : 0
% 3.12/1.45  
% 3.12/1.45  Ordering : KBO
% 3.12/1.45  
% 3.12/1.45  Simplification rules
% 3.12/1.45  ----------------------
% 3.12/1.45  #Subsume      : 8
% 3.12/1.45  #Demod        : 97
% 3.12/1.45  #Tautology    : 47
% 3.12/1.45  #SimpNegUnit  : 16
% 3.12/1.45  #BackRed      : 11
% 3.12/1.45  
% 3.12/1.45  #Partial instantiations: 0
% 3.12/1.45  #Strategies tried      : 1
% 3.12/1.45  
% 3.12/1.45  Timing (in seconds)
% 3.12/1.45  ----------------------
% 3.12/1.45  Preprocessing        : 0.37
% 3.12/1.45  Parsing              : 0.19
% 3.12/1.45  CNF conversion       : 0.03
% 3.12/1.45  Main loop            : 0.31
% 3.12/1.45  Inferencing          : 0.10
% 3.12/1.45  Reduction            : 0.10
% 3.12/1.45  Demodulation         : 0.07
% 3.12/1.45  BG Simplification    : 0.02
% 3.12/1.45  Subsumption          : 0.05
% 3.12/1.46  Abstraction          : 0.01
% 3.12/1.46  MUC search           : 0.00
% 3.12/1.46  Cooper               : 0.00
% 3.12/1.46  Total                : 0.72
% 3.12/1.46  Index Insertion      : 0.00
% 3.12/1.46  Index Deletion       : 0.00
% 3.12/1.46  Index Matching       : 0.00
% 3.12/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
