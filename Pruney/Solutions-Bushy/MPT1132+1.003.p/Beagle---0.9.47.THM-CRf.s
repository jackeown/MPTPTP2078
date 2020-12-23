%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1132+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:28 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 490 expanded)
%              Number of leaves         :   30 ( 190 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (2569 expanded)
%              Number of equality atoms :    9 ( 195 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                   => ( C = D
                     => ( v5_pre_topc(C,A,B)
                      <=> v5_pre_topc(D,A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_45,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(c_30,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,
    ( ~ v5_pre_topc('#skF_5','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52])).

tff(c_117,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_123,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k8_relset_1(A_62,B_63,C_64,D_65) = k10_relat_1(C_64,D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,(
    ! [D_65] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_65) = k10_relat_1('#skF_4',D_65) ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_258,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_98),u1_struct_0(B_99),C_100,'#skF_1'(A_98,B_99,C_100)),A_98)
      | v5_pre_topc(C_100,A_98,B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),u1_struct_0(B_99))))
      | ~ v1_funct_2(C_100,u1_struct_0(A_98),u1_struct_0(B_99))
      | ~ v1_funct_1(C_100)
      | ~ l1_pre_topc(B_99)
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_270,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_258])).

tff(c_275,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_40,c_38,c_270])).

tff(c_276,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_275])).

tff(c_198,plain,(
    ! [A_86,B_87,C_88] :
      ( v4_pre_topc('#skF_1'(A_86,B_87,C_88),B_87)
      | v5_pre_topc(C_88,A_86,B_87)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_86),u1_struct_0(B_87))))
      | ~ v1_funct_2(C_88,u1_struct_0(A_86),u1_struct_0(B_87))
      | ~ v1_funct_1(C_88)
      | ~ l1_pre_topc(B_87)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_202,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_198])).

tff(c_211,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_40,c_202])).

tff(c_212,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_211])).

tff(c_226,plain,(
    ! [A_92,B_93,C_94] :
      ( m1_subset_1('#skF_1'(A_92,B_93,C_94),k1_zfmisc_1(u1_struct_0(B_93)))
      | v5_pre_topc(C_94,A_92,B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0(B_93))))
      | ~ v1_funct_2(C_94,u1_struct_0(A_92),u1_struct_0(B_93))
      | ~ v1_funct_1(C_94)
      | ~ l1_pre_topc(B_93)
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_230,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_226])).

tff(c_239,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_40,c_230])).

tff(c_240,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_239])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    ! [B_34,A_32] :
      ( v4_pre_topc(B_34,g1_pre_topc(u1_struct_0(A_32),u1_pre_topc(A_32)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ v4_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [B_34,A_32] :
      ( m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_32),u1_pre_topc(A_32)))))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ v4_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_25] :
      ( m1_subset_1(u1_pre_topc(A_25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25))))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [A_56,B_57] :
      ( l1_pre_topc(g1_pre_topc(A_56,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    ! [A_25] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_25),u1_pre_topc(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_14,c_96])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_58,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_5','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_59,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_58])).

tff(c_122,plain,(
    v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_59])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_63,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_131,plain,(
    ! [D_65] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_65) = k10_relat_1('#skF_4',D_65) ),
    inference(resolution,[status(thm)],[c_63,c_123])).

tff(c_277,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_101),u1_struct_0(B_102),C_103,D_104),A_101)
      | ~ v4_pre_topc(D_104,B_102)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(B_102)))
      | ~ v5_pre_topc(C_103,A_101,B_102)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101),u1_struct_0(B_102))))
      | ~ v1_funct_2(C_103,u1_struct_0(A_101),u1_struct_0(B_102))
      | ~ v1_funct_1(C_103)
      | ~ l1_pre_topc(B_102)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_279,plain,(
    ! [D_104] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_104),'#skF_2')
      | ~ v4_pre_topc(D_104,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_63,c_277])).

tff(c_287,plain,(
    ! [D_104] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_104),'#skF_2')
      | ~ v4_pre_topc(D_104,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_62,c_122,c_131,c_279])).

tff(c_292,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_295,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_292])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_295])).

tff(c_302,plain,(
    ! [D_105] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_105),'#skF_2')
      | ~ v4_pre_topc(D_105,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_105,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ) ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_306,plain,(
    ! [B_34] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_34),'#skF_2')
      | ~ v4_pre_topc(B_34,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_34,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_302])).

tff(c_315,plain,(
    ! [B_106] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_106),'#skF_2')
      | ~ v4_pre_topc(B_106,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_106,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_306])).

tff(c_319,plain,(
    ! [B_34] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_34),'#skF_2')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_34,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_315])).

tff(c_323,plain,(
    ! [B_107] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_107),'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_107,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_319])).

tff(c_326,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_323])).

tff(c_333,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_326])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_333])).

tff(c_336,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_419,plain,(
    ! [A_132,B_133,C_134] :
      ( v4_pre_topc('#skF_1'(A_132,B_133,C_134),B_133)
      | v5_pre_topc(C_134,A_132,B_133)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0(A_132),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_421,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_419])).

tff(c_429,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_62,c_421])).

tff(c_430,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_429])).

tff(c_435,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_438,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_435])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_438])).

tff(c_444,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_344,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k8_relset_1(A_108,B_109,C_110,D_111) = k10_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_352,plain,(
    ! [D_111] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_111) = k10_relat_1('#skF_4',D_111) ),
    inference(resolution,[status(thm)],[c_63,c_344])).

tff(c_518,plain,(
    ! [A_144,B_145,C_146] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_144),u1_struct_0(B_145),C_146,'#skF_1'(A_144,B_145,C_146)),A_144)
      | v5_pre_topc(C_146,A_144,B_145)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_144),u1_struct_0(B_145))))
      | ~ v1_funct_2(C_146,u1_struct_0(A_144),u1_struct_0(B_145))
      | ~ v1_funct_1(C_146)
      | ~ l1_pre_topc(B_145)
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_526,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_518])).

tff(c_533,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_444,c_42,c_62,c_63,c_526])).

tff(c_534,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_533])).

tff(c_443,plain,(
    v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_445,plain,(
    ! [A_135,B_136,C_137] :
      ( m1_subset_1('#skF_1'(A_135,B_136,C_137),k1_zfmisc_1(u1_struct_0(B_136)))
      | v5_pre_topc(C_137,A_135,B_136)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_135),u1_struct_0(B_136))))
      | ~ v1_funct_2(C_137,u1_struct_0(A_135),u1_struct_0(B_136))
      | ~ v1_funct_1(C_137)
      | ~ l1_pre_topc(B_136)
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_447,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_445])).

tff(c_455,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_444,c_42,c_62,c_447])).

tff(c_456,plain,(
    m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_455])).

tff(c_28,plain,(
    ! [B_34,A_32] :
      ( v4_pre_topc(B_34,A_32)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_32),u1_pre_topc(A_32)))))
      | ~ v4_pre_topc(B_34,g1_pre_topc(u1_struct_0(A_32),u1_pre_topc(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_466,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3')
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_456,c_28])).

tff(c_475,plain,(
    v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_443,c_466])).

tff(c_26,plain,(
    ! [B_34,A_32] :
      ( m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_32),u1_pre_topc(A_32)))))
      | ~ v4_pre_topc(B_34,g1_pre_topc(u1_struct_0(A_32),u1_pre_topc(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_463,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_456,c_26])).

tff(c_472,plain,(
    m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_443,c_463])).

tff(c_337,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_353,plain,(
    ! [D_111] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_111) = k10_relat_1('#skF_4',D_111) ),
    inference(resolution,[status(thm)],[c_38,c_344])).

tff(c_537,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_147),u1_struct_0(B_148),C_149,D_150),A_147)
      | ~ v4_pre_topc(D_150,B_148)
      | ~ m1_subset_1(D_150,k1_zfmisc_1(u1_struct_0(B_148)))
      | ~ v5_pre_topc(C_149,A_147,B_148)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_147),u1_struct_0(B_148))))
      | ~ v1_funct_2(C_149,u1_struct_0(A_147),u1_struct_0(B_148))
      | ~ v1_funct_1(C_149)
      | ~ l1_pre_topc(B_148)
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_541,plain,(
    ! [D_150] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_150),'#skF_2')
      | ~ v4_pre_topc(D_150,'#skF_3')
      | ~ m1_subset_1(D_150,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_537])).

tff(c_552,plain,(
    ! [D_151] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_151),'#skF_2')
      | ~ v4_pre_topc(D_151,'#skF_3')
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_40,c_337,c_353,c_541])).

tff(c_555,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_472,c_552])).

tff(c_562,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_555])).

tff(c_564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_562])).

%------------------------------------------------------------------------------
