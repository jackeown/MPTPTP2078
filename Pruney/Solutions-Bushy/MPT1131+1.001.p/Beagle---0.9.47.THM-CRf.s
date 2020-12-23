%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1131+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:27 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 424 expanded)
%              Number of leaves         :   30 ( 166 expanded)
%              Depth                    :   11
%              Number of atoms          :  267 (2151 expanded)
%              Number of equality atoms :   11 ( 172 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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
                      & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B)))) )
                   => ( C = D
                     => ( v5_pre_topc(C,A,B)
                      <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_29] :
      ( m1_subset_1(u1_pre_topc(A_29),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29))))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    ! [A_49,B_50] :
      ( l1_pre_topc(g1_pre_topc(A_49,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    ! [A_29] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_29),u1_pre_topc(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_16,c_68])).

tff(c_28,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,
    ( ~ v5_pre_topc('#skF_5',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_58,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50])).

tff(c_80,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_93,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k8_relset_1(A_59,B_60,C_61,D_62) = k10_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_103,plain,(
    ! [D_62] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_62) = k10_relat_1('#skF_4',D_62) ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_224,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_108),u1_struct_0(B_109),C_110,'#skF_1'(A_108,B_109,C_110)),A_108)
      | v5_pre_topc(C_110,A_108,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc(B_109)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_236,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_224])).

tff(c_241,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_36,c_236])).

tff(c_242,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_241])).

tff(c_192,plain,(
    ! [A_102,B_103,C_104] :
      ( v4_pre_topc('#skF_1'(A_102,B_103,C_104),B_103)
      | v5_pre_topc(C_104,A_102,B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(B_103))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ v1_funct_1(C_104)
      | ~ l1_pre_topc(B_103)
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_199,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_192])).

tff(c_206,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_199])).

tff(c_207,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_206])).

tff(c_208,plain,(
    ! [A_105,B_106,C_107] :
      ( m1_subset_1('#skF_1'(A_105,B_106,C_107),k1_zfmisc_1(u1_struct_0(B_106)))
      | v5_pre_topc(C_107,A_105,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),u1_struct_0(B_106))))
      | ~ v1_funct_2(C_107,u1_struct_0(A_105),u1_struct_0(B_106))
      | ~ v1_funct_1(C_107)
      | ~ l1_pre_topc(B_106)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_215,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_208])).

tff(c_222,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_215])).

tff(c_223,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_222])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_56,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_5',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_57,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56])).

tff(c_81,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_57])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_61,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_102,plain,(
    ! [D_62] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_62) = k10_relat_1('#skF_4',D_62) ),
    inference(resolution,[status(thm)],[c_61,c_93])).

tff(c_243,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_111),u1_struct_0(B_112),C_113,D_114),A_111)
      | ~ v4_pre_topc(D_114,B_112)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0(B_112)))
      | ~ v5_pre_topc(C_113,A_111,B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,u1_struct_0(A_111),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_248,plain,(
    ! [D_114] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_114),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_114,'#skF_3')
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_61,c_243])).

tff(c_254,plain,(
    ! [D_114] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_114),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_114,'#skF_3')
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_60,c_81,c_102,c_248])).

tff(c_258,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_261,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_258])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_261])).

tff(c_268,plain,(
    ! [D_115] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_115),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_115,'#skF_3')
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_119,plain,(
    ! [D_65] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_65) = k10_relat_1('#skF_4',D_65) ),
    inference(resolution,[status(thm)],[c_61,c_93])).

tff(c_14,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( m1_subset_1(k8_relset_1(A_25,B_26,C_27,D_28),k1_zfmisc_1(A_25))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    ! [D_65] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_65),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_14])).

tff(c_131,plain,(
    ! [D_65] : m1_subset_1(k10_relat_1('#skF_4',D_65),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_125])).

tff(c_146,plain,(
    ! [B_79,A_80] :
      ( v4_pre_topc(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_80),u1_pre_topc(A_80)))))
      | ~ v4_pre_topc(B_79,g1_pre_topc(u1_struct_0(A_80),u1_pre_topc(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_152,plain,(
    ! [D_65] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_65),'#skF_2')
      | ~ v4_pre_topc(k10_relat_1('#skF_4',D_65),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_131,c_146])).

tff(c_160,plain,(
    ! [D_65] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_65),'#skF_2')
      | ~ v4_pre_topc(k10_relat_1('#skF_4',D_65),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_152])).

tff(c_284,plain,(
    ! [D_120] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_120),'#skF_2')
      | ~ v4_pre_topc(D_120,'#skF_3')
      | ~ m1_subset_1(D_120,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_268,c_160])).

tff(c_287,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_223,c_284])).

tff(c_294,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_287])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_294])).

tff(c_297,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_405,plain,(
    ! [A_156,B_157,C_158] :
      ( v4_pre_topc('#skF_1'(A_156,B_157,C_158),B_157)
      | v5_pre_topc(C_158,A_156,B_157)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0(A_156),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_pre_topc(B_157)
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_410,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_61,c_405])).

tff(c_416,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_60,c_410])).

tff(c_417,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_416])).

tff(c_421,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_424,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_421])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_424])).

tff(c_429,plain,(
    v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_430,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_437,plain,(
    ! [A_171,B_172,C_173] :
      ( m1_subset_1('#skF_1'(A_171,B_172,C_173),k1_zfmisc_1(u1_struct_0(B_172)))
      | v5_pre_topc(C_173,A_171,B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0(B_172))))
      | ~ v1_funct_2(C_173,u1_struct_0(A_171),u1_struct_0(B_172))
      | ~ v1_funct_1(C_173)
      | ~ l1_pre_topc(B_172)
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_442,plain,
    ( m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_61,c_437])).

tff(c_448,plain,
    ( m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_42,c_40,c_60,c_442])).

tff(c_449,plain,(
    m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_448])).

tff(c_298,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_312,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k8_relset_1(A_125,B_126,C_127,D_128) = k10_relat_1(C_127,D_128)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_322,plain,(
    ! [D_128] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_128) = k10_relat_1('#skF_4',D_128) ),
    inference(resolution,[status(thm)],[c_36,c_312])).

tff(c_472,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_177),u1_struct_0(B_178),C_179,D_180),A_177)
      | ~ v4_pre_topc(D_180,B_178)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(u1_struct_0(B_178)))
      | ~ v5_pre_topc(C_179,A_177,B_178)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177),u1_struct_0(B_178))))
      | ~ v1_funct_2(C_179,u1_struct_0(A_177),u1_struct_0(B_178))
      | ~ v1_funct_1(C_179)
      | ~ l1_pre_topc(B_178)
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_479,plain,(
    ! [D_180] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_180),'#skF_2')
      | ~ v4_pre_topc(D_180,'#skF_3')
      | ~ m1_subset_1(D_180,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_472])).

tff(c_487,plain,(
    ! [D_181] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_181),'#skF_2')
      | ~ v4_pre_topc(D_181,'#skF_3')
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_298,c_322,c_479])).

tff(c_490,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_449,c_487])).

tff(c_497,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_490])).

tff(c_323,plain,(
    ! [D_129] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_129) = k10_relat_1('#skF_4',D_129) ),
    inference(resolution,[status(thm)],[c_36,c_312])).

tff(c_329,plain,(
    ! [D_129] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_129),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_14])).

tff(c_335,plain,(
    ! [D_129] : m1_subset_1(k10_relat_1('#skF_4',D_129),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_329])).

tff(c_22,plain,(
    ! [B_36,A_34] :
      ( v4_pre_topc(B_36,g1_pre_topc(u1_struct_0(A_34),u1_pre_topc(A_34)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ v4_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_321,plain,(
    ! [D_128] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_128) = k10_relat_1('#skF_4',D_128) ),
    inference(resolution,[status(thm)],[c_61,c_312])).

tff(c_453,plain,(
    ! [A_174,B_175,C_176] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_174),u1_struct_0(B_175),C_176,'#skF_1'(A_174,B_175,C_176)),A_174)
      | v5_pre_topc(C_176,A_174,B_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174),u1_struct_0(B_175))))
      | ~ v1_funct_2(C_176,u1_struct_0(A_174),u1_struct_0(B_175))
      | ~ v1_funct_1(C_176)
      | ~ l1_pre_topc(B_175)
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_457,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_453])).

tff(c_467,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_42,c_40,c_60,c_61,c_457])).

tff(c_468,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_467])).

tff(c_501,plain,
    ( ~ m1_subset_1(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_468])).

tff(c_505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_497,c_335,c_501])).

%------------------------------------------------------------------------------
