%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:11 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 549 expanded)
%              Number of leaves         :   29 ( 209 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (2889 expanded)
%              Number of equality atoms :    9 ( 225 expanded)
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

tff(f_103,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_50,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(c_26,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_5','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_55,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54])).

tff(c_78,plain,(
    v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_48,plain,
    ( ~ v5_pre_topc('#skF_5','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_48])).

tff(c_80,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_81,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k8_relset_1(A_51,B_52,C_53,D_54) = k10_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [D_54] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_54) = k10_relat_1('#skF_4',D_54) ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_142,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_71),u1_struct_0(B_72),C_73,'#skF_1'(A_71,B_72,C_73)),A_71)
      | v5_pre_topc(C_73,A_71,B_72)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71),u1_struct_0(B_72))))
      | ~ v1_funct_2(C_73,u1_struct_0(A_71),u1_struct_0(B_72))
      | ~ v1_funct_1(C_73)
      | ~ l1_pre_topc(B_72)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_154,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_142])).

tff(c_159,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_34,c_154])).

tff(c_160,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_159])).

tff(c_118,plain,(
    ! [A_65,B_66,C_67] :
      ( v4_pre_topc('#skF_1'(A_65,B_66,C_67),B_66)
      | v5_pre_topc(C_67,A_65,B_66)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65),u1_struct_0(B_66))))
      | ~ v1_funct_2(C_67,u1_struct_0(A_65),u1_struct_0(B_66))
      | ~ v1_funct_1(C_67)
      | ~ l1_pre_topc(B_66)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_128,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_122])).

tff(c_129,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_128])).

tff(c_130,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1('#skF_1'(A_68,B_69,C_70),k1_zfmisc_1(u1_struct_0(B_69)))
      | v5_pre_topc(C_70,A_68,B_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(B_69))))
      | ~ v1_funct_2(C_70,u1_struct_0(A_68),u1_struct_0(B_69))
      | ~ v1_funct_1(C_70)
      | ~ l1_pre_topc(B_69)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_134,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_130])).

tff(c_140,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_134])).

tff(c_141,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_140])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [B_32,A_30] :
      ( v4_pre_topc(B_32,g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ v4_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ v4_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_67,plain,(
    ! [A_48] :
      ( m1_subset_1(u1_pre_topc(A_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_48))))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_27,B_28] :
      ( l1_pre_topc(g1_pre_topc(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    ! [A_48] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_48),u1_pre_topc(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_67,c_12])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_59,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_86,plain,(
    ! [D_54] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_54) = k10_relat_1('#skF_4',D_54) ),
    inference(resolution,[status(thm)],[c_59,c_81])).

tff(c_161,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_74),u1_struct_0(B_75),C_76,D_77),A_74)
      | ~ v4_pre_topc(D_77,B_75)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(u1_struct_0(B_75)))
      | ~ v5_pre_topc(C_76,A_74,B_75)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74),u1_struct_0(B_75))))
      | ~ v1_funct_2(C_76,u1_struct_0(A_74),u1_struct_0(B_75))
      | ~ v1_funct_1(C_76)
      | ~ l1_pre_topc(B_75)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [D_77] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_77),'#skF_2')
      | ~ v4_pre_topc(D_77,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_77,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_59,c_161])).

tff(c_168,plain,(
    ! [D_77] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_77),'#skF_2')
      | ~ v4_pre_topc(D_77,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_77,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_58,c_78,c_86,c_163])).

tff(c_172,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_175,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_175])).

tff(c_182,plain,(
    ! [D_78] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_78),'#skF_2')
      | ~ v4_pre_topc(D_78,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_78,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_186,plain,(
    ! [B_32] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_32),'#skF_2')
      | ~ v4_pre_topc(B_32,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_32,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_182])).

tff(c_190,plain,(
    ! [B_79] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_79),'#skF_2')
      | ~ v4_pre_topc(B_79,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_79,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_186])).

tff(c_194,plain,(
    ! [B_32] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_32),'#skF_2')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_32,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_190])).

tff(c_198,plain,(
    ! [B_80] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_80),'#skF_2')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_80,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_194])).

tff(c_201,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_198])).

tff(c_204,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_201])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_204])).

tff(c_207,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_210,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_56])).

tff(c_248,plain,(
    ! [A_95,B_96,C_97] :
      ( v4_pre_topc('#skF_1'(A_95,B_96,C_97),B_96)
      | v5_pre_topc(C_97,A_95,B_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95),u1_struct_0(B_96))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_95),u1_struct_0(B_96))
      | ~ v1_funct_1(C_97)
      | ~ l1_pre_topc(B_96)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_250,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_59,c_248])).

tff(c_255,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_58,c_250])).

tff(c_256,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_255])).

tff(c_260,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_263,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_263])).

tff(c_269,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_211,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k8_relset_1(A_81,B_82,C_83,D_84) = k10_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_216,plain,(
    ! [D_84] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_84) = k10_relat_1('#skF_4',D_84) ),
    inference(resolution,[status(thm)],[c_59,c_211])).

tff(c_294,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_101),u1_struct_0(B_102),C_103,'#skF_1'(A_101,B_102,C_103)),A_101)
      | v5_pre_topc(C_103,A_101,B_102)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101),u1_struct_0(B_102))))
      | ~ v1_funct_2(C_103,u1_struct_0(A_101),u1_struct_0(B_102))
      | ~ v1_funct_1(C_103)
      | ~ l1_pre_topc(B_102)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_302,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_294])).

tff(c_309,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_269,c_38,c_58,c_59,c_302])).

tff(c_310,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_309])).

tff(c_268,plain,(
    v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_270,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1('#skF_1'(A_98,B_99,C_100),k1_zfmisc_1(u1_struct_0(B_99)))
      | v5_pre_topc(C_100,A_98,B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),u1_struct_0(B_99))))
      | ~ v1_funct_2(C_100,u1_struct_0(A_98),u1_struct_0(B_99))
      | ~ v1_funct_1(C_100)
      | ~ l1_pre_topc(B_99)
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_272,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_59,c_270])).

tff(c_277,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_269,c_38,c_58,c_272])).

tff(c_278,plain,(
    m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_277])).

tff(c_24,plain,(
    ! [B_32,A_30] :
      ( v4_pre_topc(B_32,A_30)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))))
      | ~ v4_pre_topc(B_32,g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_287,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3')
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_24])).

tff(c_293,plain,(
    v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_268,c_287])).

tff(c_22,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))))
      | ~ v4_pre_topc(B_32,g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_284,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_22])).

tff(c_290,plain,(
    m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_268,c_284])).

tff(c_217,plain,(
    ! [D_84] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_84) = k10_relat_1('#skF_4',D_84) ),
    inference(resolution,[status(thm)],[c_34,c_211])).

tff(c_313,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_104),u1_struct_0(B_105),C_106,D_107),A_104)
      | ~ v4_pre_topc(D_107,B_105)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(u1_struct_0(B_105)))
      | ~ v5_pre_topc(C_106,A_104,B_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_104),u1_struct_0(B_105))))
      | ~ v1_funct_2(C_106,u1_struct_0(A_104),u1_struct_0(B_105))
      | ~ v1_funct_1(C_106)
      | ~ l1_pre_topc(B_105)
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_317,plain,(
    ! [D_107] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_107),'#skF_2')
      | ~ v4_pre_topc(D_107,'#skF_3')
      | ~ m1_subset_1(D_107,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_313])).

tff(c_324,plain,(
    ! [D_108] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_108),'#skF_2')
      | ~ v4_pre_topc(D_108,'#skF_3')
      | ~ m1_subset_1(D_108,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_207,c_217,c_317])).

tff(c_327,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_290,c_324])).

tff(c_330,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_327])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_310,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:40:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.39  
% 2.51/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.39  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.83/1.39  
% 2.83/1.39  %Foreground sorts:
% 2.83/1.39  
% 2.83/1.39  
% 2.83/1.39  %Background operators:
% 2.83/1.39  
% 2.83/1.39  
% 2.83/1.39  %Foreground operators:
% 2.83/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.83/1.39  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.83/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.39  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.83/1.39  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.83/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.39  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.83/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.39  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.83/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.39  
% 2.83/1.42  tff(f_103, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 2.83/1.42  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.83/1.42  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.83/1.42  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v4_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v4_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_pre_topc)).
% 2.83/1.42  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.83/1.42  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 2.83/1.42  tff(c_26, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_54, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v5_pre_topc('#skF_5', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_55, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54])).
% 2.83/1.42  tff(c_78, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_55])).
% 2.83/1.42  tff(c_48, plain, (~v5_pre_topc('#skF_5', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_56, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_48])).
% 2.83/1.42  tff(c_80, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_56])).
% 2.83/1.42  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_36, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_81, plain, (![A_51, B_52, C_53, D_54]: (k8_relset_1(A_51, B_52, C_53, D_54)=k10_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.42  tff(c_87, plain, (![D_54]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_54)=k10_relat_1('#skF_4', D_54))), inference(resolution, [status(thm)], [c_34, c_81])).
% 2.83/1.42  tff(c_142, plain, (![A_71, B_72, C_73]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_71), u1_struct_0(B_72), C_73, '#skF_1'(A_71, B_72, C_73)), A_71) | v5_pre_topc(C_73, A_71, B_72) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_71), u1_struct_0(B_72)))) | ~v1_funct_2(C_73, u1_struct_0(A_71), u1_struct_0(B_72)) | ~v1_funct_1(C_73) | ~l1_pre_topc(B_72) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.42  tff(c_154, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_87, c_142])).
% 2.83/1.42  tff(c_159, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_38, c_36, c_34, c_154])).
% 2.83/1.42  tff(c_160, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_80, c_159])).
% 2.83/1.42  tff(c_118, plain, (![A_65, B_66, C_67]: (v4_pre_topc('#skF_1'(A_65, B_66, C_67), B_66) | v5_pre_topc(C_67, A_65, B_66) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65), u1_struct_0(B_66)))) | ~v1_funct_2(C_67, u1_struct_0(A_65), u1_struct_0(B_66)) | ~v1_funct_1(C_67) | ~l1_pre_topc(B_66) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.42  tff(c_122, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_118])).
% 2.83/1.42  tff(c_128, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_38, c_36, c_122])).
% 2.83/1.42  tff(c_129, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_128])).
% 2.83/1.42  tff(c_130, plain, (![A_68, B_69, C_70]: (m1_subset_1('#skF_1'(A_68, B_69, C_70), k1_zfmisc_1(u1_struct_0(B_69))) | v5_pre_topc(C_70, A_68, B_69) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(B_69)))) | ~v1_funct_2(C_70, u1_struct_0(A_68), u1_struct_0(B_69)) | ~v1_funct_1(C_70) | ~l1_pre_topc(B_69) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.42  tff(c_134, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_130])).
% 2.83/1.42  tff(c_140, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_38, c_36, c_134])).
% 2.83/1.42  tff(c_141, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_80, c_140])).
% 2.83/1.42  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_20, plain, (![B_32, A_30]: (v4_pre_topc(B_32, g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~v4_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.42  tff(c_18, plain, (![B_32, A_30]: (m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~v4_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.42  tff(c_67, plain, (![A_48]: (m1_subset_1(u1_pre_topc(A_48), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_48)))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.83/1.42  tff(c_12, plain, (![A_27, B_28]: (l1_pre_topc(g1_pre_topc(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.83/1.42  tff(c_74, plain, (![A_48]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_48), u1_pre_topc(A_48))) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_67, c_12])).
% 2.83/1.42  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.83/1.42  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.42  tff(c_59, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 2.83/1.42  tff(c_86, plain, (![D_54]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_4', D_54)=k10_relat_1('#skF_4', D_54))), inference(resolution, [status(thm)], [c_59, c_81])).
% 2.83/1.42  tff(c_161, plain, (![A_74, B_75, C_76, D_77]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_74), u1_struct_0(B_75), C_76, D_77), A_74) | ~v4_pre_topc(D_77, B_75) | ~m1_subset_1(D_77, k1_zfmisc_1(u1_struct_0(B_75))) | ~v5_pre_topc(C_76, A_74, B_75) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74), u1_struct_0(B_75)))) | ~v1_funct_2(C_76, u1_struct_0(A_74), u1_struct_0(B_75)) | ~v1_funct_1(C_76) | ~l1_pre_topc(B_75) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.42  tff(c_163, plain, (![D_77]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_4', D_77), '#skF_2') | ~v4_pre_topc(D_77, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(D_77, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_59, c_161])).
% 2.83/1.42  tff(c_168, plain, (![D_77]: (v4_pre_topc(k10_relat_1('#skF_4', D_77), '#skF_2') | ~v4_pre_topc(D_77, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(D_77, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_58, c_78, c_86, c_163])).
% 2.83/1.42  tff(c_172, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_168])).
% 2.83/1.42  tff(c_175, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_74, c_172])).
% 2.83/1.42  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_175])).
% 2.83/1.42  tff(c_182, plain, (![D_78]: (v4_pre_topc(k10_relat_1('#skF_4', D_78), '#skF_2') | ~v4_pre_topc(D_78, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(D_78, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))))), inference(splitRight, [status(thm)], [c_168])).
% 2.83/1.42  tff(c_186, plain, (![B_32]: (v4_pre_topc(k10_relat_1('#skF_4', B_32), '#skF_2') | ~v4_pre_topc(B_32, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc(B_32, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_182])).
% 2.83/1.42  tff(c_190, plain, (![B_79]: (v4_pre_topc(k10_relat_1('#skF_4', B_79), '#skF_2') | ~v4_pre_topc(B_79, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc(B_79, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_186])).
% 2.83/1.42  tff(c_194, plain, (![B_32]: (v4_pre_topc(k10_relat_1('#skF_4', B_32), '#skF_2') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc(B_32, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_190])).
% 2.83/1.42  tff(c_198, plain, (![B_80]: (v4_pre_topc(k10_relat_1('#skF_4', B_80), '#skF_2') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc(B_80, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_194])).
% 2.83/1.42  tff(c_201, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | ~v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_141, c_198])).
% 2.83/1.42  tff(c_204, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_201])).
% 2.83/1.42  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_204])).
% 2.83/1.42  tff(c_207, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_55])).
% 2.83/1.42  tff(c_210, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_56])).
% 2.83/1.42  tff(c_248, plain, (![A_95, B_96, C_97]: (v4_pre_topc('#skF_1'(A_95, B_96, C_97), B_96) | v5_pre_topc(C_97, A_95, B_96) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95), u1_struct_0(B_96)))) | ~v1_funct_2(C_97, u1_struct_0(A_95), u1_struct_0(B_96)) | ~v1_funct_1(C_97) | ~l1_pre_topc(B_96) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.42  tff(c_250, plain, (v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_59, c_248])).
% 2.83/1.42  tff(c_255, plain, (v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_58, c_250])).
% 2.83/1.42  tff(c_256, plain, (v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_210, c_255])).
% 2.83/1.42  tff(c_260, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_256])).
% 2.83/1.42  tff(c_263, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_74, c_260])).
% 2.83/1.42  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_263])).
% 2.83/1.42  tff(c_269, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_256])).
% 2.83/1.42  tff(c_211, plain, (![A_81, B_82, C_83, D_84]: (k8_relset_1(A_81, B_82, C_83, D_84)=k10_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.42  tff(c_216, plain, (![D_84]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_4', D_84)=k10_relat_1('#skF_4', D_84))), inference(resolution, [status(thm)], [c_59, c_211])).
% 2.83/1.42  tff(c_294, plain, (![A_101, B_102, C_103]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_101), u1_struct_0(B_102), C_103, '#skF_1'(A_101, B_102, C_103)), A_101) | v5_pre_topc(C_103, A_101, B_102) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101), u1_struct_0(B_102)))) | ~v1_funct_2(C_103, u1_struct_0(A_101), u1_struct_0(B_102)) | ~v1_funct_1(C_103) | ~l1_pre_topc(B_102) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.42  tff(c_302, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), '#skF_2') | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_216, c_294])).
% 2.83/1.42  tff(c_309, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), '#skF_2') | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_269, c_38, c_58, c_59, c_302])).
% 2.83/1.42  tff(c_310, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_210, c_309])).
% 2.83/1.42  tff(c_268, plain, (v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_256])).
% 2.83/1.42  tff(c_270, plain, (![A_98, B_99, C_100]: (m1_subset_1('#skF_1'(A_98, B_99, C_100), k1_zfmisc_1(u1_struct_0(B_99))) | v5_pre_topc(C_100, A_98, B_99) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98), u1_struct_0(B_99)))) | ~v1_funct_2(C_100, u1_struct_0(A_98), u1_struct_0(B_99)) | ~v1_funct_1(C_100) | ~l1_pre_topc(B_99) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.42  tff(c_272, plain, (m1_subset_1('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_59, c_270])).
% 2.83/1.42  tff(c_277, plain, (m1_subset_1('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_269, c_38, c_58, c_272])).
% 2.83/1.42  tff(c_278, plain, (m1_subset_1('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(negUnitSimplification, [status(thm)], [c_210, c_277])).
% 2.83/1.42  tff(c_24, plain, (![B_32, A_30]: (v4_pre_topc(B_32, A_30) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))))) | ~v4_pre_topc(B_32, g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.42  tff(c_287, plain, (v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), '#skF_3') | ~v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_278, c_24])).
% 2.83/1.42  tff(c_293, plain, (v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_268, c_287])).
% 2.83/1.42  tff(c_22, plain, (![B_32, A_30]: (m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))))) | ~v4_pre_topc(B_32, g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.83/1.42  tff(c_284, plain, (m1_subset_1('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_278, c_22])).
% 2.83/1.42  tff(c_290, plain, (m1_subset_1('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_268, c_284])).
% 2.83/1.42  tff(c_217, plain, (![D_84]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_84)=k10_relat_1('#skF_4', D_84))), inference(resolution, [status(thm)], [c_34, c_211])).
% 2.83/1.42  tff(c_313, plain, (![A_104, B_105, C_106, D_107]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_104), u1_struct_0(B_105), C_106, D_107), A_104) | ~v4_pre_topc(D_107, B_105) | ~m1_subset_1(D_107, k1_zfmisc_1(u1_struct_0(B_105))) | ~v5_pre_topc(C_106, A_104, B_105) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_104), u1_struct_0(B_105)))) | ~v1_funct_2(C_106, u1_struct_0(A_104), u1_struct_0(B_105)) | ~v1_funct_1(C_106) | ~l1_pre_topc(B_105) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.42  tff(c_317, plain, (![D_107]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_107), '#skF_2') | ~v4_pre_topc(D_107, '#skF_3') | ~m1_subset_1(D_107, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_313])).
% 2.83/1.42  tff(c_324, plain, (![D_108]: (v4_pre_topc(k10_relat_1('#skF_4', D_108), '#skF_2') | ~v4_pre_topc(D_108, '#skF_3') | ~m1_subset_1(D_108, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_38, c_36, c_207, c_217, c_317])).
% 2.83/1.42  tff(c_327, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), '#skF_2') | ~v4_pre_topc('#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_290, c_324])).
% 2.83/1.42  tff(c_330, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_327])).
% 2.83/1.42  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_310, c_330])).
% 2.83/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.42  
% 2.83/1.42  Inference rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Ref     : 0
% 2.83/1.42  #Sup     : 46
% 2.83/1.42  #Fact    : 0
% 2.83/1.42  #Define  : 0
% 2.83/1.42  #Split   : 3
% 2.83/1.42  #Chain   : 0
% 2.83/1.42  #Close   : 0
% 2.83/1.42  
% 2.83/1.42  Ordering : KBO
% 2.83/1.42  
% 2.83/1.42  Simplification rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Subsume      : 4
% 2.83/1.42  #Demod        : 97
% 2.83/1.42  #Tautology    : 23
% 2.83/1.42  #SimpNegUnit  : 8
% 2.83/1.42  #BackRed      : 0
% 2.83/1.42  
% 2.83/1.42  #Partial instantiations: 0
% 2.83/1.42  #Strategies tried      : 1
% 2.83/1.42  
% 2.83/1.42  Timing (in seconds)
% 2.83/1.42  ----------------------
% 2.83/1.42  Preprocessing        : 0.37
% 2.83/1.42  Parsing              : 0.19
% 2.83/1.42  CNF conversion       : 0.03
% 2.83/1.42  Main loop            : 0.26
% 2.83/1.42  Inferencing          : 0.10
% 2.83/1.42  Reduction            : 0.09
% 2.83/1.42  Demodulation         : 0.06
% 2.83/1.42  BG Simplification    : 0.02
% 2.83/1.42  Subsumption          : 0.04
% 2.83/1.42  Abstraction          : 0.01
% 2.83/1.42  MUC search           : 0.00
% 2.83/1.42  Cooper               : 0.00
% 2.83/1.42  Total                : 0.68
% 2.83/1.42  Index Insertion      : 0.00
% 2.83/1.42  Index Deletion       : 0.00
% 2.83/1.42  Index Matching       : 0.00
% 2.83/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
