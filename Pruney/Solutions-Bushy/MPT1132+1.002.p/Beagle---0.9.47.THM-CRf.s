%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1132+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:27 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 515 expanded)
%              Number of leaves         :   31 ( 196 expanded)
%              Depth                    :   13
%              Number of atoms          :  312 (2637 expanded)
%              Number of equality atoms :   22 ( 210 expanded)
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

tff(f_117,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_51,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_57,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_32,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_5','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_61,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_60])).

tff(c_104,plain,(
    v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_54,plain,
    ( ~ v5_pre_topc('#skF_5','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_54])).

tff(c_117,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_62])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_136,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k8_relset_1(A_67,B_68,C_69,D_70) = k10_relat_1(C_69,D_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_142,plain,(
    ! [D_70] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_70) = k10_relat_1('#skF_4',D_70) ),
    inference(resolution,[status(thm)],[c_40,c_136])).

tff(c_564,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_117),u1_struct_0(B_118),C_119,'#skF_1'(A_117,B_118,C_119)),A_117)
      | v5_pre_topc(C_119,A_117,B_118)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117),u1_struct_0(B_118))))
      | ~ v1_funct_2(C_119,u1_struct_0(A_117),u1_struct_0(B_118))
      | ~ v1_funct_1(C_119)
      | ~ l1_pre_topc(B_118)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_582,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_564])).

tff(c_587,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_42,c_40,c_582])).

tff(c_588,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_587])).

tff(c_363,plain,(
    ! [A_105,B_106,C_107] :
      ( v4_pre_topc('#skF_1'(A_105,B_106,C_107),B_106)
      | v5_pre_topc(C_107,A_105,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),u1_struct_0(B_106))))
      | ~ v1_funct_2(C_107,u1_struct_0(A_105),u1_struct_0(B_106))
      | ~ v1_funct_1(C_107)
      | ~ l1_pre_topc(B_106)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_367,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_363])).

tff(c_373,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_42,c_367])).

tff(c_374,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_373])).

tff(c_470,plain,(
    ! [A_109,B_110,C_111] :
      ( m1_subset_1('#skF_1'(A_109,B_110,C_111),k1_zfmisc_1(u1_struct_0(B_110)))
      | v5_pre_topc(C_111,A_109,B_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109),u1_struct_0(B_110))))
      | ~ v1_funct_2(C_111,u1_struct_0(A_109),u1_struct_0(B_110))
      | ~ v1_funct_1(C_111)
      | ~ l1_pre_topc(B_110)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_478,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_470])).

tff(c_484,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_42,c_478])).

tff(c_485,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_484])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_26,plain,(
    ! [B_39,A_37] :
      ( v4_pre_topc(B_39,g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ v4_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ! [A_26] :
      ( m1_subset_1(u1_pre_topc(A_26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26))))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_72,plain,(
    ! [A_52,B_53] :
      ( l1_pre_topc(g1_pre_topc(A_52,B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    ! [A_26] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_26),u1_pre_topc(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_78,plain,(
    ! [A_55,B_56] :
      ( v1_pre_topc(g1_pre_topc(A_55,B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    ! [A_26] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_26),u1_pre_topc(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_16,c_78])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_122,plain,(
    ! [C_59,A_60,D_61,B_62] :
      ( C_59 = A_60
      | g1_pre_topc(C_59,D_61) != g1_pre_topc(A_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,(
    ! [A_1,A_60,B_62] :
      ( u1_struct_0(A_1) = A_60
      | g1_pre_topc(A_60,B_62) != A_1
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_60)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_215,plain,(
    ! [A_91,B_92] :
      ( u1_struct_0(g1_pre_topc(A_91,B_92)) = A_91
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91)))
      | ~ v1_pre_topc(g1_pre_topc(A_91,B_92))
      | ~ l1_pre_topc(g1_pre_topc(A_91,B_92)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_124])).

tff(c_341,plain,(
    ! [A_103] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_103),u1_pre_topc(A_103))) = u1_struct_0(A_103)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_103),u1_pre_topc(A_103)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_103),u1_pre_topc(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_16,c_215])).

tff(c_352,plain,(
    ! [A_104] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_104),u1_pre_topc(A_104))) = u1_struct_0(A_104)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_104),u1_pre_topc(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_82,c_341])).

tff(c_362,plain,(
    ! [A_26] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_26),u1_pre_topc(A_26))) = u1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_76,c_352])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_65,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_141,plain,(
    ! [D_70] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_70) = k10_relat_1('#skF_4',D_70) ),
    inference(resolution,[status(thm)],[c_65,c_136])).

tff(c_589,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_120),u1_struct_0(B_121),C_122,D_123),A_120)
      | ~ v4_pre_topc(D_123,B_121)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(u1_struct_0(B_121)))
      | ~ v5_pre_topc(C_122,A_120,B_121)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120),u1_struct_0(B_121))))
      | ~ v1_funct_2(C_122,u1_struct_0(A_120),u1_struct_0(B_121))
      | ~ v1_funct_1(C_122)
      | ~ l1_pre_topc(B_121)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_595,plain,(
    ! [D_123] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_123),'#skF_2')
      | ~ v4_pre_topc(D_123,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_123,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_65,c_589])).

tff(c_600,plain,(
    ! [D_123] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_123),'#skF_2')
      | ~ v4_pre_topc(D_123,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_123,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_64,c_104,c_141,c_595])).

tff(c_670,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_600])).

tff(c_676,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_670])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_676])).

tff(c_690,plain,(
    ! [D_132] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_132),'#skF_2')
      | ~ v4_pre_topc(D_132,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_132,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ) ),
    inference(splitRight,[status(thm)],[c_600])).

tff(c_693,plain,(
    ! [D_132] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_132),'#skF_2')
      | ~ v4_pre_topc(D_132,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_132,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_690])).

tff(c_708,plain,(
    ! [D_133] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_133),'#skF_2')
      | ~ v4_pre_topc(D_133,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_693])).

tff(c_712,plain,(
    ! [B_39] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_39),'#skF_2')
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_39,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_708])).

tff(c_721,plain,(
    ! [B_134] :
      ( v4_pre_topc(k10_relat_1('#skF_4',B_134),'#skF_2')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v4_pre_topc(B_134,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_712])).

tff(c_724,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_485,c_721])).

tff(c_727,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_724])).

tff(c_729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_727])).

tff(c_731,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_978,plain,(
    ! [A_180,B_181,C_182] :
      ( v4_pre_topc('#skF_1'(A_180,B_181,C_182),B_181)
      | v5_pre_topc(C_182,A_180,B_181)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_180),u1_struct_0(B_181))))
      | ~ v1_funct_2(C_182,u1_struct_0(A_180),u1_struct_0(B_181))
      | ~ v1_funct_1(C_182)
      | ~ l1_pre_topc(B_181)
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_980,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_978])).

tff(c_985,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_64,c_980])).

tff(c_986,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_731,c_985])).

tff(c_1176,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_986])).

tff(c_1182,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1176])).

tff(c_1188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1182])).

tff(c_1190,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_986])).

tff(c_762,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k8_relset_1(A_143,B_144,C_145,D_146) = k10_relat_1(C_145,D_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_767,plain,(
    ! [D_146] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4',D_146) = k10_relat_1('#skF_4',D_146) ),
    inference(resolution,[status(thm)],[c_65,c_762])).

tff(c_1217,plain,(
    ! [A_191,B_192,C_193] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_191),u1_struct_0(B_192),C_193,'#skF_1'(A_191,B_192,C_193)),A_191)
      | v5_pre_topc(C_193,A_191,B_192)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),u1_struct_0(B_192))))
      | ~ v1_funct_2(C_193,u1_struct_0(A_191),u1_struct_0(B_192))
      | ~ v1_funct_1(C_193)
      | ~ l1_pre_topc(B_192)
      | ~ l1_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1231,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_1217])).

tff(c_1238,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1190,c_44,c_64,c_65,c_1231])).

tff(c_1239,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_731,c_1238])).

tff(c_1189,plain,(
    v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_986])).

tff(c_1128,plain,(
    ! [A_187,B_188,C_189] :
      ( m1_subset_1('#skF_1'(A_187,B_188,C_189),k1_zfmisc_1(u1_struct_0(B_188)))
      | v5_pre_topc(C_189,A_187,B_188)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_187),u1_struct_0(B_188))))
      | ~ v1_funct_2(C_189,u1_struct_0(A_187),u1_struct_0(B_188))
      | ~ v1_funct_1(C_189)
      | ~ l1_pre_topc(B_188)
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1134,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_1128])).

tff(c_1139,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_64,c_1134])).

tff(c_1140,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_731,c_1139])).

tff(c_1191,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1140])).

tff(c_1198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_1191])).

tff(c_1199,plain,(
    m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_1140])).

tff(c_30,plain,(
    ! [B_39,A_37] :
      ( v4_pre_topc(B_39,A_37)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37)))))
      | ~ v4_pre_topc(B_39,g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1252,plain,
    ( v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3')
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1199,c_30])).

tff(c_1267,plain,(
    v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1189,c_1252])).

tff(c_28,plain,(
    ! [B_39,A_37] :
      ( m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37)))))
      | ~ v4_pre_topc(B_39,g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1249,plain,
    ( m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1199,c_28])).

tff(c_1264,plain,(
    m1_subset_1('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1189,c_1249])).

tff(c_730,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_768,plain,(
    ! [D_146] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_146) = k10_relat_1('#skF_4',D_146) ),
    inference(resolution,[status(thm)],[c_40,c_762])).

tff(c_1305,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_196),u1_struct_0(B_197),C_198,D_199),A_196)
      | ~ v4_pre_topc(D_199,B_197)
      | ~ m1_subset_1(D_199,k1_zfmisc_1(u1_struct_0(B_197)))
      | ~ v5_pre_topc(C_198,A_196,B_197)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_196),u1_struct_0(B_197))))
      | ~ v1_funct_2(C_198,u1_struct_0(A_196),u1_struct_0(B_197))
      | ~ v1_funct_1(C_198)
      | ~ l1_pre_topc(B_197)
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1313,plain,(
    ! [D_199] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_199),'#skF_2')
      | ~ v4_pre_topc(D_199,'#skF_3')
      | ~ m1_subset_1(D_199,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_1305])).

tff(c_1320,plain,(
    ! [D_200] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_200),'#skF_2')
      | ~ v4_pre_topc(D_200,'#skF_3')
      | ~ m1_subset_1(D_200,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_42,c_730,c_768,c_1313])).

tff(c_1323,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1264,c_1320])).

tff(c_1326,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1267,c_1323])).

tff(c_1328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1239,c_1326])).

%------------------------------------------------------------------------------
