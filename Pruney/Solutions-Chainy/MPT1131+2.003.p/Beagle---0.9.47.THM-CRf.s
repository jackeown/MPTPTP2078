%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:11 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 430 expanded)
%              Number of leaves         :   30 ( 168 expanded)
%              Depth                    :   11
%              Number of atoms          :  268 (2183 expanded)
%              Number of equality atoms :   10 ( 175 expanded)
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

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_54,axiom,(
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

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18,plain,(
    ! [A_33] :
      ( m1_subset_1(u1_pre_topc(A_33),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33))))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,(
    ! [A_49,B_50] :
      ( l1_pre_topc(g1_pre_topc(A_49,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_72,plain,(
    ! [A_33] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_18,c_68])).

tff(c_28,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_5',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_57,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56])).

tff(c_80,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_50,plain,
    ( ~ v5_pre_topc('#skF_5',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_58,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50])).

tff(c_82,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_83,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k8_relset_1(A_55,B_56,C_57,D_58) = k10_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [D_58] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_58) = k10_relat_1('#skF_4',D_58) ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_225,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_108),u1_struct_0(B_109),C_110,'#skF_1'(A_108,B_109,C_110)),A_108)
      | v5_pre_topc(C_110,A_108,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc(B_109)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_237,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_225])).

tff(c_242,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_36,c_237])).

tff(c_243,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_242])).

tff(c_193,plain,(
    ! [A_102,B_103,C_104] :
      ( v4_pre_topc('#skF_1'(A_102,B_103,C_104),B_103)
      | v5_pre_topc(C_104,A_102,B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(B_103))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ v1_funct_1(C_104)
      | ~ l1_pre_topc(B_103)
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_200,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_193])).

tff(c_207,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_200])).

tff(c_208,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_207])).

tff(c_209,plain,(
    ! [A_105,B_106,C_107] :
      ( m1_subset_1('#skF_1'(A_105,B_106,C_107),k1_zfmisc_1(u1_struct_0(B_106)))
      | v5_pre_topc(C_107,A_105,B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),u1_struct_0(B_106))))
      | ~ v1_funct_2(C_107,u1_struct_0(A_105),u1_struct_0(B_106))
      | ~ v1_funct_1(C_107)
      | ~ l1_pre_topc(B_106)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_216,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_209])).

tff(c_223,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_216])).

tff(c_224,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_223])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_61,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_88,plain,(
    ! [D_58] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_58) = k10_relat_1('#skF_4',D_58) ),
    inference(resolution,[status(thm)],[c_61,c_83])).

tff(c_244,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_249,plain,(
    ! [D_114] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_114),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_114,'#skF_3')
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_61,c_244])).

tff(c_255,plain,(
    ! [D_114] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_114),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_114,'#skF_3')
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_60,c_80,c_88,c_249])).

tff(c_259,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_262,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_259])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_262])).

tff(c_269,plain,(
    ! [D_115] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_115),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_115,'#skF_3')
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_120,plain,(
    ! [D_65] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_65) = k10_relat_1('#skF_4',D_65) ),
    inference(resolution,[status(thm)],[c_61,c_83])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k8_relset_1(A_1,B_2,C_3,D_4),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [D_65] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_65),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_2])).

tff(c_132,plain,(
    ! [D_65] : m1_subset_1(k10_relat_1('#skF_4',D_65),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_126])).

tff(c_147,plain,(
    ! [B_79,A_80] :
      ( v4_pre_topc(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_80),u1_pre_topc(A_80)))))
      | ~ v4_pre_topc(B_79,g1_pre_topc(u1_struct_0(A_80),u1_pre_topc(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_153,plain,(
    ! [D_65] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_65),'#skF_2')
      | ~ v4_pre_topc(k10_relat_1('#skF_4',D_65),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_132,c_147])).

tff(c_161,plain,(
    ! [D_65] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_65),'#skF_2')
      | ~ v4_pre_topc(k10_relat_1('#skF_4',D_65),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_153])).

tff(c_285,plain,(
    ! [D_120] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_120),'#skF_2')
      | ~ v4_pre_topc(D_120,'#skF_3')
      | ~ m1_subset_1(D_120,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_269,c_161])).

tff(c_288,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_224,c_285])).

tff(c_295,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_288])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_295])).

tff(c_299,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_406,plain,(
    ! [A_156,B_157,C_158] :
      ( v4_pre_topc('#skF_1'(A_156,B_157,C_158),B_157)
      | v5_pre_topc(C_158,A_156,B_157)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0(A_156),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_pre_topc(B_157)
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_411,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_61,c_406])).

tff(c_417,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_60,c_411])).

tff(c_418,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_417])).

tff(c_422,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_425,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_422])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_425])).

tff(c_430,plain,(
    v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_431,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_438,plain,(
    ! [A_171,B_172,C_173] :
      ( m1_subset_1('#skF_1'(A_171,B_172,C_173),k1_zfmisc_1(u1_struct_0(B_172)))
      | v5_pre_topc(C_173,A_171,B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0(B_172))))
      | ~ v1_funct_2(C_173,u1_struct_0(A_171),u1_struct_0(B_172))
      | ~ v1_funct_1(C_173)
      | ~ l1_pre_topc(B_172)
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_443,plain,
    ( m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_61,c_438])).

tff(c_449,plain,
    ( m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_42,c_40,c_60,c_443])).

tff(c_450,plain,(
    m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_449])).

tff(c_298,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_302,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k8_relset_1(A_121,B_122,C_123,D_124) = k10_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_308,plain,(
    ! [D_124] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_124) = k10_relat_1('#skF_4',D_124) ),
    inference(resolution,[status(thm)],[c_36,c_302])).

tff(c_473,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_480,plain,(
    ! [D_180] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_180),'#skF_2')
      | ~ v4_pre_topc(D_180,'#skF_3')
      | ~ m1_subset_1(D_180,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_473])).

tff(c_488,plain,(
    ! [D_181] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_181),'#skF_2')
      | ~ v4_pre_topc(D_181,'#skF_3')
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_298,c_308,c_480])).

tff(c_491,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_450,c_488])).

tff(c_498,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_491])).

tff(c_318,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( m1_subset_1(k8_relset_1(A_126,B_127,C_128,D_129),k1_zfmisc_1(A_126))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_332,plain,(
    ! [D_124] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_124),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_318])).

tff(c_337,plain,(
    ! [D_124] : m1_subset_1(k10_relat_1('#skF_4',D_124),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_332])).

tff(c_22,plain,(
    ! [B_36,A_34] :
      ( v4_pre_topc(B_36,g1_pre_topc(u1_struct_0(A_34),u1_pre_topc(A_34)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ v4_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_307,plain,(
    ! [D_124] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_124) = k10_relat_1('#skF_4',D_124) ),
    inference(resolution,[status(thm)],[c_61,c_302])).

tff(c_454,plain,(
    ! [A_174,B_175,C_176] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_174),u1_struct_0(B_175),C_176,'#skF_1'(A_174,B_175,C_176)),A_174)
      | v5_pre_topc(C_176,A_174,B_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174),u1_struct_0(B_175))))
      | ~ v1_funct_2(C_176,u1_struct_0(A_174),u1_struct_0(B_175))
      | ~ v1_funct_1(C_176)
      | ~ l1_pre_topc(B_175)
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_458,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_454])).

tff(c_468,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_42,c_40,c_60,c_61,c_458])).

tff(c_469,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_468])).

tff(c_502,plain,
    ( ~ m1_subset_1(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_469])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_498,c_337,c_502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.46  
% 3.06/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.46  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.06/1.46  
% 3.06/1.46  %Foreground sorts:
% 3.06/1.46  
% 3.06/1.46  
% 3.06/1.46  %Background operators:
% 3.06/1.46  
% 3.06/1.46  
% 3.06/1.46  %Foreground operators:
% 3.06/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.06/1.46  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.06/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.46  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.06/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.06/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.46  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.06/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.06/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.06/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.46  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.06/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.06/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.46  
% 3.06/1.48  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 3.06/1.48  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.06/1.48  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 3.06/1.48  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.06/1.48  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 3.06/1.48  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 3.06/1.48  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v4_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v4_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_pre_topc)).
% 3.06/1.48  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_18, plain, (![A_33]: (m1_subset_1(u1_pre_topc(A_33), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_33)))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.06/1.48  tff(c_68, plain, (![A_49, B_50]: (l1_pre_topc(g1_pre_topc(A_49, B_50)) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.06/1.48  tff(c_72, plain, (![A_33]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33))) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_18, c_68])).
% 3.06/1.48  tff(c_28, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_56, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v5_pre_topc('#skF_5', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_57, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_56])).
% 3.06/1.48  tff(c_80, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_57])).
% 3.06/1.48  tff(c_50, plain, (~v5_pre_topc('#skF_5', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_58, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_50])).
% 3.06/1.48  tff(c_82, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58])).
% 3.06/1.48  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_83, plain, (![A_55, B_56, C_57, D_58]: (k8_relset_1(A_55, B_56, C_57, D_58)=k10_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.48  tff(c_89, plain, (![D_58]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_58)=k10_relat_1('#skF_4', D_58))), inference(resolution, [status(thm)], [c_36, c_83])).
% 3.06/1.48  tff(c_225, plain, (![A_108, B_109, C_110]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_108), u1_struct_0(B_109), C_110, '#skF_1'(A_108, B_109, C_110)), A_108) | v5_pre_topc(C_110, A_108, B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108), u1_struct_0(B_109)))) | ~v1_funct_2(C_110, u1_struct_0(A_108), u1_struct_0(B_109)) | ~v1_funct_1(C_110) | ~l1_pre_topc(B_109) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.48  tff(c_237, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_225])).
% 3.06/1.48  tff(c_242, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_40, c_38, c_36, c_237])).
% 3.06/1.48  tff(c_243, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_82, c_242])).
% 3.06/1.48  tff(c_193, plain, (![A_102, B_103, C_104]: (v4_pre_topc('#skF_1'(A_102, B_103, C_104), B_103) | v5_pre_topc(C_104, A_102, B_103) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), u1_struct_0(B_103)))) | ~v1_funct_2(C_104, u1_struct_0(A_102), u1_struct_0(B_103)) | ~v1_funct_1(C_104) | ~l1_pre_topc(B_103) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.48  tff(c_200, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_193])).
% 3.06/1.48  tff(c_207, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_40, c_38, c_200])).
% 3.06/1.48  tff(c_208, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_82, c_207])).
% 3.06/1.48  tff(c_209, plain, (![A_105, B_106, C_107]: (m1_subset_1('#skF_1'(A_105, B_106, C_107), k1_zfmisc_1(u1_struct_0(B_106))) | v5_pre_topc(C_107, A_105, B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), u1_struct_0(B_106)))) | ~v1_funct_2(C_107, u1_struct_0(A_105), u1_struct_0(B_106)) | ~v1_funct_1(C_107) | ~l1_pre_topc(B_106) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.48  tff(c_216, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_209])).
% 3.06/1.48  tff(c_223, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_40, c_38, c_216])).
% 3.06/1.48  tff(c_224, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_82, c_223])).
% 3.06/1.48  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_60, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 3.06/1.48  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.06/1.48  tff(c_61, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 3.06/1.48  tff(c_88, plain, (![D_58]: (k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'), '#skF_4', D_58)=k10_relat_1('#skF_4', D_58))), inference(resolution, [status(thm)], [c_61, c_83])).
% 3.06/1.48  tff(c_244, plain, (![A_111, B_112, C_113, D_114]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_111), u1_struct_0(B_112), C_113, D_114), A_111) | ~v4_pre_topc(D_114, B_112) | ~m1_subset_1(D_114, k1_zfmisc_1(u1_struct_0(B_112))) | ~v5_pre_topc(C_113, A_111, B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, u1_struct_0(A_111), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.48  tff(c_249, plain, (![D_114]: (v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'), '#skF_4', D_114), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v4_pre_topc(D_114, '#skF_3') | ~m1_subset_1(D_114, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_61, c_244])).
% 3.06/1.48  tff(c_255, plain, (![D_114]: (v4_pre_topc(k10_relat_1('#skF_4', D_114), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v4_pre_topc(D_114, '#skF_3') | ~m1_subset_1(D_114, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_60, c_80, c_88, c_249])).
% 3.06/1.48  tff(c_259, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_255])).
% 3.06/1.48  tff(c_262, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_72, c_259])).
% 3.06/1.48  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_262])).
% 3.06/1.48  tff(c_269, plain, (![D_115]: (v4_pre_topc(k10_relat_1('#skF_4', D_115), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v4_pre_topc(D_115, '#skF_3') | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_255])).
% 3.06/1.48  tff(c_120, plain, (![D_65]: (k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'), '#skF_4', D_65)=k10_relat_1('#skF_4', D_65))), inference(resolution, [status(thm)], [c_61, c_83])).
% 3.06/1.48  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k8_relset_1(A_1, B_2, C_3, D_4), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.48  tff(c_126, plain, (![D_65]: (m1_subset_1(k10_relat_1('#skF_4', D_65), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_120, c_2])).
% 3.06/1.48  tff(c_132, plain, (![D_65]: (m1_subset_1(k10_relat_1('#skF_4', D_65), k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_126])).
% 3.06/1.48  tff(c_147, plain, (![B_79, A_80]: (v4_pre_topc(B_79, A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_80), u1_pre_topc(A_80))))) | ~v4_pre_topc(B_79, g1_pre_topc(u1_struct_0(A_80), u1_pre_topc(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.06/1.48  tff(c_153, plain, (![D_65]: (v4_pre_topc(k10_relat_1('#skF_4', D_65), '#skF_2') | ~v4_pre_topc(k10_relat_1('#skF_4', D_65), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_132, c_147])).
% 3.06/1.48  tff(c_161, plain, (![D_65]: (v4_pre_topc(k10_relat_1('#skF_4', D_65), '#skF_2') | ~v4_pre_topc(k10_relat_1('#skF_4', D_65), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_153])).
% 3.06/1.48  tff(c_285, plain, (![D_120]: (v4_pre_topc(k10_relat_1('#skF_4', D_120), '#skF_2') | ~v4_pre_topc(D_120, '#skF_3') | ~m1_subset_1(D_120, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_269, c_161])).
% 3.06/1.48  tff(c_288, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | ~v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_224, c_285])).
% 3.06/1.48  tff(c_295, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_288])).
% 3.06/1.48  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_295])).
% 3.06/1.48  tff(c_299, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_57])).
% 3.06/1.48  tff(c_406, plain, (![A_156, B_157, C_158]: (v4_pre_topc('#skF_1'(A_156, B_157, C_158), B_157) | v5_pre_topc(C_158, A_156, B_157) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_156), u1_struct_0(B_157)))) | ~v1_funct_2(C_158, u1_struct_0(A_156), u1_struct_0(B_157)) | ~v1_funct_1(C_158) | ~l1_pre_topc(B_157) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.48  tff(c_411, plain, (v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_61, c_406])).
% 3.06/1.48  tff(c_417, plain, (v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_60, c_411])).
% 3.06/1.48  tff(c_418, plain, (v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_299, c_417])).
% 3.06/1.48  tff(c_422, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_418])).
% 3.06/1.48  tff(c_425, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_72, c_422])).
% 3.06/1.48  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_425])).
% 3.06/1.48  tff(c_430, plain, (v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_418])).
% 3.06/1.48  tff(c_431, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_418])).
% 3.06/1.48  tff(c_438, plain, (![A_171, B_172, C_173]: (m1_subset_1('#skF_1'(A_171, B_172, C_173), k1_zfmisc_1(u1_struct_0(B_172))) | v5_pre_topc(C_173, A_171, B_172) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), u1_struct_0(B_172)))) | ~v1_funct_2(C_173, u1_struct_0(A_171), u1_struct_0(B_172)) | ~v1_funct_1(C_173) | ~l1_pre_topc(B_172) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.48  tff(c_443, plain, (m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_61, c_438])).
% 3.06/1.48  tff(c_449, plain, (m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_42, c_40, c_60, c_443])).
% 3.06/1.48  tff(c_450, plain, (m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_299, c_449])).
% 3.06/1.48  tff(c_298, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_57])).
% 3.06/1.48  tff(c_302, plain, (![A_121, B_122, C_123, D_124]: (k8_relset_1(A_121, B_122, C_123, D_124)=k10_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.48  tff(c_308, plain, (![D_124]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_124)=k10_relat_1('#skF_4', D_124))), inference(resolution, [status(thm)], [c_36, c_302])).
% 3.06/1.48  tff(c_473, plain, (![A_177, B_178, C_179, D_180]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_177), u1_struct_0(B_178), C_179, D_180), A_177) | ~v4_pre_topc(D_180, B_178) | ~m1_subset_1(D_180, k1_zfmisc_1(u1_struct_0(B_178))) | ~v5_pre_topc(C_179, A_177, B_178) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177), u1_struct_0(B_178)))) | ~v1_funct_2(C_179, u1_struct_0(A_177), u1_struct_0(B_178)) | ~v1_funct_1(C_179) | ~l1_pre_topc(B_178) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.48  tff(c_480, plain, (![D_180]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_180), '#skF_2') | ~v4_pre_topc(D_180, '#skF_3') | ~m1_subset_1(D_180, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_473])).
% 3.06/1.48  tff(c_488, plain, (![D_181]: (v4_pre_topc(k10_relat_1('#skF_4', D_181), '#skF_2') | ~v4_pre_topc(D_181, '#skF_3') | ~m1_subset_1(D_181, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_40, c_38, c_298, c_308, c_480])).
% 3.06/1.48  tff(c_491, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), '#skF_2') | ~v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_450, c_488])).
% 3.06/1.48  tff(c_498, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_491])).
% 3.06/1.48  tff(c_318, plain, (![A_126, B_127, C_128, D_129]: (m1_subset_1(k8_relset_1(A_126, B_127, C_128, D_129), k1_zfmisc_1(A_126)) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.48  tff(c_332, plain, (![D_124]: (m1_subset_1(k10_relat_1('#skF_4', D_124), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_308, c_318])).
% 3.06/1.48  tff(c_337, plain, (![D_124]: (m1_subset_1(k10_relat_1('#skF_4', D_124), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_332])).
% 3.06/1.48  tff(c_22, plain, (![B_36, A_34]: (v4_pre_topc(B_36, g1_pre_topc(u1_struct_0(A_34), u1_pre_topc(A_34))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~v4_pre_topc(B_36, A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.06/1.48  tff(c_307, plain, (![D_124]: (k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'), '#skF_4', D_124)=k10_relat_1('#skF_4', D_124))), inference(resolution, [status(thm)], [c_61, c_302])).
% 3.06/1.48  tff(c_454, plain, (![A_174, B_175, C_176]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_174), u1_struct_0(B_175), C_176, '#skF_1'(A_174, B_175, C_176)), A_174) | v5_pre_topc(C_176, A_174, B_175) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174), u1_struct_0(B_175)))) | ~v1_funct_2(C_176, u1_struct_0(A_174), u1_struct_0(B_175)) | ~v1_funct_1(C_176) | ~l1_pre_topc(B_175) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.48  tff(c_458, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_307, c_454])).
% 3.06/1.48  tff(c_468, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_42, c_40, c_60, c_61, c_458])).
% 3.06/1.48  tff(c_469, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_299, c_468])).
% 3.06/1.48  tff(c_502, plain, (~m1_subset_1(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_469])).
% 3.06/1.48  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_498, c_337, c_502])).
% 3.06/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.48  
% 3.06/1.48  Inference rules
% 3.06/1.48  ----------------------
% 3.06/1.48  #Ref     : 0
% 3.06/1.48  #Sup     : 80
% 3.06/1.48  #Fact    : 0
% 3.06/1.48  #Define  : 0
% 3.06/1.48  #Split   : 3
% 3.06/1.48  #Chain   : 0
% 3.06/1.48  #Close   : 0
% 3.06/1.48  
% 3.06/1.48  Ordering : KBO
% 3.06/1.48  
% 3.06/1.48  Simplification rules
% 3.06/1.49  ----------------------
% 3.06/1.49  #Subsume      : 4
% 3.06/1.49  #Demod        : 115
% 3.06/1.49  #Tautology    : 28
% 3.06/1.49  #SimpNegUnit  : 7
% 3.06/1.49  #BackRed      : 0
% 3.06/1.49  
% 3.06/1.49  #Partial instantiations: 0
% 3.06/1.49  #Strategies tried      : 1
% 3.06/1.49  
% 3.06/1.49  Timing (in seconds)
% 3.06/1.49  ----------------------
% 3.06/1.49  Preprocessing        : 0.34
% 3.06/1.49  Parsing              : 0.18
% 3.06/1.49  CNF conversion       : 0.03
% 3.06/1.49  Main loop            : 0.33
% 3.06/1.49  Inferencing          : 0.13
% 3.06/1.49  Reduction            : 0.10
% 3.06/1.49  Demodulation         : 0.08
% 3.06/1.49  BG Simplification    : 0.02
% 3.06/1.49  Subsumption          : 0.05
% 3.06/1.49  Abstraction          : 0.02
% 3.06/1.49  MUC search           : 0.00
% 3.06/1.49  Cooper               : 0.00
% 3.06/1.49  Total                : 0.71
% 3.06/1.49  Index Insertion      : 0.00
% 3.06/1.49  Index Deletion       : 0.00
% 3.06/1.49  Index Matching       : 0.00
% 3.06/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
