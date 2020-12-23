%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1132+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:27 EST 2020

% Result     : Theorem 18.56s
% Output     : CNFRefutation 18.56s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 493 expanded)
%              Number of leaves         :   33 ( 193 expanded)
%              Depth                    :   13
%              Number of atoms          :  280 (2569 expanded)
%              Number of equality atoms :    9 ( 195 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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

tff(f_106,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_65,axiom,(
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

tff(c_42,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_64,plain,
    ( ~ v5_pre_topc('#skF_7','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_72,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_166,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_376,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k8_relset_1(A_117,B_118,C_119,D_120) = k10_relat_1(C_119,D_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_397,plain,(
    ! [D_120] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_120) = k10_relat_1('#skF_6',D_120) ),
    inference(resolution,[status(thm)],[c_50,c_376])).

tff(c_819,plain,(
    ! [A_194,B_195,C_196] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_194),u1_struct_0(B_195),C_196,'#skF_1'(A_194,B_195,C_196)),A_194)
      | v5_pre_topc(C_196,A_194,B_195)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_194),u1_struct_0(B_195))))
      | ~ v1_funct_2(C_196,u1_struct_0(A_194),u1_struct_0(B_195))
      | ~ v1_funct_1(C_196)
      | ~ l1_pre_topc(B_195)
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_831,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4','#skF_5','#skF_6')),'#skF_4')
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_819])).

tff(c_841,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4','#skF_5','#skF_6')),'#skF_4')
    | v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_52,c_50,c_831])).

tff(c_842,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4','#skF_5','#skF_6')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_841])).

tff(c_729,plain,(
    ! [A_179,B_180,C_181] :
      ( v4_pre_topc('#skF_1'(A_179,B_180,C_181),B_180)
      | v5_pre_topc(C_181,A_179,B_180)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_179),u1_struct_0(B_180))))
      | ~ v1_funct_2(C_181,u1_struct_0(A_179),u1_struct_0(B_180))
      | ~ v1_funct_1(C_181)
      | ~ l1_pre_topc(B_180)
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_745,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_729])).

tff(c_758,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_52,c_745])).

tff(c_759,plain,(
    v4_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_758])).

tff(c_774,plain,(
    ! [A_190,B_191,C_192] :
      ( m1_subset_1('#skF_1'(A_190,B_191,C_192),k1_zfmisc_1(u1_struct_0(B_191)))
      | v5_pre_topc(C_192,A_190,B_191)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190),u1_struct_0(B_191))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_190),u1_struct_0(B_191))
      | ~ v1_funct_1(C_192)
      | ~ l1_pre_topc(B_191)
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_790,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_774])).

tff(c_803,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_52,c_790])).

tff(c_804,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_803])).

tff(c_58,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    ! [B_47,A_45] :
      ( v4_pre_topc(B_47,g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ v4_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    ! [B_47,A_45] :
      ( m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ v4_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_pre_topc(A_30),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30))))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_114,plain,(
    ! [A_76,B_77] :
      ( l1_pre_topc(g1_pre_topc(A_76,B_77))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_122,plain,(
    ! [A_30] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_46,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_74,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_70,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v5_pre_topc('#skF_7','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_71,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_70])).

tff(c_187,plain,(
    v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_71])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_75,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_395,plain,(
    ! [D_120] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))),'#skF_6',D_120) = k10_relat_1('#skF_6',D_120) ),
    inference(resolution,[status(thm)],[c_75,c_376])).

tff(c_1009,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_200),u1_struct_0(B_201),C_202,D_203),A_200)
      | ~ v4_pre_topc(D_203,B_201)
      | ~ m1_subset_1(D_203,k1_zfmisc_1(u1_struct_0(B_201)))
      | ~ v5_pre_topc(C_202,A_200,B_201)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_200),u1_struct_0(B_201))))
      | ~ v1_funct_2(C_202,u1_struct_0(A_200),u1_struct_0(B_201))
      | ~ v1_funct_1(C_202)
      | ~ l1_pre_topc(B_201)
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1023,plain,(
    ! [D_203] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))),'#skF_6',D_203),'#skF_4')
      | ~ v4_pre_topc(D_203,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1(D_203,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
      | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_75,c_1009])).

tff(c_1038,plain,(
    ! [D_203] :
      ( v4_pre_topc(k10_relat_1('#skF_6',D_203),'#skF_4')
      | ~ v4_pre_topc(D_203,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1(D_203,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_74,c_187,c_395,c_1023])).

tff(c_1054,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1038])).

tff(c_1060,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_1054])).

tff(c_1066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1060])).

tff(c_1101,plain,(
    ! [D_214] :
      ( v4_pre_topc(k10_relat_1('#skF_6',D_214),'#skF_4')
      | ~ v4_pre_topc(D_214,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1(D_214,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))) ) ),
    inference(splitRight,[status(thm)],[c_1038])).

tff(c_1113,plain,(
    ! [B_47] :
      ( v4_pre_topc(k10_relat_1('#skF_6',B_47),'#skF_4')
      | ~ v4_pre_topc(B_47,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v4_pre_topc(B_47,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_1101])).

tff(c_42176,plain,(
    ! [B_1895] :
      ( v4_pre_topc(k10_relat_1('#skF_6',B_1895),'#skF_4')
      | ~ v4_pre_topc(B_1895,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1(B_1895,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v4_pre_topc(B_1895,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1113])).

tff(c_42184,plain,(
    ! [B_47] :
      ( v4_pre_topc(k10_relat_1('#skF_6',B_47),'#skF_4')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v4_pre_topc(B_47,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_42176])).

tff(c_42196,plain,(
    ! [B_1896] :
      ( v4_pre_topc(k10_relat_1('#skF_6',B_1896),'#skF_4')
      | ~ m1_subset_1(B_1896,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v4_pre_topc(B_1896,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42184])).

tff(c_42215,plain,
    ( v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4','#skF_5','#skF_6')),'#skF_4')
    | ~ v4_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_804,c_42196])).

tff(c_42253,plain,(
    v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4','#skF_5','#skF_6')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_42215])).

tff(c_42255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_42253])).

tff(c_42256,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_42805,plain,(
    ! [A_1996,B_1997,C_1998] :
      ( v4_pre_topc('#skF_1'(A_1996,B_1997,C_1998),B_1997)
      | v5_pre_topc(C_1998,A_1996,B_1997)
      | ~ m1_subset_1(C_1998,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1996),u1_struct_0(B_1997))))
      | ~ v1_funct_2(C_1998,u1_struct_0(A_1996),u1_struct_0(B_1997))
      | ~ v1_funct_1(C_1998)
      | ~ l1_pre_topc(B_1997)
      | ~ l1_pre_topc(A_1996) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42819,plain,
    ( v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_42805])).

tff(c_42831,plain,
    ( v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_74,c_42819])).

tff(c_42832,plain,
    ( v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42256,c_42831])).

tff(c_42839,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_42832])).

tff(c_42845,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_42839])).

tff(c_42851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_42845])).

tff(c_42853,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_42832])).

tff(c_42473,plain,(
    ! [A_1926,B_1927,C_1928,D_1929] :
      ( k8_relset_1(A_1926,B_1927,C_1928,D_1929) = k10_relat_1(C_1928,D_1929)
      | ~ m1_subset_1(C_1928,k1_zfmisc_1(k2_zfmisc_1(A_1926,B_1927))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42493,plain,(
    ! [D_1929] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))),'#skF_6',D_1929) = k10_relat_1('#skF_6',D_1929) ),
    inference(resolution,[status(thm)],[c_75,c_42473])).

tff(c_43018,plain,(
    ! [A_2018,B_2019,C_2020] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_2018),u1_struct_0(B_2019),C_2020,'#skF_1'(A_2018,B_2019,C_2020)),A_2018)
      | v5_pre_topc(C_2020,A_2018,B_2019)
      | ~ m1_subset_1(C_2020,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2018),u1_struct_0(B_2019))))
      | ~ v1_funct_2(C_2020,u1_struct_0(A_2018),u1_struct_0(B_2019))
      | ~ v1_funct_1(C_2020)
      | ~ l1_pre_topc(B_2019)
      | ~ l1_pre_topc(A_2018) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_43026,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6')),'#skF_4')
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42493,c_43018])).

tff(c_43038,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6')),'#skF_4')
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_42853,c_54,c_74,c_75,c_43026])).

tff(c_43039,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42256,c_43038])).

tff(c_42852,plain,(
    v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_42832])).

tff(c_42869,plain,(
    ! [A_2001,B_2002,C_2003] :
      ( m1_subset_1('#skF_1'(A_2001,B_2002,C_2003),k1_zfmisc_1(u1_struct_0(B_2002)))
      | v5_pre_topc(C_2003,A_2001,B_2002)
      | ~ m1_subset_1(C_2003,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2001),u1_struct_0(B_2002))))
      | ~ v1_funct_2(C_2003,u1_struct_0(A_2001),u1_struct_0(B_2002))
      | ~ v1_funct_1(C_2003)
      | ~ l1_pre_topc(B_2002)
      | ~ l1_pre_topc(A_2001) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42883,plain,
    ( m1_subset_1('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_42869])).

tff(c_42895,plain,
    ( m1_subset_1('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_42853,c_54,c_74,c_42883])).

tff(c_42896,plain,(
    m1_subset_1('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_42256,c_42895])).

tff(c_38,plain,(
    ! [B_47,A_45] :
      ( v4_pre_topc(B_47,A_45)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))))
      | ~ v4_pre_topc(B_47,g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42967,plain,
    ( v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),'#skF_5')
    | ~ v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_42896,c_38])).

tff(c_42983,plain,(
    v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42852,c_42967])).

tff(c_36,plain,(
    ! [B_47,A_45] :
      ( m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))))
      | ~ v4_pre_topc(B_47,g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42964,plain,
    ( m1_subset_1('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_42896,c_36])).

tff(c_42980,plain,(
    m1_subset_1('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42852,c_42964])).

tff(c_42257,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_42494,plain,(
    ! [D_1929] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_1929) = k10_relat_1('#skF_6',D_1929) ),
    inference(resolution,[status(thm)],[c_50,c_42473])).

tff(c_43148,plain,(
    ! [A_2034,B_2035,C_2036,D_2037] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_2034),u1_struct_0(B_2035),C_2036,D_2037),A_2034)
      | ~ v4_pre_topc(D_2037,B_2035)
      | ~ m1_subset_1(D_2037,k1_zfmisc_1(u1_struct_0(B_2035)))
      | ~ v5_pre_topc(C_2036,A_2034,B_2035)
      | ~ m1_subset_1(C_2036,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2034),u1_struct_0(B_2035))))
      | ~ v1_funct_2(C_2036,u1_struct_0(A_2034),u1_struct_0(B_2035))
      | ~ v1_funct_1(C_2036)
      | ~ l1_pre_topc(B_2035)
      | ~ l1_pre_topc(A_2034) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_43164,plain,(
    ! [D_2037] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_2037),'#skF_4')
      | ~ v4_pre_topc(D_2037,'#skF_5')
      | ~ m1_subset_1(D_2037,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_43148])).

tff(c_43180,plain,(
    ! [D_2038] :
      ( v4_pre_topc(k10_relat_1('#skF_6',D_2038),'#skF_4')
      | ~ v4_pre_topc(D_2038,'#skF_5')
      | ~ m1_subset_1(D_2038,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_52,c_42257,c_42494,c_43164])).

tff(c_43183,plain,
    ( v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6')),'#skF_4')
    | ~ v4_pre_topc('#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_42980,c_43180])).

tff(c_43210,plain,(
    v4_pre_topc(k10_relat_1('#skF_6','#skF_1'('#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')),'#skF_6')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42983,c_43183])).

tff(c_43212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43039,c_43210])).

%------------------------------------------------------------------------------
