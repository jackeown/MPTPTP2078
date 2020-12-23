%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:40 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 224 expanded)
%              Number of leaves         :   37 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 (1146 expanded)
%              Number of equality atoms :   21 ( 155 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_22,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_51,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_82,plain,(
    ! [A_87,B_88] :
      ( k6_domain_1(A_87,B_88) = k1_tarski(B_88)
      | ~ m1_subset_1(B_88,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_51,c_82])).

tff(c_120,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_12,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_12])).

tff(c_126,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_123])).

tff(c_129,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_129])).

tff(c_135,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_59,plain,(
    ! [B_77,A_78] :
      ( l1_pre_topc(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_65,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_97,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_82])).

tff(c_99,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_102,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_12])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_102])).

tff(c_108,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_108])).

tff(c_114,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_40,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_32,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_28,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k1_tarski(A_1),k1_zfmisc_1(B_2))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_170,plain,(
    ! [A_97,B_98,C_99,E_100] :
      ( k8_relset_1(u1_struct_0(A_97),u1_struct_0(B_98),C_99,E_100) = k2_pre_topc(A_97,E_100)
      | ~ m1_subset_1(E_100,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(E_100,k1_zfmisc_1(u1_struct_0(B_98)))
      | ~ v3_borsuk_1(C_99,A_97,B_98)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_97),u1_struct_0(B_98))))
      | ~ v5_pre_topc(C_99,A_97,B_98)
      | ~ v1_funct_2(C_99,u1_struct_0(A_97),u1_struct_0(B_98))
      | ~ v1_funct_1(C_99)
      | ~ m1_pre_topc(B_98,A_97)
      | ~ v4_tex_2(B_98,A_97)
      | v2_struct_0(B_98)
      | ~ l1_pre_topc(A_97)
      | ~ v3_tdlat_3(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_202,plain,(
    ! [A_110,B_111,C_112,A_113] :
      ( k8_relset_1(u1_struct_0(A_110),u1_struct_0(B_111),C_112,k1_tarski(A_113)) = k2_pre_topc(A_110,k1_tarski(A_113))
      | ~ m1_subset_1(k1_tarski(A_113),k1_zfmisc_1(u1_struct_0(B_111)))
      | ~ v3_borsuk_1(C_112,A_110,B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_111))))
      | ~ v5_pre_topc(C_112,A_110,B_111)
      | ~ v1_funct_2(C_112,u1_struct_0(A_110),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ m1_pre_topc(B_111,A_110)
      | ~ v4_tex_2(B_111,A_110)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_110)
      | ~ v3_tdlat_3(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110)
      | ~ r2_hidden(A_113,u1_struct_0(A_110)) ) ),
    inference(resolution,[status(thm)],[c_2,c_170])).

tff(c_207,plain,(
    ! [A_114,B_115,C_116,A_117] :
      ( k8_relset_1(u1_struct_0(A_114),u1_struct_0(B_115),C_116,k1_tarski(A_117)) = k2_pre_topc(A_114,k1_tarski(A_117))
      | ~ v3_borsuk_1(C_116,A_114,B_115)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_114),u1_struct_0(B_115))))
      | ~ v5_pre_topc(C_116,A_114,B_115)
      | ~ v1_funct_2(C_116,u1_struct_0(A_114),u1_struct_0(B_115))
      | ~ v1_funct_1(C_116)
      | ~ m1_pre_topc(B_115,A_114)
      | ~ v4_tex_2(B_115,A_114)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_114)
      | ~ v3_tdlat_3(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114)
      | ~ r2_hidden(A_117,u1_struct_0(A_114))
      | ~ r2_hidden(A_117,u1_struct_0(B_115)) ) ),
    inference(resolution,[status(thm)],[c_2,c_202])).

tff(c_212,plain,(
    ! [A_117] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_117)) = k2_pre_topc('#skF_1',k1_tarski(A_117))
      | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ v4_tex_2('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r2_hidden(A_117,u1_struct_0('#skF_1'))
      | ~ r2_hidden(A_117,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_30,c_207])).

tff(c_216,plain,(
    ! [A_117] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_117)) = k2_pre_topc('#skF_1',k1_tarski(A_117))
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ r2_hidden(A_117,u1_struct_0('#skF_1'))
      | ~ r2_hidden(A_117,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_40,c_38,c_36,c_34,c_32,c_28,c_212])).

tff(c_218,plain,(
    ! [A_118] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_118)) = k2_pre_topc('#skF_1',k1_tarski(A_118))
      | ~ r2_hidden(A_118,u1_struct_0('#skF_1'))
      | ~ r2_hidden(A_118,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_216])).

tff(c_134,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_113,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_20,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_115,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_52])).

tff(c_160,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_115])).

tff(c_229,plain,
    ( ~ r2_hidden('#skF_4',u1_struct_0('#skF_1'))
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_160])).

tff(c_231,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_234,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_231])).

tff(c_237,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_234])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_237])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_244,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_240])).

tff(c_247,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_244])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.80  
% 3.27/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.81  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.81  
% 3.27/1.81  %Foreground sorts:
% 3.27/1.81  
% 3.27/1.81  
% 3.27/1.81  %Background operators:
% 3.27/1.81  
% 3.27/1.81  
% 3.27/1.81  %Foreground operators:
% 3.27/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.27/1.81  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.27/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.81  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.81  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.27/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.27/1.81  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.27/1.81  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.81  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.81  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.81  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.81  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.27/1.81  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.27/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.81  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.81  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.27/1.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.27/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.27/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.27/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.81  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.27/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.81  
% 3.41/1.83  tff(f_152, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.41/1.83  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.41/1.83  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.41/1.83  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.41/1.83  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.41/1.83  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.41/1.83  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.41/1.83  tff(f_113, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.41/1.83  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_8, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.83  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_22, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_24, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_51, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 3.41/1.83  tff(c_82, plain, (![A_87, B_88]: (k6_domain_1(A_87, B_88)=k1_tarski(B_88) | ~m1_subset_1(B_88, A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.41/1.83  tff(c_98, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_51, c_82])).
% 3.41/1.83  tff(c_120, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_98])).
% 3.41/1.83  tff(c_12, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.41/1.83  tff(c_123, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_120, c_12])).
% 3.41/1.83  tff(c_126, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_123])).
% 3.41/1.83  tff(c_129, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_126])).
% 3.41/1.83  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_129])).
% 3.41/1.83  tff(c_135, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_98])).
% 3.41/1.83  tff(c_6, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.41/1.83  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_59, plain, (![B_77, A_78]: (l1_pre_topc(B_77) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.41/1.83  tff(c_62, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_59])).
% 3.41/1.83  tff(c_65, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_62])).
% 3.41/1.83  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_26, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_97, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_82])).
% 3.41/1.83  tff(c_99, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_97])).
% 3.41/1.83  tff(c_102, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_99, c_12])).
% 3.41/1.83  tff(c_105, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_102])).
% 3.41/1.83  tff(c_108, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_105])).
% 3.41/1.83  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_108])).
% 3.41/1.83  tff(c_114, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_97])).
% 3.41/1.83  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_46, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_40, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_34, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_32, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_28, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k1_tarski(A_1), k1_zfmisc_1(B_2)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.41/1.83  tff(c_170, plain, (![A_97, B_98, C_99, E_100]: (k8_relset_1(u1_struct_0(A_97), u1_struct_0(B_98), C_99, E_100)=k2_pre_topc(A_97, E_100) | ~m1_subset_1(E_100, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(E_100, k1_zfmisc_1(u1_struct_0(B_98))) | ~v3_borsuk_1(C_99, A_97, B_98) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_97), u1_struct_0(B_98)))) | ~v5_pre_topc(C_99, A_97, B_98) | ~v1_funct_2(C_99, u1_struct_0(A_97), u1_struct_0(B_98)) | ~v1_funct_1(C_99) | ~m1_pre_topc(B_98, A_97) | ~v4_tex_2(B_98, A_97) | v2_struct_0(B_98) | ~l1_pre_topc(A_97) | ~v3_tdlat_3(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.41/1.83  tff(c_202, plain, (![A_110, B_111, C_112, A_113]: (k8_relset_1(u1_struct_0(A_110), u1_struct_0(B_111), C_112, k1_tarski(A_113))=k2_pre_topc(A_110, k1_tarski(A_113)) | ~m1_subset_1(k1_tarski(A_113), k1_zfmisc_1(u1_struct_0(B_111))) | ~v3_borsuk_1(C_112, A_110, B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_111)))) | ~v5_pre_topc(C_112, A_110, B_111) | ~v1_funct_2(C_112, u1_struct_0(A_110), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~m1_pre_topc(B_111, A_110) | ~v4_tex_2(B_111, A_110) | v2_struct_0(B_111) | ~l1_pre_topc(A_110) | ~v3_tdlat_3(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110) | ~r2_hidden(A_113, u1_struct_0(A_110)))), inference(resolution, [status(thm)], [c_2, c_170])).
% 3.41/1.83  tff(c_207, plain, (![A_114, B_115, C_116, A_117]: (k8_relset_1(u1_struct_0(A_114), u1_struct_0(B_115), C_116, k1_tarski(A_117))=k2_pre_topc(A_114, k1_tarski(A_117)) | ~v3_borsuk_1(C_116, A_114, B_115) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_114), u1_struct_0(B_115)))) | ~v5_pre_topc(C_116, A_114, B_115) | ~v1_funct_2(C_116, u1_struct_0(A_114), u1_struct_0(B_115)) | ~v1_funct_1(C_116) | ~m1_pre_topc(B_115, A_114) | ~v4_tex_2(B_115, A_114) | v2_struct_0(B_115) | ~l1_pre_topc(A_114) | ~v3_tdlat_3(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114) | ~r2_hidden(A_117, u1_struct_0(A_114)) | ~r2_hidden(A_117, u1_struct_0(B_115)))), inference(resolution, [status(thm)], [c_2, c_202])).
% 3.41/1.83  tff(c_212, plain, (![A_117]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_117))=k2_pre_topc('#skF_1', k1_tarski(A_117)) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r2_hidden(A_117, u1_struct_0('#skF_1')) | ~r2_hidden(A_117, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_30, c_207])).
% 3.41/1.83  tff(c_216, plain, (![A_117]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_117))=k2_pre_topc('#skF_1', k1_tarski(A_117)) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~r2_hidden(A_117, u1_struct_0('#skF_1')) | ~r2_hidden(A_117, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_40, c_38, c_36, c_34, c_32, c_28, c_212])).
% 3.41/1.83  tff(c_218, plain, (![A_118]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_118))=k2_pre_topc('#skF_1', k1_tarski(A_118)) | ~r2_hidden(A_118, u1_struct_0('#skF_1')) | ~r2_hidden(A_118, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_216])).
% 3.41/1.83  tff(c_134, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 3.41/1.83  tff(c_113, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_97])).
% 3.41/1.83  tff(c_20, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.41/1.83  tff(c_52, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 3.41/1.83  tff(c_115, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_52])).
% 3.41/1.83  tff(c_160, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_115])).
% 3.41/1.83  tff(c_229, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_1')) | ~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_160])).
% 3.41/1.83  tff(c_231, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_229])).
% 3.41/1.83  tff(c_234, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_231])).
% 3.41/1.83  tff(c_237, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_234])).
% 3.41/1.83  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_237])).
% 3.41/1.83  tff(c_240, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_229])).
% 3.41/1.83  tff(c_244, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_240])).
% 3.41/1.83  tff(c_247, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_244])).
% 3.41/1.83  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_247])).
% 3.41/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.83  
% 3.41/1.83  Inference rules
% 3.41/1.83  ----------------------
% 3.41/1.83  #Ref     : 0
% 3.41/1.83  #Sup     : 39
% 3.41/1.83  #Fact    : 0
% 3.41/1.83  #Define  : 0
% 3.41/1.83  #Split   : 5
% 3.41/1.83  #Chain   : 0
% 3.41/1.83  #Close   : 0
% 3.41/1.83  
% 3.41/1.83  Ordering : KBO
% 3.41/1.83  
% 3.41/1.83  Simplification rules
% 3.41/1.83  ----------------------
% 3.41/1.83  #Subsume      : 0
% 3.41/1.84  #Demod        : 28
% 3.41/1.84  #Tautology    : 15
% 3.41/1.84  #SimpNegUnit  : 6
% 3.41/1.84  #BackRed      : 1
% 3.41/1.84  
% 3.41/1.84  #Partial instantiations: 0
% 3.41/1.84  #Strategies tried      : 1
% 3.41/1.84  
% 3.41/1.84  Timing (in seconds)
% 3.41/1.84  ----------------------
% 3.41/1.84  Preprocessing        : 0.59
% 3.41/1.84  Parsing              : 0.32
% 3.41/1.84  CNF conversion       : 0.05
% 3.41/1.84  Main loop            : 0.39
% 3.41/1.84  Inferencing          : 0.14
% 3.41/1.84  Reduction            : 0.12
% 3.41/1.84  Demodulation         : 0.08
% 3.41/1.84  BG Simplification    : 0.03
% 3.41/1.84  Subsumption          : 0.07
% 3.41/1.84  Abstraction          : 0.02
% 3.41/1.84  MUC search           : 0.00
% 3.41/1.84  Cooper               : 0.00
% 3.41/1.84  Total                : 1.05
% 3.41/1.84  Index Insertion      : 0.00
% 3.41/1.84  Index Deletion       : 0.00
% 3.41/1.84  Index Matching       : 0.00
% 3.41/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
