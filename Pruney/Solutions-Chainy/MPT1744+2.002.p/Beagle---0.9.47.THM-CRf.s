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
% DateTime   : Thu Dec  3 10:26:48 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 245 expanded)
%              Number of leaves         :   49 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 (1562 expanded)
%              Number of equality atoms :   22 (  53 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k3_funct_2 > k6_domain_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_218,negated_conjecture,(
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
                  & v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(B),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( ( v5_pre_topc(D,C,B)
                                & r1_tmap_1(B,A,E,F) )
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( r2_hidden(G,k8_relset_1(u1_struct_0(C),u1_struct_0(B),D,k6_domain_1(u1_struct_0(B),F)))
                                   => r1_tmap_1(C,A,k1_partfun1(u1_struct_0(C),u1_struct_0(B),u1_struct_0(B),u1_struct_0(A),D,E),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tmap_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_115,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_166,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(C))
                             => ( ( G = k3_funct_2(u1_struct_0(B),u1_struct_0(C),D,F)
                                  & r1_tmap_1(B,C,D,F)
                                  & r1_tmap_1(C,A,E,G) )
                               => r1_tmap_1(B,A,k1_partfun1(u1_struct_0(B),u1_struct_0(C),u1_struct_0(C),u1_struct_0(A),D,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_90,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_88,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_78,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_76,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_84,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_82,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_74,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_72,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_70,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_68,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    v1_funct_2('#skF_10',u1_struct_0('#skF_7'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_64,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_56,plain,(
    m1_subset_1('#skF_12',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_62,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_32,plain,(
    ! [C_20,A_18,B_19] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_110,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_32])).

tff(c_195,plain,(
    ! [A_325,B_326,C_327,D_328] :
      ( k8_relset_1(A_325,B_326,C_327,D_328) = k10_relat_1(C_327,D_328)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_200,plain,(
    ! [D_328] : k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',D_328) = k10_relat_1('#skF_9',D_328) ),
    inference(resolution,[status(thm)],[c_70,c_195])).

tff(c_38,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_111,plain,(
    ! [A_310,B_311] :
      ( k6_domain_1(A_310,B_311) = k1_tarski(B_311)
      | ~ m1_subset_1(B_311,A_310)
      | v1_xboole_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_126,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_11') = k1_tarski('#skF_11')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_111])).

tff(c_128,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_40,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_131,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_128,c_40])).

tff(c_134,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_131])).

tff(c_137,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_134])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_137])).

tff(c_142,plain,(
    k6_domain_1(u1_struct_0('#skF_7'),'#skF_11') = k1_tarski('#skF_11') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_54,plain,(
    r2_hidden('#skF_12',k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',k6_domain_1(u1_struct_0('#skF_7'),'#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_169,plain,(
    r2_hidden('#skF_12',k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_54])).

tff(c_202,plain,(
    r2_hidden('#skF_12',k10_relat_1('#skF_9',k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_169])).

tff(c_227,plain,(
    ! [A_331,D_332,B_333] :
      ( r2_hidden(k1_funct_1(A_331,D_332),B_333)
      | ~ r2_hidden(D_332,k10_relat_1(A_331,B_333))
      | ~ v1_funct_1(A_331)
      | ~ v1_relat_1(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [A_336,D_337,A_338] :
      ( k1_funct_1(A_336,D_337) = A_338
      | ~ r2_hidden(D_337,k10_relat_1(A_336,k1_tarski(A_338)))
      | ~ v1_funct_1(A_336)
      | ~ v1_relat_1(A_336) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_268,plain,
    ( k1_funct_1('#skF_9','#skF_12') = '#skF_11'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_202,c_261])).

tff(c_280,plain,(
    k1_funct_1('#skF_9','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74,c_268])).

tff(c_127,plain,
    ( k6_domain_1(u1_struct_0('#skF_8'),'#skF_12') = k1_tarski('#skF_12')
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_111])).

tff(c_148,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_151,plain,
    ( ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_148,c_40])).

tff(c_154,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_151])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_154])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_158])).

tff(c_164,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_506,plain,(
    ! [A_365,B_366,C_367,D_368] :
      ( k3_funct_2(A_365,B_366,C_367,D_368) = k1_funct_1(C_367,D_368)
      | ~ m1_subset_1(D_368,A_365)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(A_365,B_366)))
      | ~ v1_funct_2(C_367,A_365,B_366)
      | ~ v1_funct_1(C_367)
      | v1_xboole_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_514,plain,(
    ! [B_366,C_367] :
      ( k3_funct_2(u1_struct_0('#skF_8'),B_366,C_367,'#skF_12') = k1_funct_1(C_367,'#skF_12')
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),B_366)))
      | ~ v1_funct_2(C_367,u1_struct_0('#skF_8'),B_366)
      | ~ v1_funct_1(C_367)
      | v1_xboole_0(u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_56,c_506])).

tff(c_541,plain,(
    ! [B_383,C_384] :
      ( k3_funct_2(u1_struct_0('#skF_8'),B_383,C_384,'#skF_12') = k1_funct_1(C_384,'#skF_12')
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),B_383)))
      | ~ v1_funct_2(C_384,u1_struct_0('#skF_8'),B_383)
      | ~ v1_funct_1(C_384) ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_514])).

tff(c_544,plain,
    ( k3_funct_2(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9','#skF_12') = k1_funct_1('#skF_9','#skF_12')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_541])).

tff(c_547,plain,(
    k3_funct_2(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_280,c_544])).

tff(c_60,plain,(
    v5_pre_topc('#skF_9','#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1011,plain,(
    ! [B_442,A_443,C_444,D_445] :
      ( r1_tmap_1(B_442,A_443,C_444,D_445)
      | ~ m1_subset_1(D_445,u1_struct_0(B_442))
      | ~ v5_pre_topc(C_444,B_442,A_443)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_442),u1_struct_0(A_443))))
      | ~ v1_funct_2(C_444,u1_struct_0(B_442),u1_struct_0(A_443))
      | ~ v1_funct_1(C_444)
      | ~ l1_pre_topc(B_442)
      | ~ v2_pre_topc(B_442)
      | v2_struct_0(B_442)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1015,plain,(
    ! [A_443,C_444] :
      ( r1_tmap_1('#skF_8',A_443,C_444,'#skF_12')
      | ~ v5_pre_topc(C_444,'#skF_8',A_443)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_443))))
      | ~ v1_funct_2(C_444,u1_struct_0('#skF_8'),u1_struct_0(A_443))
      | ~ v1_funct_1(C_444)
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_56,c_1011])).

tff(c_1022,plain,(
    ! [A_443,C_444] :
      ( r1_tmap_1('#skF_8',A_443,C_444,'#skF_12')
      | ~ v5_pre_topc(C_444,'#skF_8',A_443)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_443))))
      | ~ v1_funct_2(C_444,u1_struct_0('#skF_8'),u1_struct_0(A_443))
      | ~ v1_funct_1(C_444)
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1015])).

tff(c_1032,plain,(
    ! [A_448,C_449] :
      ( r1_tmap_1('#skF_8',A_448,C_449,'#skF_12')
      | ~ v5_pre_topc(C_449,'#skF_8',A_448)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_448))))
      | ~ v1_funct_2(C_449,u1_struct_0('#skF_8'),u1_struct_0(A_448))
      | ~ v1_funct_1(C_449)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | v2_struct_0(A_448) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1022])).

tff(c_1035,plain,
    ( r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12')
    | ~ v5_pre_topc('#skF_9','#skF_8','#skF_7')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_1032])).

tff(c_1038,plain,
    ( r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_74,c_72,c_60,c_1035])).

tff(c_1039,plain,(
    r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1038])).

tff(c_58,plain,(
    r1_tmap_1('#skF_7','#skF_6','#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1068,plain,(
    ! [B_453,C_456,E_458,D_454,F_455,A_457] :
      ( r1_tmap_1(B_453,A_457,k1_partfun1(u1_struct_0(B_453),u1_struct_0(C_456),u1_struct_0(C_456),u1_struct_0(A_457),D_454,E_458),F_455)
      | ~ r1_tmap_1(C_456,A_457,E_458,k3_funct_2(u1_struct_0(B_453),u1_struct_0(C_456),D_454,F_455))
      | ~ r1_tmap_1(B_453,C_456,D_454,F_455)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_453),u1_struct_0(C_456),D_454,F_455),u1_struct_0(C_456))
      | ~ m1_subset_1(F_455,u1_struct_0(B_453))
      | ~ m1_subset_1(E_458,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_456),u1_struct_0(A_457))))
      | ~ v1_funct_2(E_458,u1_struct_0(C_456),u1_struct_0(A_457))
      | ~ v1_funct_1(E_458)
      | ~ m1_subset_1(D_454,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_453),u1_struct_0(C_456))))
      | ~ v1_funct_2(D_454,u1_struct_0(B_453),u1_struct_0(C_456))
      | ~ v1_funct_1(D_454)
      | ~ l1_pre_topc(C_456)
      | ~ v2_pre_topc(C_456)
      | v2_struct_0(C_456)
      | ~ l1_pre_topc(B_453)
      | ~ v2_pre_topc(B_453)
      | v2_struct_0(B_453)
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    ~ r1_tmap_1('#skF_8','#skF_6',k1_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_9','#skF_10'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1074,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_6','#skF_10',k3_funct_2(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9','#skF_12'))
    | ~ r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12')
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9','#skF_12'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_10',u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_10')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1068,c_52])).

tff(c_1078,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_76,c_84,c_82,c_74,c_72,c_70,c_68,c_66,c_64,c_56,c_62,c_547,c_1039,c_58,c_547,c_1074])).

tff(c_1080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_86,c_1078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.85  
% 4.90/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.86  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k3_funct_2 > k6_domain_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 4.90/1.86  
% 4.90/1.86  %Foreground sorts:
% 4.90/1.86  
% 4.90/1.86  
% 4.90/1.86  %Background operators:
% 4.90/1.86  
% 4.90/1.86  
% 4.90/1.86  %Foreground operators:
% 4.90/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.90/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.90/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.90/1.86  tff('#skF_11', type, '#skF_11': $i).
% 4.90/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.90/1.86  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.90/1.86  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.90/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.90/1.86  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.90/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.90/1.86  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.90/1.86  tff('#skF_10', type, '#skF_10': $i).
% 4.90/1.86  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.90/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.90/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.90/1.86  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.90/1.86  tff('#skF_9', type, '#skF_9': $i).
% 4.90/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.90/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.90/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.90/1.86  tff('#skF_8', type, '#skF_8': $i).
% 4.90/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.86  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.90/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.90/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.90/1.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.90/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.90/1.86  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.90/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.90/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.90/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.90/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.90/1.86  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.90/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.90/1.86  tff('#skF_12', type, '#skF_12': $i).
% 4.90/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.90/1.86  
% 4.90/1.88  tff(f_218, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => ((v5_pre_topc(D, C, B) & r1_tmap_1(B, A, E, F)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (r2_hidden(G, k8_relset_1(u1_struct_0(C), u1_struct_0(B), D, k6_domain_1(u1_struct_0(B), F))) => r1_tmap_1(C, A, k1_partfun1(u1_struct_0(C), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), D, E), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tmap_1)).
% 4.90/1.88  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.90/1.89  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.90/1.89  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.90/1.89  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.90/1.89  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.90/1.89  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 4.90/1.89  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.90/1.89  tff(f_67, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.90/1.89  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 4.90/1.89  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tmap_1)).
% 4.90/1.89  tff(c_92, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_80, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_86, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_90, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_88, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_78, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_76, plain, (l1_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_84, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_82, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_74, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_72, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_70, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_68, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_66, plain, (v1_funct_2('#skF_10', u1_struct_0('#skF_7'), u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_64, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_56, plain, (m1_subset_1('#skF_12', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_62, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_32, plain, (![C_20, A_18, B_19]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.90/1.89  tff(c_110, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_32])).
% 4.90/1.89  tff(c_195, plain, (![A_325, B_326, C_327, D_328]: (k8_relset_1(A_325, B_326, C_327, D_328)=k10_relat_1(C_327, D_328) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.90/1.89  tff(c_200, plain, (![D_328]: (k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', D_328)=k10_relat_1('#skF_9', D_328))), inference(resolution, [status(thm)], [c_70, c_195])).
% 4.90/1.89  tff(c_38, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.90/1.89  tff(c_111, plain, (![A_310, B_311]: (k6_domain_1(A_310, B_311)=k1_tarski(B_311) | ~m1_subset_1(B_311, A_310) | v1_xboole_0(A_310))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.90/1.89  tff(c_126, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')=k1_tarski('#skF_11') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_111])).
% 4.90/1.89  tff(c_128, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_126])).
% 4.90/1.89  tff(c_40, plain, (![A_30]: (~v1_xboole_0(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.90/1.89  tff(c_131, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_128, c_40])).
% 4.90/1.89  tff(c_134, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_86, c_131])).
% 4.90/1.89  tff(c_137, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_134])).
% 4.90/1.89  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_137])).
% 4.90/1.89  tff(c_142, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')=k1_tarski('#skF_11')), inference(splitRight, [status(thm)], [c_126])).
% 4.90/1.89  tff(c_54, plain, (r2_hidden('#skF_12', k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_169, plain, (r2_hidden('#skF_12', k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_54])).
% 4.90/1.89  tff(c_202, plain, (r2_hidden('#skF_12', k10_relat_1('#skF_9', k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_169])).
% 4.90/1.89  tff(c_227, plain, (![A_331, D_332, B_333]: (r2_hidden(k1_funct_1(A_331, D_332), B_333) | ~r2_hidden(D_332, k10_relat_1(A_331, B_333)) | ~v1_funct_1(A_331) | ~v1_relat_1(A_331))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.90/1.89  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.90/1.89  tff(c_261, plain, (![A_336, D_337, A_338]: (k1_funct_1(A_336, D_337)=A_338 | ~r2_hidden(D_337, k10_relat_1(A_336, k1_tarski(A_338))) | ~v1_funct_1(A_336) | ~v1_relat_1(A_336))), inference(resolution, [status(thm)], [c_227, c_2])).
% 4.90/1.89  tff(c_268, plain, (k1_funct_1('#skF_9', '#skF_12')='#skF_11' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_202, c_261])).
% 4.90/1.89  tff(c_280, plain, (k1_funct_1('#skF_9', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74, c_268])).
% 4.90/1.89  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_8'), '#skF_12')=k1_tarski('#skF_12') | v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_111])).
% 4.90/1.89  tff(c_148, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_127])).
% 4.90/1.89  tff(c_151, plain, (~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_148, c_40])).
% 4.90/1.89  tff(c_154, plain, (~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_80, c_151])).
% 4.90/1.89  tff(c_158, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_38, c_154])).
% 4.90/1.89  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_158])).
% 4.90/1.89  tff(c_164, plain, (~v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_127])).
% 4.90/1.89  tff(c_506, plain, (![A_365, B_366, C_367, D_368]: (k3_funct_2(A_365, B_366, C_367, D_368)=k1_funct_1(C_367, D_368) | ~m1_subset_1(D_368, A_365) | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(A_365, B_366))) | ~v1_funct_2(C_367, A_365, B_366) | ~v1_funct_1(C_367) | v1_xboole_0(A_365))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.90/1.89  tff(c_514, plain, (![B_366, C_367]: (k3_funct_2(u1_struct_0('#skF_8'), B_366, C_367, '#skF_12')=k1_funct_1(C_367, '#skF_12') | ~m1_subset_1(C_367, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), B_366))) | ~v1_funct_2(C_367, u1_struct_0('#skF_8'), B_366) | ~v1_funct_1(C_367) | v1_xboole_0(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_56, c_506])).
% 4.90/1.89  tff(c_541, plain, (![B_383, C_384]: (k3_funct_2(u1_struct_0('#skF_8'), B_383, C_384, '#skF_12')=k1_funct_1(C_384, '#skF_12') | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), B_383))) | ~v1_funct_2(C_384, u1_struct_0('#skF_8'), B_383) | ~v1_funct_1(C_384))), inference(negUnitSimplification, [status(thm)], [c_164, c_514])).
% 4.90/1.89  tff(c_544, plain, (k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')=k1_funct_1('#skF_9', '#skF_12') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_541])).
% 4.90/1.89  tff(c_547, plain, (k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_280, c_544])).
% 4.90/1.89  tff(c_60, plain, (v5_pre_topc('#skF_9', '#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_1011, plain, (![B_442, A_443, C_444, D_445]: (r1_tmap_1(B_442, A_443, C_444, D_445) | ~m1_subset_1(D_445, u1_struct_0(B_442)) | ~v5_pre_topc(C_444, B_442, A_443) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_442), u1_struct_0(A_443)))) | ~v1_funct_2(C_444, u1_struct_0(B_442), u1_struct_0(A_443)) | ~v1_funct_1(C_444) | ~l1_pre_topc(B_442) | ~v2_pre_topc(B_442) | v2_struct_0(B_442) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.90/1.89  tff(c_1015, plain, (![A_443, C_444]: (r1_tmap_1('#skF_8', A_443, C_444, '#skF_12') | ~v5_pre_topc(C_444, '#skF_8', A_443) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_443)))) | ~v1_funct_2(C_444, u1_struct_0('#skF_8'), u1_struct_0(A_443)) | ~v1_funct_1(C_444) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(resolution, [status(thm)], [c_56, c_1011])).
% 4.90/1.89  tff(c_1022, plain, (![A_443, C_444]: (r1_tmap_1('#skF_8', A_443, C_444, '#skF_12') | ~v5_pre_topc(C_444, '#skF_8', A_443) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_443)))) | ~v1_funct_2(C_444, u1_struct_0('#skF_8'), u1_struct_0(A_443)) | ~v1_funct_1(C_444) | v2_struct_0('#skF_8') | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1015])).
% 4.90/1.89  tff(c_1032, plain, (![A_448, C_449]: (r1_tmap_1('#skF_8', A_448, C_449, '#skF_12') | ~v5_pre_topc(C_449, '#skF_8', A_448) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_448)))) | ~v1_funct_2(C_449, u1_struct_0('#skF_8'), u1_struct_0(A_448)) | ~v1_funct_1(C_449) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | v2_struct_0(A_448))), inference(negUnitSimplification, [status(thm)], [c_80, c_1022])).
% 4.90/1.89  tff(c_1035, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | ~v5_pre_topc('#skF_9', '#skF_8', '#skF_7') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_70, c_1032])).
% 4.90/1.89  tff(c_1038, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_74, c_72, c_60, c_1035])).
% 4.90/1.89  tff(c_1039, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_86, c_1038])).
% 4.90/1.89  tff(c_58, plain, (r1_tmap_1('#skF_7', '#skF_6', '#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_1068, plain, (![B_453, C_456, E_458, D_454, F_455, A_457]: (r1_tmap_1(B_453, A_457, k1_partfun1(u1_struct_0(B_453), u1_struct_0(C_456), u1_struct_0(C_456), u1_struct_0(A_457), D_454, E_458), F_455) | ~r1_tmap_1(C_456, A_457, E_458, k3_funct_2(u1_struct_0(B_453), u1_struct_0(C_456), D_454, F_455)) | ~r1_tmap_1(B_453, C_456, D_454, F_455) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_453), u1_struct_0(C_456), D_454, F_455), u1_struct_0(C_456)) | ~m1_subset_1(F_455, u1_struct_0(B_453)) | ~m1_subset_1(E_458, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_456), u1_struct_0(A_457)))) | ~v1_funct_2(E_458, u1_struct_0(C_456), u1_struct_0(A_457)) | ~v1_funct_1(E_458) | ~m1_subset_1(D_454, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_453), u1_struct_0(C_456)))) | ~v1_funct_2(D_454, u1_struct_0(B_453), u1_struct_0(C_456)) | ~v1_funct_1(D_454) | ~l1_pre_topc(C_456) | ~v2_pre_topc(C_456) | v2_struct_0(C_456) | ~l1_pre_topc(B_453) | ~v2_pre_topc(B_453) | v2_struct_0(B_453) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.90/1.89  tff(c_52, plain, (~r1_tmap_1('#skF_8', '#skF_6', k1_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), '#skF_9', '#skF_10'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_218])).
% 4.90/1.89  tff(c_1074, plain, (~r1_tmap_1('#skF_7', '#skF_6', '#skF_10', k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')) | ~r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_10', u1_struct_0('#skF_7'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_10') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1068, c_52])).
% 4.90/1.89  tff(c_1078, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_76, c_84, c_82, c_74, c_72, c_70, c_68, c_66, c_64, c_56, c_62, c_547, c_1039, c_58, c_547, c_1074])).
% 4.90/1.89  tff(c_1080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_86, c_1078])).
% 4.90/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.89  
% 4.90/1.89  Inference rules
% 4.90/1.89  ----------------------
% 4.90/1.89  #Ref     : 0
% 4.90/1.89  #Sup     : 199
% 4.90/1.89  #Fact    : 0
% 4.90/1.89  #Define  : 0
% 4.90/1.89  #Split   : 5
% 4.90/1.89  #Chain   : 0
% 4.90/1.89  #Close   : 0
% 4.90/1.89  
% 4.90/1.89  Ordering : KBO
% 4.90/1.89  
% 4.90/1.89  Simplification rules
% 4.90/1.89  ----------------------
% 4.90/1.89  #Subsume      : 15
% 4.90/1.89  #Demod        : 120
% 4.90/1.89  #Tautology    : 55
% 4.90/1.89  #SimpNegUnit  : 11
% 4.90/1.89  #BackRed      : 1
% 4.90/1.89  
% 4.90/1.89  #Partial instantiations: 0
% 4.90/1.89  #Strategies tried      : 1
% 4.90/1.89  
% 4.90/1.89  Timing (in seconds)
% 4.90/1.89  ----------------------
% 4.90/1.89  Preprocessing        : 0.41
% 4.90/1.89  Parsing              : 0.20
% 4.90/1.89  CNF conversion       : 0.05
% 4.90/1.89  Main loop            : 0.68
% 4.90/1.89  Inferencing          : 0.25
% 4.90/1.89  Reduction            : 0.19
% 4.90/1.89  Demodulation         : 0.14
% 4.90/1.89  BG Simplification    : 0.04
% 4.90/1.89  Subsumption          : 0.14
% 4.90/1.89  Abstraction          : 0.04
% 4.90/1.89  MUC search           : 0.00
% 4.90/1.89  Cooper               : 0.00
% 4.90/1.89  Total                : 1.15
% 4.90/1.89  Index Insertion      : 0.00
% 4.90/1.89  Index Deletion       : 0.00
% 4.90/1.89  Index Matching       : 0.00
% 4.90/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
