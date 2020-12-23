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

% Result     : Theorem 4.97s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 266 expanded)
%              Number of leaves         :   52 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  313 (1718 expanded)
%              Number of equality atoms :   22 (  53 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k3_funct_2 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k1_connsp_2 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_243,negated_conjecture,(
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
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_64,axiom,(
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

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_140,axiom,(
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

tff(f_191,axiom,(
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

tff(c_98,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_96,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_94,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_84,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_82,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_90,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_88,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_80,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_78,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_76,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_74,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_72,plain,(
    v1_funct_2('#skF_10',u1_struct_0('#skF_7'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_70,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_62,plain,(
    m1_subset_1('#skF_12',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_68,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_116,plain,(
    ! [B_317,A_318] :
      ( v1_relat_1(B_317)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(A_318))
      | ~ v1_relat_1(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_76,c_116])).

tff(c_125,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_626,plain,(
    ! [A_424,B_425,C_426,D_427] :
      ( k8_relset_1(A_424,B_425,C_426,D_427) = k10_relat_1(C_426,D_427)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_631,plain,(
    ! [D_427] : k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',D_427) = k10_relat_1('#skF_9',D_427) ),
    inference(resolution,[status(thm)],[c_76,c_626])).

tff(c_138,plain,(
    ! [A_322,B_323] :
      ( k6_domain_1(A_322,B_323) = k1_tarski(B_323)
      | ~ m1_subset_1(B_323,A_322)
      | v1_xboole_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_154,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_11') = k1_tarski('#skF_11')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_68,c_138])).

tff(c_386,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_48,plain,(
    ! [B_41,A_39] :
      ( r2_hidden(B_41,k1_connsp_2(A_39,B_41))
      | ~ m1_subset_1(B_41,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_496,plain,(
    ! [A_399,B_400] :
      ( m1_subset_1(k1_connsp_2(A_399,B_400),k1_zfmisc_1(u1_struct_0(A_399)))
      | ~ m1_subset_1(B_400,u1_struct_0(A_399))
      | ~ l1_pre_topc(A_399)
      | ~ v2_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_557,plain,(
    ! [A_408,A_409,B_410] :
      ( ~ v1_xboole_0(u1_struct_0(A_408))
      | ~ r2_hidden(A_409,k1_connsp_2(A_408,B_410))
      | ~ m1_subset_1(B_410,u1_struct_0(A_408))
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_496,c_16])).

tff(c_577,plain,(
    ! [A_411,B_412] :
      ( ~ v1_xboole_0(u1_struct_0(A_411))
      | ~ m1_subset_1(B_412,u1_struct_0(A_411))
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_48,c_557])).

tff(c_583,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_577])).

tff(c_590,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_386,c_583])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_590])).

tff(c_593,plain,(
    k6_domain_1(u1_struct_0('#skF_7'),'#skF_11') = k1_tarski('#skF_11') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_60,plain,(
    r2_hidden('#skF_12',k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',k6_domain_1(u1_struct_0('#skF_7'),'#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_595,plain,(
    r2_hidden('#skF_12',k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_60])).

tff(c_633,plain,(
    r2_hidden('#skF_12',k10_relat_1('#skF_9',k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_595])).

tff(c_649,plain,(
    ! [A_429,D_430,B_431] :
      ( r2_hidden(k1_funct_1(A_429,D_430),B_431)
      | ~ r2_hidden(D_430,k10_relat_1(A_429,B_431))
      | ~ v1_funct_1(A_429)
      | ~ v1_relat_1(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_693,plain,(
    ! [A_435,D_436,A_437] :
      ( k1_funct_1(A_435,D_436) = A_437
      | ~ r2_hidden(D_436,k10_relat_1(A_435,k1_tarski(A_437)))
      | ~ v1_funct_1(A_435)
      | ~ v1_relat_1(A_435) ) ),
    inference(resolution,[status(thm)],[c_649,c_2])).

tff(c_700,plain,
    ( k1_funct_1('#skF_9','#skF_12') = '#skF_11'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_633,c_693])).

tff(c_712,plain,(
    k1_funct_1('#skF_9','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_80,c_700])).

tff(c_153,plain,
    ( k6_domain_1(u1_struct_0('#skF_8'),'#skF_12') = k1_tarski('#skF_12')
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_62,c_138])).

tff(c_155,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_266,plain,(
    ! [A_353,B_354] :
      ( m1_subset_1(k1_connsp_2(A_353,B_354),k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ m1_subset_1(B_354,u1_struct_0(A_353))
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_343,plain,(
    ! [A_365,A_366,B_367] :
      ( ~ v1_xboole_0(u1_struct_0(A_365))
      | ~ r2_hidden(A_366,k1_connsp_2(A_365,B_367))
      | ~ m1_subset_1(B_367,u1_struct_0(A_365))
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(resolution,[status(thm)],[c_266,c_16])).

tff(c_368,plain,(
    ! [A_368,B_369] :
      ( ~ v1_xboole_0(u1_struct_0(A_368))
      | ~ m1_subset_1(B_369,u1_struct_0(A_368))
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368)
      | v2_struct_0(A_368) ) ),
    inference(resolution,[status(thm)],[c_48,c_343])).

tff(c_371,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_8'))
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_368])).

tff(c_377,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_155,c_371])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_377])).

tff(c_381,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_1014,plain,(
    ! [A_484,B_485,C_486,D_487] :
      ( k3_funct_2(A_484,B_485,C_486,D_487) = k1_funct_1(C_486,D_487)
      | ~ m1_subset_1(D_487,A_484)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1(A_484,B_485)))
      | ~ v1_funct_2(C_486,A_484,B_485)
      | ~ v1_funct_1(C_486)
      | v1_xboole_0(A_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1022,plain,(
    ! [B_485,C_486] :
      ( k3_funct_2(u1_struct_0('#skF_8'),B_485,C_486,'#skF_12') = k1_funct_1(C_486,'#skF_12')
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),B_485)))
      | ~ v1_funct_2(C_486,u1_struct_0('#skF_8'),B_485)
      | ~ v1_funct_1(C_486)
      | v1_xboole_0(u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_62,c_1014])).

tff(c_1036,plain,(
    ! [B_488,C_489] :
      ( k3_funct_2(u1_struct_0('#skF_8'),B_488,C_489,'#skF_12') = k1_funct_1(C_489,'#skF_12')
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),B_488)))
      | ~ v1_funct_2(C_489,u1_struct_0('#skF_8'),B_488)
      | ~ v1_funct_1(C_489) ) ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_1022])).

tff(c_1039,plain,
    ( k3_funct_2(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9','#skF_12') = k1_funct_1('#skF_9','#skF_12')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_1036])).

tff(c_1042,plain,(
    k3_funct_2(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_712,c_1039])).

tff(c_66,plain,(
    v5_pre_topc('#skF_9','#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_1795,plain,(
    ! [B_584,A_585,C_586,D_587] :
      ( r1_tmap_1(B_584,A_585,C_586,D_587)
      | ~ m1_subset_1(D_587,u1_struct_0(B_584))
      | ~ v5_pre_topc(C_586,B_584,A_585)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_584),u1_struct_0(A_585))))
      | ~ v1_funct_2(C_586,u1_struct_0(B_584),u1_struct_0(A_585))
      | ~ v1_funct_1(C_586)
      | ~ l1_pre_topc(B_584)
      | ~ v2_pre_topc(B_584)
      | v2_struct_0(B_584)
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1797,plain,(
    ! [A_585,C_586] :
      ( r1_tmap_1('#skF_8',A_585,C_586,'#skF_12')
      | ~ v5_pre_topc(C_586,'#skF_8',A_585)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_585))))
      | ~ v1_funct_2(C_586,u1_struct_0('#skF_8'),u1_struct_0(A_585))
      | ~ v1_funct_1(C_586)
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(resolution,[status(thm)],[c_62,c_1795])).

tff(c_1802,plain,(
    ! [A_585,C_586] :
      ( r1_tmap_1('#skF_8',A_585,C_586,'#skF_12')
      | ~ v5_pre_topc(C_586,'#skF_8',A_585)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_585))))
      | ~ v1_funct_2(C_586,u1_struct_0('#skF_8'),u1_struct_0(A_585))
      | ~ v1_funct_1(C_586)
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_1797])).

tff(c_1808,plain,(
    ! [A_588,C_589] :
      ( r1_tmap_1('#skF_8',A_588,C_589,'#skF_12')
      | ~ v5_pre_topc(C_589,'#skF_8',A_588)
      | ~ m1_subset_1(C_589,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_588))))
      | ~ v1_funct_2(C_589,u1_struct_0('#skF_8'),u1_struct_0(A_588))
      | ~ v1_funct_1(C_589)
      | ~ l1_pre_topc(A_588)
      | ~ v2_pre_topc(A_588)
      | v2_struct_0(A_588) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1802])).

tff(c_1811,plain,
    ( r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12')
    | ~ v5_pre_topc('#skF_9','#skF_8','#skF_7')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_1808])).

tff(c_1814,plain,
    ( r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_80,c_78,c_66,c_1811])).

tff(c_1815,plain,(
    r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1814])).

tff(c_64,plain,(
    r1_tmap_1('#skF_7','#skF_6','#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_1824,plain,(
    ! [A_595,D_594,B_593,F_592,E_596,C_597] :
      ( r1_tmap_1(B_593,A_595,k1_partfun1(u1_struct_0(B_593),u1_struct_0(C_597),u1_struct_0(C_597),u1_struct_0(A_595),D_594,E_596),F_592)
      | ~ r1_tmap_1(C_597,A_595,E_596,k3_funct_2(u1_struct_0(B_593),u1_struct_0(C_597),D_594,F_592))
      | ~ r1_tmap_1(B_593,C_597,D_594,F_592)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_593),u1_struct_0(C_597),D_594,F_592),u1_struct_0(C_597))
      | ~ m1_subset_1(F_592,u1_struct_0(B_593))
      | ~ m1_subset_1(E_596,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_597),u1_struct_0(A_595))))
      | ~ v1_funct_2(E_596,u1_struct_0(C_597),u1_struct_0(A_595))
      | ~ v1_funct_1(E_596)
      | ~ m1_subset_1(D_594,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_593),u1_struct_0(C_597))))
      | ~ v1_funct_2(D_594,u1_struct_0(B_593),u1_struct_0(C_597))
      | ~ v1_funct_1(D_594)
      | ~ l1_pre_topc(C_597)
      | ~ v2_pre_topc(C_597)
      | v2_struct_0(C_597)
      | ~ l1_pre_topc(B_593)
      | ~ v2_pre_topc(B_593)
      | v2_struct_0(B_593)
      | ~ l1_pre_topc(A_595)
      | ~ v2_pre_topc(A_595)
      | v2_struct_0(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_58,plain,(
    ~ r1_tmap_1('#skF_8','#skF_6',k1_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_9','#skF_10'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_1830,plain,
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
    inference(resolution,[status(thm)],[c_1824,c_58])).

tff(c_1834,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_82,c_90,c_88,c_80,c_78,c_76,c_74,c_72,c_70,c_62,c_68,c_1042,c_1815,c_64,c_1042,c_1830])).

tff(c_1836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_86,c_92,c_1834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.98  
% 4.97/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.98  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k3_funct_2 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k1_connsp_2 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 4.97/1.98  
% 4.97/1.98  %Foreground sorts:
% 4.97/1.98  
% 4.97/1.98  
% 4.97/1.98  %Background operators:
% 4.97/1.98  
% 4.97/1.98  
% 4.97/1.98  %Foreground operators:
% 4.97/1.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.97/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.97/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.97/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.97/1.98  tff('#skF_11', type, '#skF_11': $i).
% 4.97/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.97/1.98  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 4.97/1.98  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.97/1.98  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.97/1.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.97/1.98  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.97/1.98  tff('#skF_7', type, '#skF_7': $i).
% 4.97/1.98  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.97/1.98  tff('#skF_10', type, '#skF_10': $i).
% 4.97/1.98  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.97/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.97/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.97/1.98  tff('#skF_6', type, '#skF_6': $i).
% 4.97/1.98  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.97/1.98  tff('#skF_9', type, '#skF_9': $i).
% 4.97/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.97/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.97/1.98  tff('#skF_8', type, '#skF_8': $i).
% 4.97/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.97/1.98  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.97/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.97/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.97/1.98  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.97/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.97/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.97/1.98  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.97/1.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.97/1.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.97/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.97/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.97/1.98  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.97/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.97/1.98  tff('#skF_12', type, '#skF_12': $i).
% 4.97/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.97/1.98  
% 5.34/2.00  tff(f_243, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => ((v5_pre_topc(D, C, B) & r1_tmap_1(B, A, E, F)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (r2_hidden(G, k8_relset_1(u1_struct_0(C), u1_struct_0(B), D, k6_domain_1(u1_struct_0(B), F))) => r1_tmap_1(C, A, k1_partfun1(u1_struct_0(C), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), D, E), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tmap_1)).
% 5.34/2.00  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.34/2.00  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.34/2.00  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.34/2.00  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.34/2.00  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 5.34/2.00  tff(f_99, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 5.34/2.00  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.34/2.00  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 5.34/2.00  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.34/2.00  tff(f_81, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.34/2.00  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 5.34/2.00  tff(f_191, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tmap_1)).
% 5.34/2.00  tff(c_98, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_86, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_92, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_96, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_94, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_84, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_82, plain, (l1_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_90, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_88, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_80, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_78, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_76, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_74, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_72, plain, (v1_funct_2('#skF_10', u1_struct_0('#skF_7'), u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_70, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_62, plain, (m1_subset_1('#skF_12', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_68, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.34/2.00  tff(c_116, plain, (![B_317, A_318]: (v1_relat_1(B_317) | ~m1_subset_1(B_317, k1_zfmisc_1(A_318)) | ~v1_relat_1(A_318))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.34/2.00  tff(c_119, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_76, c_116])).
% 5.34/2.00  tff(c_125, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_119])).
% 5.34/2.00  tff(c_626, plain, (![A_424, B_425, C_426, D_427]: (k8_relset_1(A_424, B_425, C_426, D_427)=k10_relat_1(C_426, D_427) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.34/2.00  tff(c_631, plain, (![D_427]: (k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', D_427)=k10_relat_1('#skF_9', D_427))), inference(resolution, [status(thm)], [c_76, c_626])).
% 5.34/2.00  tff(c_138, plain, (![A_322, B_323]: (k6_domain_1(A_322, B_323)=k1_tarski(B_323) | ~m1_subset_1(B_323, A_322) | v1_xboole_0(A_322))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.34/2.00  tff(c_154, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')=k1_tarski('#skF_11') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_138])).
% 5.34/2.00  tff(c_386, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_154])).
% 5.34/2.00  tff(c_48, plain, (![B_41, A_39]: (r2_hidden(B_41, k1_connsp_2(A_39, B_41)) | ~m1_subset_1(B_41, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.34/2.00  tff(c_496, plain, (![A_399, B_400]: (m1_subset_1(k1_connsp_2(A_399, B_400), k1_zfmisc_1(u1_struct_0(A_399))) | ~m1_subset_1(B_400, u1_struct_0(A_399)) | ~l1_pre_topc(A_399) | ~v2_pre_topc(A_399) | v2_struct_0(A_399))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.34/2.00  tff(c_16, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.34/2.00  tff(c_557, plain, (![A_408, A_409, B_410]: (~v1_xboole_0(u1_struct_0(A_408)) | ~r2_hidden(A_409, k1_connsp_2(A_408, B_410)) | ~m1_subset_1(B_410, u1_struct_0(A_408)) | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(resolution, [status(thm)], [c_496, c_16])).
% 5.34/2.00  tff(c_577, plain, (![A_411, B_412]: (~v1_xboole_0(u1_struct_0(A_411)) | ~m1_subset_1(B_412, u1_struct_0(A_411)) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(resolution, [status(thm)], [c_48, c_557])).
% 5.34/2.00  tff(c_583, plain, (~v1_xboole_0(u1_struct_0('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_68, c_577])).
% 5.34/2.00  tff(c_590, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_386, c_583])).
% 5.34/2.00  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_590])).
% 5.34/2.00  tff(c_593, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')=k1_tarski('#skF_11')), inference(splitRight, [status(thm)], [c_154])).
% 5.34/2.00  tff(c_60, plain, (r2_hidden('#skF_12', k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_595, plain, (r2_hidden('#skF_12', k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_593, c_60])).
% 5.34/2.00  tff(c_633, plain, (r2_hidden('#skF_12', k10_relat_1('#skF_9', k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_631, c_595])).
% 5.34/2.00  tff(c_649, plain, (![A_429, D_430, B_431]: (r2_hidden(k1_funct_1(A_429, D_430), B_431) | ~r2_hidden(D_430, k10_relat_1(A_429, B_431)) | ~v1_funct_1(A_429) | ~v1_relat_1(A_429))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.34/2.00  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.34/2.00  tff(c_693, plain, (![A_435, D_436, A_437]: (k1_funct_1(A_435, D_436)=A_437 | ~r2_hidden(D_436, k10_relat_1(A_435, k1_tarski(A_437))) | ~v1_funct_1(A_435) | ~v1_relat_1(A_435))), inference(resolution, [status(thm)], [c_649, c_2])).
% 5.34/2.00  tff(c_700, plain, (k1_funct_1('#skF_9', '#skF_12')='#skF_11' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_633, c_693])).
% 5.34/2.00  tff(c_712, plain, (k1_funct_1('#skF_9', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_80, c_700])).
% 5.34/2.00  tff(c_153, plain, (k6_domain_1(u1_struct_0('#skF_8'), '#skF_12')=k1_tarski('#skF_12') | v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_62, c_138])).
% 5.34/2.00  tff(c_155, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_153])).
% 5.34/2.00  tff(c_266, plain, (![A_353, B_354]: (m1_subset_1(k1_connsp_2(A_353, B_354), k1_zfmisc_1(u1_struct_0(A_353))) | ~m1_subset_1(B_354, u1_struct_0(A_353)) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.34/2.00  tff(c_343, plain, (![A_365, A_366, B_367]: (~v1_xboole_0(u1_struct_0(A_365)) | ~r2_hidden(A_366, k1_connsp_2(A_365, B_367)) | ~m1_subset_1(B_367, u1_struct_0(A_365)) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(resolution, [status(thm)], [c_266, c_16])).
% 5.34/2.00  tff(c_368, plain, (![A_368, B_369]: (~v1_xboole_0(u1_struct_0(A_368)) | ~m1_subset_1(B_369, u1_struct_0(A_368)) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368) | v2_struct_0(A_368))), inference(resolution, [status(thm)], [c_48, c_343])).
% 5.34/2.00  tff(c_371, plain, (~v1_xboole_0(u1_struct_0('#skF_8')) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_62, c_368])).
% 5.34/2.00  tff(c_377, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_155, c_371])).
% 5.34/2.00  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_377])).
% 5.34/2.00  tff(c_381, plain, (~v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_153])).
% 5.34/2.00  tff(c_1014, plain, (![A_484, B_485, C_486, D_487]: (k3_funct_2(A_484, B_485, C_486, D_487)=k1_funct_1(C_486, D_487) | ~m1_subset_1(D_487, A_484) | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1(A_484, B_485))) | ~v1_funct_2(C_486, A_484, B_485) | ~v1_funct_1(C_486) | v1_xboole_0(A_484))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.34/2.00  tff(c_1022, plain, (![B_485, C_486]: (k3_funct_2(u1_struct_0('#skF_8'), B_485, C_486, '#skF_12')=k1_funct_1(C_486, '#skF_12') | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), B_485))) | ~v1_funct_2(C_486, u1_struct_0('#skF_8'), B_485) | ~v1_funct_1(C_486) | v1_xboole_0(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_62, c_1014])).
% 5.34/2.00  tff(c_1036, plain, (![B_488, C_489]: (k3_funct_2(u1_struct_0('#skF_8'), B_488, C_489, '#skF_12')=k1_funct_1(C_489, '#skF_12') | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), B_488))) | ~v1_funct_2(C_489, u1_struct_0('#skF_8'), B_488) | ~v1_funct_1(C_489))), inference(negUnitSimplification, [status(thm)], [c_381, c_1022])).
% 5.34/2.00  tff(c_1039, plain, (k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')=k1_funct_1('#skF_9', '#skF_12') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_1036])).
% 5.34/2.00  tff(c_1042, plain, (k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_712, c_1039])).
% 5.34/2.00  tff(c_66, plain, (v5_pre_topc('#skF_9', '#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_1795, plain, (![B_584, A_585, C_586, D_587]: (r1_tmap_1(B_584, A_585, C_586, D_587) | ~m1_subset_1(D_587, u1_struct_0(B_584)) | ~v5_pre_topc(C_586, B_584, A_585) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_584), u1_struct_0(A_585)))) | ~v1_funct_2(C_586, u1_struct_0(B_584), u1_struct_0(A_585)) | ~v1_funct_1(C_586) | ~l1_pre_topc(B_584) | ~v2_pre_topc(B_584) | v2_struct_0(B_584) | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585) | v2_struct_0(A_585))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.34/2.00  tff(c_1797, plain, (![A_585, C_586]: (r1_tmap_1('#skF_8', A_585, C_586, '#skF_12') | ~v5_pre_topc(C_586, '#skF_8', A_585) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_585)))) | ~v1_funct_2(C_586, u1_struct_0('#skF_8'), u1_struct_0(A_585)) | ~v1_funct_1(C_586) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585) | v2_struct_0(A_585))), inference(resolution, [status(thm)], [c_62, c_1795])).
% 5.34/2.00  tff(c_1802, plain, (![A_585, C_586]: (r1_tmap_1('#skF_8', A_585, C_586, '#skF_12') | ~v5_pre_topc(C_586, '#skF_8', A_585) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_585)))) | ~v1_funct_2(C_586, u1_struct_0('#skF_8'), u1_struct_0(A_585)) | ~v1_funct_1(C_586) | v2_struct_0('#skF_8') | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585) | v2_struct_0(A_585))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_1797])).
% 5.34/2.00  tff(c_1808, plain, (![A_588, C_589]: (r1_tmap_1('#skF_8', A_588, C_589, '#skF_12') | ~v5_pre_topc(C_589, '#skF_8', A_588) | ~m1_subset_1(C_589, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_588)))) | ~v1_funct_2(C_589, u1_struct_0('#skF_8'), u1_struct_0(A_588)) | ~v1_funct_1(C_589) | ~l1_pre_topc(A_588) | ~v2_pre_topc(A_588) | v2_struct_0(A_588))), inference(negUnitSimplification, [status(thm)], [c_86, c_1802])).
% 5.34/2.00  tff(c_1811, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | ~v5_pre_topc('#skF_9', '#skF_8', '#skF_7') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_76, c_1808])).
% 5.34/2.00  tff(c_1814, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_80, c_78, c_66, c_1811])).
% 5.34/2.00  tff(c_1815, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_92, c_1814])).
% 5.34/2.00  tff(c_64, plain, (r1_tmap_1('#skF_7', '#skF_6', '#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_1824, plain, (![A_595, D_594, B_593, F_592, E_596, C_597]: (r1_tmap_1(B_593, A_595, k1_partfun1(u1_struct_0(B_593), u1_struct_0(C_597), u1_struct_0(C_597), u1_struct_0(A_595), D_594, E_596), F_592) | ~r1_tmap_1(C_597, A_595, E_596, k3_funct_2(u1_struct_0(B_593), u1_struct_0(C_597), D_594, F_592)) | ~r1_tmap_1(B_593, C_597, D_594, F_592) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_593), u1_struct_0(C_597), D_594, F_592), u1_struct_0(C_597)) | ~m1_subset_1(F_592, u1_struct_0(B_593)) | ~m1_subset_1(E_596, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_597), u1_struct_0(A_595)))) | ~v1_funct_2(E_596, u1_struct_0(C_597), u1_struct_0(A_595)) | ~v1_funct_1(E_596) | ~m1_subset_1(D_594, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_593), u1_struct_0(C_597)))) | ~v1_funct_2(D_594, u1_struct_0(B_593), u1_struct_0(C_597)) | ~v1_funct_1(D_594) | ~l1_pre_topc(C_597) | ~v2_pre_topc(C_597) | v2_struct_0(C_597) | ~l1_pre_topc(B_593) | ~v2_pre_topc(B_593) | v2_struct_0(B_593) | ~l1_pre_topc(A_595) | ~v2_pre_topc(A_595) | v2_struct_0(A_595))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.34/2.00  tff(c_58, plain, (~r1_tmap_1('#skF_8', '#skF_6', k1_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), '#skF_9', '#skF_10'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_243])).
% 5.34/2.00  tff(c_1830, plain, (~r1_tmap_1('#skF_7', '#skF_6', '#skF_10', k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')) | ~r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_10', u1_struct_0('#skF_7'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_10') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1824, c_58])).
% 5.34/2.00  tff(c_1834, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_82, c_90, c_88, c_80, c_78, c_76, c_74, c_72, c_70, c_62, c_68, c_1042, c_1815, c_64, c_1042, c_1830])).
% 5.34/2.00  tff(c_1836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_86, c_92, c_1834])).
% 5.34/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.34/2.00  
% 5.34/2.00  Inference rules
% 5.34/2.00  ----------------------
% 5.34/2.00  #Ref     : 0
% 5.34/2.00  #Sup     : 344
% 5.34/2.00  #Fact    : 0
% 5.34/2.00  #Define  : 0
% 5.34/2.00  #Split   : 18
% 5.34/2.00  #Chain   : 0
% 5.34/2.00  #Close   : 0
% 5.34/2.00  
% 5.34/2.00  Ordering : KBO
% 5.34/2.00  
% 5.34/2.00  Simplification rules
% 5.34/2.00  ----------------------
% 5.34/2.00  #Subsume      : 31
% 5.34/2.00  #Demod        : 173
% 5.34/2.00  #Tautology    : 94
% 5.34/2.00  #SimpNegUnit  : 20
% 5.34/2.00  #BackRed      : 4
% 5.34/2.00  
% 5.34/2.00  #Partial instantiations: 0
% 5.34/2.00  #Strategies tried      : 1
% 5.34/2.00  
% 5.34/2.00  Timing (in seconds)
% 5.34/2.00  ----------------------
% 5.34/2.00  Preprocessing        : 0.43
% 5.34/2.00  Parsing              : 0.22
% 5.34/2.00  CNF conversion       : 0.05
% 5.34/2.00  Main loop            : 0.72
% 5.34/2.00  Inferencing          : 0.26
% 5.34/2.00  Reduction            : 0.21
% 5.34/2.00  Demodulation         : 0.15
% 5.34/2.00  BG Simplification    : 0.04
% 5.34/2.00  Subsumption          : 0.15
% 5.34/2.00  Abstraction          : 0.05
% 5.34/2.00  MUC search           : 0.00
% 5.34/2.00  Cooper               : 0.00
% 5.34/2.00  Total                : 1.20
% 5.34/2.00  Index Insertion      : 0.00
% 5.34/2.01  Index Deletion       : 0.00
% 5.34/2.01  Index Matching       : 0.00
% 5.34/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
