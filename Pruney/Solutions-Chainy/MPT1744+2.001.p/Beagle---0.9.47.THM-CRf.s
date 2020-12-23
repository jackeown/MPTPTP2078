%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:48 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 260 expanded)
%              Number of leaves         :   51 ( 123 expanded)
%              Depth                    :   10
%              Number of atoms          :  307 (1706 expanded)
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

tff(f_238,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_94,axiom,(
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

tff(f_55,axiom,(
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

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_135,axiom,(
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

tff(f_186,axiom,(
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

tff(c_96,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_94,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_92,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_82,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_80,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_88,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_86,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_78,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_76,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_72,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_70,plain,(
    v1_funct_2('#skF_10',u1_struct_0('#skF_7'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_68,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_60,plain,(
    m1_subset_1('#skF_12',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_66,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_113,plain,(
    ! [C_313,A_314,B_315] :
      ( v1_relat_1(C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_120,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_113])).

tff(c_632,plain,(
    ! [A_419,B_420,C_421,D_422] :
      ( k8_relset_1(A_419,B_420,C_421,D_422) = k10_relat_1(C_421,D_422)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(A_419,B_420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_637,plain,(
    ! [D_422] : k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',D_422) = k10_relat_1('#skF_9',D_422) ),
    inference(resolution,[status(thm)],[c_74,c_632])).

tff(c_131,plain,(
    ! [A_319,B_320] :
      ( k6_domain_1(A_319,B_320) = k1_tarski(B_320)
      | ~ m1_subset_1(B_320,A_319)
      | v1_xboole_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_146,plain,
    ( k6_domain_1(u1_struct_0('#skF_7'),'#skF_11') = k1_tarski('#skF_11')
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_131])).

tff(c_148,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_46,plain,(
    ! [B_39,A_37] :
      ( r2_hidden(B_39,k1_connsp_2(A_37,B_39))
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_260,plain,(
    ! [A_350,B_351] :
      ( m1_subset_1(k1_connsp_2(A_350,B_351),k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ m1_subset_1(B_351,u1_struct_0(A_350))
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_315,plain,(
    ! [A_360,A_361,B_362] :
      ( ~ v1_xboole_0(u1_struct_0(A_360))
      | ~ r2_hidden(A_361,k1_connsp_2(A_360,B_362))
      | ~ m1_subset_1(B_362,u1_struct_0(A_360))
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_260,c_16])).

tff(c_340,plain,(
    ! [A_363,B_364] :
      ( ~ v1_xboole_0(u1_struct_0(A_363))
      | ~ m1_subset_1(B_364,u1_struct_0(A_363))
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_46,c_315])).

tff(c_343,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_340])).

tff(c_349,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_148,c_343])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_349])).

tff(c_352,plain,(
    k6_domain_1(u1_struct_0('#skF_7'),'#skF_11') = k1_tarski('#skF_11') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_58,plain,(
    r2_hidden('#skF_12',k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',k6_domain_1(u1_struct_0('#skF_7'),'#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_354,plain,(
    r2_hidden('#skF_12',k8_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9',k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_58])).

tff(c_650,plain,(
    r2_hidden('#skF_12',k10_relat_1('#skF_9',k1_tarski('#skF_11'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_354])).

tff(c_639,plain,(
    ! [A_423,D_424,B_425] :
      ( r2_hidden(k1_funct_1(A_423,D_424),B_425)
      | ~ r2_hidden(D_424,k10_relat_1(A_423,B_425))
      | ~ v1_funct_1(A_423)
      | ~ v1_relat_1(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_675,plain,(
    ! [A_428,D_429,A_430] :
      ( k1_funct_1(A_428,D_429) = A_430
      | ~ r2_hidden(D_429,k10_relat_1(A_428,k1_tarski(A_430)))
      | ~ v1_funct_1(A_428)
      | ~ v1_relat_1(A_428) ) ),
    inference(resolution,[status(thm)],[c_639,c_2])).

tff(c_678,plain,
    ( k1_funct_1('#skF_9','#skF_12') = '#skF_11'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_650,c_675])).

tff(c_693,plain,(
    k1_funct_1('#skF_9','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_78,c_678])).

tff(c_147,plain,
    ( k6_domain_1(u1_struct_0('#skF_8'),'#skF_12') = k1_tarski('#skF_12')
    | v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_131])).

tff(c_359,plain,(
    v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_491,plain,(
    ! [A_395,B_396] :
      ( m1_subset_1(k1_connsp_2(A_395,B_396),k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ m1_subset_1(B_396,u1_struct_0(A_395))
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_565,plain,(
    ! [A_403,A_404,B_405] :
      ( ~ v1_xboole_0(u1_struct_0(A_403))
      | ~ r2_hidden(A_404,k1_connsp_2(A_403,B_405))
      | ~ m1_subset_1(B_405,u1_struct_0(A_403))
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | v2_struct_0(A_403) ) ),
    inference(resolution,[status(thm)],[c_491,c_16])).

tff(c_585,plain,(
    ! [A_406,B_407] :
      ( ~ v1_xboole_0(u1_struct_0(A_406))
      | ~ m1_subset_1(B_407,u1_struct_0(A_406))
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_46,c_565])).

tff(c_591,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_8'))
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_585])).

tff(c_598,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_359,c_591])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_598])).

tff(c_602,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_1047,plain,(
    ! [A_480,B_481,C_482,D_483] :
      ( k3_funct_2(A_480,B_481,C_482,D_483) = k1_funct_1(C_482,D_483)
      | ~ m1_subset_1(D_483,A_480)
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(A_480,B_481)))
      | ~ v1_funct_2(C_482,A_480,B_481)
      | ~ v1_funct_1(C_482)
      | v1_xboole_0(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1057,plain,(
    ! [B_481,C_482] :
      ( k3_funct_2(u1_struct_0('#skF_8'),B_481,C_482,'#skF_12') = k1_funct_1(C_482,'#skF_12')
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),B_481)))
      | ~ v1_funct_2(C_482,u1_struct_0('#skF_8'),B_481)
      | ~ v1_funct_1(C_482)
      | v1_xboole_0(u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_60,c_1047])).

tff(c_1080,plain,(
    ! [B_486,C_487] :
      ( k3_funct_2(u1_struct_0('#skF_8'),B_486,C_487,'#skF_12') = k1_funct_1(C_487,'#skF_12')
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),B_486)))
      | ~ v1_funct_2(C_487,u1_struct_0('#skF_8'),B_486)
      | ~ v1_funct_1(C_487) ) ),
    inference(negUnitSimplification,[status(thm)],[c_602,c_1057])).

tff(c_1083,plain,
    ( k3_funct_2(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9','#skF_12') = k1_funct_1('#skF_9','#skF_12')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_1080])).

tff(c_1086,plain,(
    k3_funct_2(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),'#skF_9','#skF_12') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_693,c_1083])).

tff(c_64,plain,(
    v5_pre_topc('#skF_9','#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_1607,plain,(
    ! [B_558,A_559,C_560,D_561] :
      ( r1_tmap_1(B_558,A_559,C_560,D_561)
      | ~ m1_subset_1(D_561,u1_struct_0(B_558))
      | ~ v5_pre_topc(C_560,B_558,A_559)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_558),u1_struct_0(A_559))))
      | ~ v1_funct_2(C_560,u1_struct_0(B_558),u1_struct_0(A_559))
      | ~ v1_funct_1(C_560)
      | ~ l1_pre_topc(B_558)
      | ~ v2_pre_topc(B_558)
      | v2_struct_0(B_558)
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1611,plain,(
    ! [A_559,C_560] :
      ( r1_tmap_1('#skF_8',A_559,C_560,'#skF_12')
      | ~ v5_pre_topc(C_560,'#skF_8',A_559)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_559))))
      | ~ v1_funct_2(C_560,u1_struct_0('#skF_8'),u1_struct_0(A_559))
      | ~ v1_funct_1(C_560)
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559) ) ),
    inference(resolution,[status(thm)],[c_60,c_1607])).

tff(c_1618,plain,(
    ! [A_559,C_560] :
      ( r1_tmap_1('#skF_8',A_559,C_560,'#skF_12')
      | ~ v5_pre_topc(C_560,'#skF_8',A_559)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_559))))
      | ~ v1_funct_2(C_560,u1_struct_0('#skF_8'),u1_struct_0(A_559))
      | ~ v1_funct_1(C_560)
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_1611])).

tff(c_1628,plain,(
    ! [A_564,C_565] :
      ( r1_tmap_1('#skF_8',A_564,C_565,'#skF_12')
      | ~ v5_pre_topc(C_565,'#skF_8',A_564)
      | ~ m1_subset_1(C_565,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(A_564))))
      | ~ v1_funct_2(C_565,u1_struct_0('#skF_8'),u1_struct_0(A_564))
      | ~ v1_funct_1(C_565)
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1618])).

tff(c_1631,plain,
    ( r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12')
    | ~ v5_pre_topc('#skF_9','#skF_8','#skF_7')
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_funct_1('#skF_9')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_1628])).

tff(c_1634,plain,
    ( r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_76,c_64,c_1631])).

tff(c_1635,plain,(
    r1_tmap_1('#skF_8','#skF_7','#skF_9','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1634])).

tff(c_62,plain,(
    r1_tmap_1('#skF_7','#skF_6','#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_1681,plain,(
    ! [B_579,E_577,F_575,C_576,A_578,D_574] :
      ( r1_tmap_1(B_579,A_578,k1_partfun1(u1_struct_0(B_579),u1_struct_0(C_576),u1_struct_0(C_576),u1_struct_0(A_578),D_574,E_577),F_575)
      | ~ r1_tmap_1(C_576,A_578,E_577,k3_funct_2(u1_struct_0(B_579),u1_struct_0(C_576),D_574,F_575))
      | ~ r1_tmap_1(B_579,C_576,D_574,F_575)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_579),u1_struct_0(C_576),D_574,F_575),u1_struct_0(C_576))
      | ~ m1_subset_1(F_575,u1_struct_0(B_579))
      | ~ m1_subset_1(E_577,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_576),u1_struct_0(A_578))))
      | ~ v1_funct_2(E_577,u1_struct_0(C_576),u1_struct_0(A_578))
      | ~ v1_funct_1(E_577)
      | ~ m1_subset_1(D_574,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_579),u1_struct_0(C_576))))
      | ~ v1_funct_2(D_574,u1_struct_0(B_579),u1_struct_0(C_576))
      | ~ v1_funct_1(D_574)
      | ~ l1_pre_topc(C_576)
      | ~ v2_pre_topc(C_576)
      | v2_struct_0(C_576)
      | ~ l1_pre_topc(B_579)
      | ~ v2_pre_topc(B_579)
      | v2_struct_0(B_579)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578)
      | v2_struct_0(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_56,plain,(
    ~ r1_tmap_1('#skF_8','#skF_6',k1_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_9','#skF_10'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_1687,plain,
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
    inference(resolution,[status(thm)],[c_1681,c_56])).

tff(c_1691,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_8')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_80,c_88,c_86,c_78,c_76,c_74,c_72,c_70,c_68,c_60,c_66,c_1086,c_1635,c_62,c_1086,c_1687])).

tff(c_1693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_90,c_1691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:07:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.90  
% 4.65/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.90  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k3_funct_2 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k1_connsp_2 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 4.65/1.90  
% 4.65/1.90  %Foreground sorts:
% 4.65/1.90  
% 4.65/1.90  
% 4.65/1.90  %Background operators:
% 4.65/1.90  
% 4.65/1.90  
% 4.65/1.90  %Foreground operators:
% 4.65/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.65/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.65/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.65/1.90  tff('#skF_11', type, '#skF_11': $i).
% 4.65/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.65/1.90  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 4.65/1.90  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.65/1.90  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.65/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.65/1.90  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.65/1.90  tff('#skF_7', type, '#skF_7': $i).
% 4.65/1.90  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.65/1.90  tff('#skF_10', type, '#skF_10': $i).
% 4.65/1.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.65/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.65/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.65/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.65/1.90  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.65/1.90  tff('#skF_9', type, '#skF_9': $i).
% 4.65/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.90  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.65/1.90  tff('#skF_8', type, '#skF_8': $i).
% 4.65/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.90  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.65/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.65/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.65/1.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.65/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.65/1.90  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.65/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.65/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.65/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.65/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.65/1.90  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.65/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.65/1.90  tff('#skF_12', type, '#skF_12': $i).
% 4.65/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.90  
% 4.65/1.92  tff(f_238, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => ((v5_pre_topc(D, C, B) & r1_tmap_1(B, A, E, F)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (r2_hidden(G, k8_relset_1(u1_struct_0(C), u1_struct_0(B), D, k6_domain_1(u1_struct_0(B), F))) => r1_tmap_1(C, A, k1_partfun1(u1_struct_0(C), u1_struct_0(B), u1_struct_0(B), u1_struct_0(A), D, E), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tmap_1)).
% 4.65/1.92  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.65/1.92  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.65/1.92  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.65/1.92  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 4.65/1.92  tff(f_94, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 4.65/1.92  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.65/1.92  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 4.65/1.92  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.65/1.92  tff(f_76, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.65/1.92  tff(f_135, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 4.65/1.92  tff(f_186, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tmap_1)).
% 4.65/1.92  tff(c_96, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_84, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_90, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_94, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_92, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_82, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_80, plain, (l1_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_88, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_86, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_78, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_76, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_74, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_72, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_70, plain, (v1_funct_2('#skF_10', u1_struct_0('#skF_7'), u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_68, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_60, plain, (m1_subset_1('#skF_12', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_66, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_113, plain, (![C_313, A_314, B_315]: (v1_relat_1(C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.65/1.92  tff(c_120, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_113])).
% 4.65/1.92  tff(c_632, plain, (![A_419, B_420, C_421, D_422]: (k8_relset_1(A_419, B_420, C_421, D_422)=k10_relat_1(C_421, D_422) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(A_419, B_420))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.92  tff(c_637, plain, (![D_422]: (k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', D_422)=k10_relat_1('#skF_9', D_422))), inference(resolution, [status(thm)], [c_74, c_632])).
% 4.65/1.92  tff(c_131, plain, (![A_319, B_320]: (k6_domain_1(A_319, B_320)=k1_tarski(B_320) | ~m1_subset_1(B_320, A_319) | v1_xboole_0(A_319))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.65/1.92  tff(c_146, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')=k1_tarski('#skF_11') | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_131])).
% 4.65/1.92  tff(c_148, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_146])).
% 4.65/1.92  tff(c_46, plain, (![B_39, A_37]: (r2_hidden(B_39, k1_connsp_2(A_37, B_39)) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.65/1.92  tff(c_260, plain, (![A_350, B_351]: (m1_subset_1(k1_connsp_2(A_350, B_351), k1_zfmisc_1(u1_struct_0(A_350))) | ~m1_subset_1(B_351, u1_struct_0(A_350)) | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.65/1.92  tff(c_16, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.65/1.92  tff(c_315, plain, (![A_360, A_361, B_362]: (~v1_xboole_0(u1_struct_0(A_360)) | ~r2_hidden(A_361, k1_connsp_2(A_360, B_362)) | ~m1_subset_1(B_362, u1_struct_0(A_360)) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(resolution, [status(thm)], [c_260, c_16])).
% 4.65/1.92  tff(c_340, plain, (![A_363, B_364]: (~v1_xboole_0(u1_struct_0(A_363)) | ~m1_subset_1(B_364, u1_struct_0(A_363)) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(resolution, [status(thm)], [c_46, c_315])).
% 4.65/1.92  tff(c_343, plain, (~v1_xboole_0(u1_struct_0('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_66, c_340])).
% 4.65/1.92  tff(c_349, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_148, c_343])).
% 4.65/1.92  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_349])).
% 4.65/1.92  tff(c_352, plain, (k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')=k1_tarski('#skF_11')), inference(splitRight, [status(thm)], [c_146])).
% 4.65/1.92  tff(c_58, plain, (r2_hidden('#skF_12', k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', k6_domain_1(u1_struct_0('#skF_7'), '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_354, plain, (r2_hidden('#skF_12', k8_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_58])).
% 4.65/1.92  tff(c_650, plain, (r2_hidden('#skF_12', k10_relat_1('#skF_9', k1_tarski('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_354])).
% 4.65/1.92  tff(c_639, plain, (![A_423, D_424, B_425]: (r2_hidden(k1_funct_1(A_423, D_424), B_425) | ~r2_hidden(D_424, k10_relat_1(A_423, B_425)) | ~v1_funct_1(A_423) | ~v1_relat_1(A_423))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.65/1.92  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.92  tff(c_675, plain, (![A_428, D_429, A_430]: (k1_funct_1(A_428, D_429)=A_430 | ~r2_hidden(D_429, k10_relat_1(A_428, k1_tarski(A_430))) | ~v1_funct_1(A_428) | ~v1_relat_1(A_428))), inference(resolution, [status(thm)], [c_639, c_2])).
% 4.65/1.92  tff(c_678, plain, (k1_funct_1('#skF_9', '#skF_12')='#skF_11' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_650, c_675])).
% 4.65/1.92  tff(c_693, plain, (k1_funct_1('#skF_9', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_78, c_678])).
% 4.65/1.92  tff(c_147, plain, (k6_domain_1(u1_struct_0('#skF_8'), '#skF_12')=k1_tarski('#skF_12') | v1_xboole_0(u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_131])).
% 4.65/1.92  tff(c_359, plain, (v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_147])).
% 4.65/1.92  tff(c_491, plain, (![A_395, B_396]: (m1_subset_1(k1_connsp_2(A_395, B_396), k1_zfmisc_1(u1_struct_0(A_395))) | ~m1_subset_1(B_396, u1_struct_0(A_395)) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.65/1.92  tff(c_565, plain, (![A_403, A_404, B_405]: (~v1_xboole_0(u1_struct_0(A_403)) | ~r2_hidden(A_404, k1_connsp_2(A_403, B_405)) | ~m1_subset_1(B_405, u1_struct_0(A_403)) | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403) | v2_struct_0(A_403))), inference(resolution, [status(thm)], [c_491, c_16])).
% 4.65/1.92  tff(c_585, plain, (![A_406, B_407]: (~v1_xboole_0(u1_struct_0(A_406)) | ~m1_subset_1(B_407, u1_struct_0(A_406)) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(resolution, [status(thm)], [c_46, c_565])).
% 4.65/1.92  tff(c_591, plain, (~v1_xboole_0(u1_struct_0('#skF_8')) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_60, c_585])).
% 4.65/1.92  tff(c_598, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_359, c_591])).
% 4.65/1.92  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_598])).
% 4.65/1.92  tff(c_602, plain, (~v1_xboole_0(u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_147])).
% 4.65/1.92  tff(c_1047, plain, (![A_480, B_481, C_482, D_483]: (k3_funct_2(A_480, B_481, C_482, D_483)=k1_funct_1(C_482, D_483) | ~m1_subset_1(D_483, A_480) | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(A_480, B_481))) | ~v1_funct_2(C_482, A_480, B_481) | ~v1_funct_1(C_482) | v1_xboole_0(A_480))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.65/1.92  tff(c_1057, plain, (![B_481, C_482]: (k3_funct_2(u1_struct_0('#skF_8'), B_481, C_482, '#skF_12')=k1_funct_1(C_482, '#skF_12') | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), B_481))) | ~v1_funct_2(C_482, u1_struct_0('#skF_8'), B_481) | ~v1_funct_1(C_482) | v1_xboole_0(u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_60, c_1047])).
% 4.65/1.92  tff(c_1080, plain, (![B_486, C_487]: (k3_funct_2(u1_struct_0('#skF_8'), B_486, C_487, '#skF_12')=k1_funct_1(C_487, '#skF_12') | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), B_486))) | ~v1_funct_2(C_487, u1_struct_0('#skF_8'), B_486) | ~v1_funct_1(C_487))), inference(negUnitSimplification, [status(thm)], [c_602, c_1057])).
% 4.65/1.92  tff(c_1083, plain, (k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')=k1_funct_1('#skF_9', '#skF_12') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_1080])).
% 4.65/1.92  tff(c_1086, plain, (k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_693, c_1083])).
% 4.65/1.92  tff(c_64, plain, (v5_pre_topc('#skF_9', '#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_1607, plain, (![B_558, A_559, C_560, D_561]: (r1_tmap_1(B_558, A_559, C_560, D_561) | ~m1_subset_1(D_561, u1_struct_0(B_558)) | ~v5_pre_topc(C_560, B_558, A_559) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_558), u1_struct_0(A_559)))) | ~v1_funct_2(C_560, u1_struct_0(B_558), u1_struct_0(A_559)) | ~v1_funct_1(C_560) | ~l1_pre_topc(B_558) | ~v2_pre_topc(B_558) | v2_struct_0(B_558) | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559) | v2_struct_0(A_559))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.65/1.92  tff(c_1611, plain, (![A_559, C_560]: (r1_tmap_1('#skF_8', A_559, C_560, '#skF_12') | ~v5_pre_topc(C_560, '#skF_8', A_559) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_559)))) | ~v1_funct_2(C_560, u1_struct_0('#skF_8'), u1_struct_0(A_559)) | ~v1_funct_1(C_560) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559) | v2_struct_0(A_559))), inference(resolution, [status(thm)], [c_60, c_1607])).
% 4.65/1.92  tff(c_1618, plain, (![A_559, C_560]: (r1_tmap_1('#skF_8', A_559, C_560, '#skF_12') | ~v5_pre_topc(C_560, '#skF_8', A_559) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_559)))) | ~v1_funct_2(C_560, u1_struct_0('#skF_8'), u1_struct_0(A_559)) | ~v1_funct_1(C_560) | v2_struct_0('#skF_8') | ~l1_pre_topc(A_559) | ~v2_pre_topc(A_559) | v2_struct_0(A_559))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_1611])).
% 4.65/1.92  tff(c_1628, plain, (![A_564, C_565]: (r1_tmap_1('#skF_8', A_564, C_565, '#skF_12') | ~v5_pre_topc(C_565, '#skF_8', A_564) | ~m1_subset_1(C_565, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0(A_564)))) | ~v1_funct_2(C_565, u1_struct_0('#skF_8'), u1_struct_0(A_564)) | ~v1_funct_1(C_565) | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(negUnitSimplification, [status(thm)], [c_84, c_1618])).
% 4.65/1.92  tff(c_1631, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | ~v5_pre_topc('#skF_9', '#skF_8', '#skF_7') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_74, c_1628])).
% 4.65/1.92  tff(c_1634, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_78, c_76, c_64, c_1631])).
% 4.65/1.92  tff(c_1635, plain, (r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_90, c_1634])).
% 4.65/1.92  tff(c_62, plain, (r1_tmap_1('#skF_7', '#skF_6', '#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_1681, plain, (![B_579, E_577, F_575, C_576, A_578, D_574]: (r1_tmap_1(B_579, A_578, k1_partfun1(u1_struct_0(B_579), u1_struct_0(C_576), u1_struct_0(C_576), u1_struct_0(A_578), D_574, E_577), F_575) | ~r1_tmap_1(C_576, A_578, E_577, k3_funct_2(u1_struct_0(B_579), u1_struct_0(C_576), D_574, F_575)) | ~r1_tmap_1(B_579, C_576, D_574, F_575) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_579), u1_struct_0(C_576), D_574, F_575), u1_struct_0(C_576)) | ~m1_subset_1(F_575, u1_struct_0(B_579)) | ~m1_subset_1(E_577, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_576), u1_struct_0(A_578)))) | ~v1_funct_2(E_577, u1_struct_0(C_576), u1_struct_0(A_578)) | ~v1_funct_1(E_577) | ~m1_subset_1(D_574, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_579), u1_struct_0(C_576)))) | ~v1_funct_2(D_574, u1_struct_0(B_579), u1_struct_0(C_576)) | ~v1_funct_1(D_574) | ~l1_pre_topc(C_576) | ~v2_pre_topc(C_576) | v2_struct_0(C_576) | ~l1_pre_topc(B_579) | ~v2_pre_topc(B_579) | v2_struct_0(B_579) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578) | v2_struct_0(A_578))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.65/1.92  tff(c_56, plain, (~r1_tmap_1('#skF_8', '#skF_6', k1_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), '#skF_9', '#skF_10'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_238])).
% 4.65/1.92  tff(c_1687, plain, (~r1_tmap_1('#skF_7', '#skF_6', '#skF_10', k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12')) | ~r1_tmap_1('#skF_8', '#skF_7', '#skF_9', '#skF_12') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_8'), u1_struct_0('#skF_7'), '#skF_9', '#skF_12'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_10', u1_struct_0('#skF_7'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_10') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_7')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_7')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1681, c_56])).
% 4.65/1.92  tff(c_1691, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_8') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_80, c_88, c_86, c_78, c_76, c_74, c_72, c_70, c_68, c_60, c_66, c_1086, c_1635, c_62, c_1086, c_1687])).
% 4.65/1.92  tff(c_1693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_90, c_1691])).
% 4.65/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.92  
% 4.65/1.92  Inference rules
% 4.65/1.92  ----------------------
% 4.65/1.92  #Ref     : 0
% 4.65/1.92  #Sup     : 320
% 4.65/1.92  #Fact    : 0
% 4.65/1.92  #Define  : 0
% 4.65/1.92  #Split   : 12
% 4.65/1.92  #Chain   : 0
% 4.65/1.92  #Close   : 0
% 4.65/1.92  
% 4.65/1.92  Ordering : KBO
% 4.65/1.92  
% 4.65/1.92  Simplification rules
% 4.65/1.92  ----------------------
% 4.65/1.92  #Subsume      : 31
% 4.65/1.92  #Demod        : 178
% 4.65/1.92  #Tautology    : 95
% 4.65/1.92  #SimpNegUnit  : 14
% 4.65/1.92  #BackRed      : 4
% 4.65/1.92  
% 4.65/1.92  #Partial instantiations: 0
% 4.65/1.92  #Strategies tried      : 1
% 4.65/1.92  
% 4.65/1.92  Timing (in seconds)
% 4.65/1.92  ----------------------
% 4.65/1.92  Preprocessing        : 0.43
% 4.65/1.92  Parsing              : 0.22
% 4.65/1.92  CNF conversion       : 0.05
% 4.65/1.92  Main loop            : 0.68
% 4.65/1.92  Inferencing          : 0.26
% 4.65/1.92  Reduction            : 0.19
% 4.65/1.92  Demodulation         : 0.14
% 4.65/1.92  BG Simplification    : 0.04
% 4.65/1.92  Subsumption          : 0.14
% 4.65/1.92  Abstraction          : 0.04
% 4.65/1.92  MUC search           : 0.00
% 5.02/1.92  Cooper               : 0.00
% 5.02/1.92  Total                : 1.15
% 5.02/1.92  Index Insertion      : 0.00
% 5.02/1.92  Index Deletion       : 0.00
% 5.02/1.92  Index Matching       : 0.00
% 5.02/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
