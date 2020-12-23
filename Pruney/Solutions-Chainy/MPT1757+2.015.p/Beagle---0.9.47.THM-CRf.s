%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:06 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.17s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 985 expanded)
%              Number of leaves         :   45 ( 387 expanded)
%              Depth                    :   21
%              Number of atoms          :  592 (7228 expanded)
%              Number of equality atoms :    5 ( 337 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_323,negated_conjecture,(
    ~ ! [A] :
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
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,B)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ( E = F
                             => ( r1_tmap_1(B,A,C,E)
                              <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_193,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_186,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( m1_connsp_2(C,A,B)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( m1_connsp_2(D,A,B)
                          & v3_pre_topc(D,A)
                          & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_280,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_168,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_233,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_58,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_52,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_89,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54])).

tff(c_72,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_70,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_109,plain,(
    ! [B_333,A_334] :
      ( v2_pre_topc(B_333)
      | ~ m1_pre_topc(B_333,A_334)
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_109])).

tff(c_115,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_112])).

tff(c_96,plain,(
    ! [B_326,A_327] :
      ( l1_pre_topc(B_326)
      | ~ m1_pre_topc(B_326,A_327)
      | ~ l1_pre_topc(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_96])).

tff(c_102,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_99])).

tff(c_60,plain,(
    v1_tsep_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_44,plain,(
    ! [B_78,A_76] :
      ( m1_subset_1(u1_struct_0(B_78),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_178,plain,(
    ! [B_363,A_364] :
      ( v3_pre_topc(u1_struct_0(B_363),A_364)
      | ~ v1_tsep_1(B_363,A_364)
      | ~ m1_subset_1(u1_struct_0(B_363),k1_zfmisc_1(u1_struct_0(A_364)))
      | ~ m1_pre_topc(B_363,A_364)
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_182,plain,(
    ! [B_78,A_76] :
      ( v3_pre_topc(u1_struct_0(B_78),A_76)
      | ~ v1_tsep_1(B_78,A_76)
      | ~ v2_pre_topc(A_76)
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_44,c_178])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_219,plain,(
    ! [A_380,B_381,C_382] :
      ( r1_tarski('#skF_2'(A_380,B_381,C_382),C_382)
      | ~ m1_connsp_2(C_382,A_380,B_381)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ m1_subset_1(B_381,u1_struct_0(A_380))
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_225,plain,(
    ! [A_76,B_381,B_78] :
      ( r1_tarski('#skF_2'(A_76,B_381,u1_struct_0(B_78)),u1_struct_0(B_78))
      | ~ m1_connsp_2(u1_struct_0(B_78),A_76,B_381)
      | ~ m1_subset_1(B_381,u1_struct_0(A_76))
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76)
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_44,c_219])).

tff(c_24,plain,(
    ! [A_33,B_41,C_45] :
      ( m1_subset_1('#skF_2'(A_33,B_41,C_45),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_connsp_2(C_45,A_33,B_41)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_41,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_90,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_88])).

tff(c_121,plain,(
    r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_91,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_123,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_91])).

tff(c_78,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_66,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_868,plain,(
    ! [D_511,C_513,G_508,A_512,E_510,B_509] :
      ( r1_tmap_1(B_509,A_512,C_513,G_508)
      | ~ r1_tmap_1(D_511,A_512,k2_tmap_1(B_509,A_512,C_513,D_511),G_508)
      | ~ m1_connsp_2(E_510,B_509,G_508)
      | ~ r1_tarski(E_510,u1_struct_0(D_511))
      | ~ m1_subset_1(G_508,u1_struct_0(D_511))
      | ~ m1_subset_1(G_508,u1_struct_0(B_509))
      | ~ m1_subset_1(E_510,k1_zfmisc_1(u1_struct_0(B_509)))
      | ~ m1_pre_topc(D_511,B_509)
      | v2_struct_0(D_511)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_509),u1_struct_0(A_512))))
      | ~ v1_funct_2(C_513,u1_struct_0(B_509),u1_struct_0(A_512))
      | ~ v1_funct_1(C_513)
      | ~ l1_pre_topc(B_509)
      | ~ v2_pre_topc(B_509)
      | v2_struct_0(B_509)
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_872,plain,(
    ! [E_510] :
      ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_510,'#skF_5','#skF_8')
      | ~ r1_tarski(E_510,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_510,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_7','#skF_5')
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_121,c_868])).

tff(c_879,plain,(
    ! [E_510] :
      ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_510,'#skF_5','#skF_8')
      | ~ r1_tarski(E_510,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_510,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_68,c_66,c_64,c_58,c_56,c_89,c_872])).

tff(c_881,plain,(
    ! [E_514] :
      ( ~ m1_connsp_2(E_514,'#skF_5','#skF_8')
      | ~ r1_tarski(E_514,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_514,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_62,c_123,c_879])).

tff(c_893,plain,(
    ! [B_41,C_45] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_41,C_45),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_41,C_45),u1_struct_0('#skF_7'))
      | ~ m1_connsp_2(C_45,'#skF_5',B_41)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_881])).

tff(c_918,plain,(
    ! [B_41,C_45] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_41,C_45),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_41,C_45),u1_struct_0('#skF_7'))
      | ~ m1_connsp_2(C_45,'#skF_5',B_41)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_893])).

tff(c_931,plain,(
    ! [B_517,C_518] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_517,C_518),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_517,C_518),u1_struct_0('#skF_7'))
      | ~ m1_connsp_2(C_518,'#skF_5',B_517)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_517,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_918])).

tff(c_939,plain,(
    ! [B_381] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_381,u1_struct_0('#skF_7')),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5',B_381)
      | ~ m1_subset_1(B_381,u1_struct_0('#skF_5'))
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_7','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_225,c_931])).

tff(c_945,plain,(
    ! [B_381] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_381,u1_struct_0('#skF_7')),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5',B_381)
      | ~ m1_subset_1(B_381,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_58,c_72,c_939])).

tff(c_946,plain,(
    ! [B_381] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_381,u1_struct_0('#skF_7')),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5',B_381)
      | ~ m1_subset_1(B_381,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_945])).

tff(c_947,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_946])).

tff(c_953,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_947])).

tff(c_960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_58,c_953])).

tff(c_962,plain,(
    m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_125,plain,(
    ! [C_342,A_343,B_344] :
      ( m1_subset_1(C_342,u1_struct_0(A_343))
      | ~ m1_subset_1(C_342,u1_struct_0(B_344))
      | ~ m1_pre_topc(B_344,A_343)
      | v2_struct_0(B_344)
      | ~ l1_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_127,plain,(
    ! [A_343] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_343))
      | ~ m1_pre_topc('#skF_7',A_343)
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_89,c_125])).

tff(c_132,plain,(
    ! [A_343] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_343))
      | ~ m1_pre_topc('#skF_7',A_343)
      | ~ l1_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_127])).

tff(c_233,plain,(
    ! [B_386,A_387,C_388] :
      ( m1_connsp_2(B_386,A_387,C_388)
      | ~ r2_hidden(C_388,B_386)
      | ~ v3_pre_topc(B_386,A_387)
      | ~ m1_subset_1(C_388,u1_struct_0(A_387))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_243,plain,(
    ! [B_386,A_343] :
      ( m1_connsp_2(B_386,A_343,'#skF_8')
      | ~ r2_hidden('#skF_8',B_386)
      | ~ v3_pre_topc(B_386,A_343)
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ v2_pre_topc(A_343)
      | ~ m1_pre_topc('#skF_7',A_343)
      | ~ l1_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_132,c_233])).

tff(c_970,plain,
    ( m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_962,c_243])).

tff(c_996,plain,
    ( m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_58,c_72,c_970])).

tff(c_997,plain,
    ( m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_996])).

tff(c_1044,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_997])).

tff(c_1047,plain,
    ( ~ v1_tsep_1('#skF_7','#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_182,c_1044])).

tff(c_1051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_58,c_72,c_60,c_1047])).

tff(c_1053,plain,(
    v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_997])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_23,B_24] :
      ( m1_connsp_2('#skF_1'(A_23,B_24),A_23,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_158,plain,(
    ! [C_351,A_352,B_353] :
      ( m1_subset_1(C_351,k1_zfmisc_1(u1_struct_0(A_352)))
      | ~ m1_connsp_2(C_351,A_352,B_353)
      | ~ m1_subset_1(B_353,u1_struct_0(A_352))
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_168,plain,(
    ! [A_358,B_359] :
      ( m1_subset_1('#skF_1'(A_358,B_359),k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ m1_subset_1(B_359,u1_struct_0(A_358))
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,(
    ! [A_360,A_361,B_362] :
      ( ~ v1_xboole_0(u1_struct_0(A_360))
      | ~ r2_hidden(A_361,'#skF_1'(A_360,B_362))
      | ~ m1_subset_1(B_362,u1_struct_0(A_360))
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_168,c_4])).

tff(c_188,plain,(
    ! [A_367,B_368,A_369] :
      ( ~ v1_xboole_0(u1_struct_0(A_367))
      | ~ m1_subset_1(B_368,u1_struct_0(A_367))
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367)
      | v1_xboole_0('#skF_1'(A_367,B_368))
      | ~ m1_subset_1(A_369,'#skF_1'(A_367,B_368)) ) ),
    inference(resolution,[status(thm)],[c_2,c_172])).

tff(c_194,plain,(
    ! [A_369] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | v1_xboole_0('#skF_1'('#skF_7','#skF_8'))
      | ~ m1_subset_1(A_369,'#skF_1'('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_89,c_188])).

tff(c_201,plain,(
    ! [A_369] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | v1_xboole_0('#skF_1'('#skF_7','#skF_8'))
      | ~ m1_subset_1(A_369,'#skF_1'('#skF_7','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_102,c_194])).

tff(c_202,plain,(
    ! [A_369] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
      | v1_xboole_0('#skF_1'('#skF_7','#skF_8'))
      | ~ m1_subset_1(A_369,'#skF_1'('#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_201])).

tff(c_207,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_1052,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_997])).

tff(c_1070,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1052])).

tff(c_1073,plain,
    ( v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2,c_1070])).

tff(c_1076,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1073])).

tff(c_1078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_1076])).

tff(c_1080,plain,(
    r2_hidden('#skF_8',u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_1079,plain,(
    m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_241,plain,(
    ! [B_386] :
      ( m1_connsp_2(B_386,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_386)
      | ~ v3_pre_topc(B_386,'#skF_5')
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_233])).

tff(c_250,plain,(
    ! [B_386] :
      ( m1_connsp_2(B_386,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_386)
      | ~ v3_pre_topc(B_386,'#skF_5')
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_241])).

tff(c_268,plain,(
    ! [B_390] :
      ( m1_connsp_2(B_390,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_390)
      | ~ v3_pre_topc(B_390,'#skF_5')
      | ~ m1_subset_1(B_390,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_250])).

tff(c_276,plain,(
    ! [B_78] :
      ( m1_connsp_2(u1_struct_0(B_78),'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_78))
      | ~ v3_pre_topc(u1_struct_0(B_78),'#skF_5')
      | ~ m1_pre_topc(B_78,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_268])).

tff(c_298,plain,(
    ! [B_395] :
      ( m1_connsp_2(u1_struct_0(B_395),'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_395))
      | ~ v3_pre_topc(u1_struct_0(B_395),'#skF_5')
      | ~ m1_pre_topc(B_395,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_276])).

tff(c_12,plain,(
    ! [C_22,A_19,B_20] :
      ( m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_connsp_2(C_22,A_19,B_20)
      | ~ m1_subset_1(B_20,u1_struct_0(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_300,plain,(
    ! [B_395] :
      ( m1_subset_1(u1_struct_0(B_395),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_395))
      | ~ v3_pre_topc(u1_struct_0(B_395),'#skF_5')
      | ~ m1_pre_topc(B_395,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_298,c_12])).

tff(c_303,plain,(
    ! [B_395] :
      ( m1_subset_1(u1_struct_0(B_395),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_395))
      | ~ v3_pre_topc(u1_struct_0(B_395),'#skF_5')
      | ~ m1_pre_topc(B_395,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_300])).

tff(c_304,plain,(
    ! [B_395] :
      ( m1_subset_1(u1_struct_0(B_395),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_395))
      | ~ v3_pre_topc(u1_struct_0(B_395),'#skF_5')
      | ~ m1_pre_topc(B_395,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_303])).

tff(c_564,plain,(
    ! [A_424,B_425,C_426] :
      ( m1_connsp_2('#skF_2'(A_424,B_425,C_426),A_424,B_425)
      | ~ m1_connsp_2(C_426,A_424,B_425)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(u1_struct_0(A_424)))
      | ~ m1_subset_1(B_425,u1_struct_0(A_424))
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_570,plain,(
    ! [B_425,B_395] :
      ( m1_connsp_2('#skF_2'('#skF_5',B_425,u1_struct_0(B_395)),'#skF_5',B_425)
      | ~ m1_connsp_2(u1_struct_0(B_395),'#skF_5',B_425)
      | ~ m1_subset_1(B_425,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_395))
      | ~ v3_pre_topc(u1_struct_0(B_395),'#skF_5')
      | ~ m1_pre_topc(B_395,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_304,c_564])).

tff(c_587,plain,(
    ! [B_425,B_395] :
      ( m1_connsp_2('#skF_2'('#skF_5',B_425,u1_struct_0(B_395)),'#skF_5',B_425)
      | ~ m1_connsp_2(u1_struct_0(B_395),'#skF_5',B_425)
      | ~ m1_subset_1(B_425,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_395))
      | ~ v3_pre_topc(u1_struct_0(B_395),'#skF_5')
      | ~ m1_pre_topc(B_395,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_570])).

tff(c_588,plain,(
    ! [B_425,B_395] :
      ( m1_connsp_2('#skF_2'('#skF_5',B_425,u1_struct_0(B_395)),'#skF_5',B_425)
      | ~ m1_connsp_2(u1_struct_0(B_395),'#skF_5',B_425)
      | ~ m1_subset_1(B_425,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_395))
      | ~ v3_pre_topc(u1_struct_0(B_395),'#skF_5')
      | ~ m1_pre_topc(B_395,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_587])).

tff(c_1104,plain,(
    ! [B_530] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_530,u1_struct_0('#skF_7')),'#skF_5','#skF_8')
      | ~ m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5',B_530)
      | ~ m1_subset_1(B_530,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_1108,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_7'),'#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
    | ~ m1_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_588,c_1104])).

tff(c_1116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1053,c_1080,c_56,c_1079,c_1108])).

tff(c_1118,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_161,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1('#skF_1'(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_1287,plain,(
    ! [B_563,A_564,C_565] :
      ( r2_hidden(B_563,'#skF_3'(A_564,B_563,C_565))
      | ~ m1_connsp_2(C_565,A_564,B_563)
      | ~ m1_subset_1(C_565,k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ m1_subset_1(B_563,u1_struct_0(A_564))
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1737,plain,(
    ! [B_657,A_658,B_659] :
      ( r2_hidden(B_657,'#skF_3'(A_658,B_657,'#skF_1'(A_658,B_659)))
      | ~ m1_connsp_2('#skF_1'(A_658,B_659),A_658,B_657)
      | ~ m1_subset_1(B_657,u1_struct_0(A_658))
      | ~ m1_subset_1(B_659,u1_struct_0(A_658))
      | ~ l1_pre_topc(A_658)
      | ~ v2_pre_topc(A_658)
      | v2_struct_0(A_658) ) ),
    inference(resolution,[status(thm)],[c_161,c_1287])).

tff(c_1528,plain,(
    ! [A_611,B_612,C_613] :
      ( m1_subset_1('#skF_3'(A_611,B_612,C_613),k1_zfmisc_1(u1_struct_0(A_611)))
      | ~ m1_connsp_2(C_613,A_611,B_612)
      | ~ m1_subset_1(C_613,k1_zfmisc_1(u1_struct_0(A_611)))
      | ~ m1_subset_1(B_612,u1_struct_0(A_611))
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1573,plain,(
    ! [A_611,A_3,B_612,C_613] :
      ( ~ v1_xboole_0(u1_struct_0(A_611))
      | ~ r2_hidden(A_3,'#skF_3'(A_611,B_612,C_613))
      | ~ m1_connsp_2(C_613,A_611,B_612)
      | ~ m1_subset_1(C_613,k1_zfmisc_1(u1_struct_0(A_611)))
      | ~ m1_subset_1(B_612,u1_struct_0(A_611))
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(resolution,[status(thm)],[c_1528,c_4])).

tff(c_1826,plain,(
    ! [A_686,B_687,B_688] :
      ( ~ v1_xboole_0(u1_struct_0(A_686))
      | ~ m1_subset_1('#skF_1'(A_686,B_687),k1_zfmisc_1(u1_struct_0(A_686)))
      | ~ m1_connsp_2('#skF_1'(A_686,B_687),A_686,B_688)
      | ~ m1_subset_1(B_688,u1_struct_0(A_686))
      | ~ m1_subset_1(B_687,u1_struct_0(A_686))
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(resolution,[status(thm)],[c_1737,c_1573])).

tff(c_1842,plain,(
    ! [A_689,B_690,B_691] :
      ( ~ v1_xboole_0(u1_struct_0(A_689))
      | ~ m1_connsp_2('#skF_1'(A_689,B_690),A_689,B_691)
      | ~ m1_subset_1(B_691,u1_struct_0(A_689))
      | ~ m1_subset_1(B_690,u1_struct_0(A_689))
      | ~ l1_pre_topc(A_689)
      | ~ v2_pre_topc(A_689)
      | v2_struct_0(A_689) ) ),
    inference(resolution,[status(thm)],[c_161,c_1826])).

tff(c_1869,plain,(
    ! [A_692,B_693] :
      ( ~ v1_xboole_0(u1_struct_0(A_692))
      | ~ m1_subset_1(B_693,u1_struct_0(A_692))
      | ~ l1_pre_topc(A_692)
      | ~ v2_pre_topc(A_692)
      | v2_struct_0(A_692) ) ),
    inference(resolution,[status(thm)],[c_14,c_1842])).

tff(c_1878,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_89,c_1869])).

tff(c_1886,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_102,c_1118,c_1878])).

tff(c_1888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1886])).

tff(c_1889,plain,(
    r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2606,plain,(
    ! [F_839,D_841,A_840,B_842,C_838] :
      ( r1_tmap_1(D_841,A_840,k2_tmap_1(B_842,A_840,C_838,D_841),F_839)
      | ~ r1_tmap_1(B_842,A_840,C_838,F_839)
      | ~ m1_subset_1(F_839,u1_struct_0(D_841))
      | ~ m1_subset_1(F_839,u1_struct_0(B_842))
      | ~ m1_pre_topc(D_841,B_842)
      | v2_struct_0(D_841)
      | ~ m1_subset_1(C_838,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_842),u1_struct_0(A_840))))
      | ~ v1_funct_2(C_838,u1_struct_0(B_842),u1_struct_0(A_840))
      | ~ v1_funct_1(C_838)
      | ~ l1_pre_topc(B_842)
      | ~ v2_pre_topc(B_842)
      | v2_struct_0(B_842)
      | ~ l1_pre_topc(A_840)
      | ~ v2_pre_topc(A_840)
      | v2_struct_0(A_840) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_2608,plain,(
    ! [D_841,F_839] :
      ( r1_tmap_1(D_841,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_841),F_839)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_839)
      | ~ m1_subset_1(F_839,u1_struct_0(D_841))
      | ~ m1_subset_1(F_839,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_841,'#skF_5')
      | v2_struct_0(D_841)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_2606])).

tff(c_2611,plain,(
    ! [D_841,F_839] :
      ( r1_tmap_1(D_841,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_841),F_839)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_839)
      | ~ m1_subset_1(F_839,u1_struct_0(D_841))
      | ~ m1_subset_1(F_839,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_841,'#skF_5')
      | v2_struct_0(D_841)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_68,c_66,c_2608])).

tff(c_2613,plain,(
    ! [D_843,F_844] :
      ( r1_tmap_1(D_843,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_843),F_844)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_844)
      | ~ m1_subset_1(F_844,u1_struct_0(D_843))
      | ~ m1_subset_1(F_844,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_843,'#skF_5')
      | v2_struct_0(D_843) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_2611])).

tff(c_1890,plain,(
    ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2616,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2613,c_1890])).

tff(c_2619,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_89,c_1889,c_2616])).

tff(c_2621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.14  
% 6.06/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.14  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 6.06/2.14  
% 6.06/2.14  %Foreground sorts:
% 6.06/2.14  
% 6.06/2.14  
% 6.06/2.14  %Background operators:
% 6.06/2.14  
% 6.06/2.14  
% 6.06/2.14  %Foreground operators:
% 6.06/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.06/2.14  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.06/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.06/2.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.14  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 6.06/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.06/2.14  tff('#skF_7', type, '#skF_7': $i).
% 6.06/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.14  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.06/2.14  tff('#skF_6', type, '#skF_6': $i).
% 6.06/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.06/2.14  tff('#skF_9', type, '#skF_9': $i).
% 6.06/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.06/2.14  tff('#skF_8', type, '#skF_8': $i).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.06/2.14  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.06/2.14  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.06/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.14  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.06/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.06/2.14  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.06/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.06/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.06/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.06/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.06/2.14  
% 6.17/2.17  tff(f_323, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 6.17/2.17  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.17/2.17  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.17/2.17  tff(f_193, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.17/2.17  tff(f_186, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 6.17/2.17  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 6.17/2.17  tff(f_280, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 6.17/2.17  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 6.17/2.17  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 6.17/2.17  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.17/2.17  tff(f_96, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 6.17/2.17  tff(f_84, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 6.17/2.17  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.17/2.17  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 6.17/2.17  tff(f_233, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 6.17/2.17  tff(c_62, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_58, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_56, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_52, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_54, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_89, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54])).
% 6.17/2.17  tff(c_72, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_70, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_109, plain, (![B_333, A_334]: (v2_pre_topc(B_333) | ~m1_pre_topc(B_333, A_334) | ~l1_pre_topc(A_334) | ~v2_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.17/2.17  tff(c_112, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_109])).
% 6.17/2.17  tff(c_115, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_112])).
% 6.17/2.17  tff(c_96, plain, (![B_326, A_327]: (l1_pre_topc(B_326) | ~m1_pre_topc(B_326, A_327) | ~l1_pre_topc(A_327))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.17/2.17  tff(c_99, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_96])).
% 6.17/2.17  tff(c_102, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_99])).
% 6.17/2.17  tff(c_60, plain, (v1_tsep_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_44, plain, (![B_78, A_76]: (m1_subset_1(u1_struct_0(B_78), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_78, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.17/2.17  tff(c_178, plain, (![B_363, A_364]: (v3_pre_topc(u1_struct_0(B_363), A_364) | ~v1_tsep_1(B_363, A_364) | ~m1_subset_1(u1_struct_0(B_363), k1_zfmisc_1(u1_struct_0(A_364))) | ~m1_pre_topc(B_363, A_364) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364))), inference(cnfTransformation, [status(thm)], [f_186])).
% 6.17/2.17  tff(c_182, plain, (![B_78, A_76]: (v3_pre_topc(u1_struct_0(B_78), A_76) | ~v1_tsep_1(B_78, A_76) | ~v2_pre_topc(A_76) | ~m1_pre_topc(B_78, A_76) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_44, c_178])).
% 6.17/2.17  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_219, plain, (![A_380, B_381, C_382]: (r1_tarski('#skF_2'(A_380, B_381, C_382), C_382) | ~m1_connsp_2(C_382, A_380, B_381) | ~m1_subset_1(C_382, k1_zfmisc_1(u1_struct_0(A_380))) | ~m1_subset_1(B_381, u1_struct_0(A_380)) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | v2_struct_0(A_380))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.17/2.17  tff(c_225, plain, (![A_76, B_381, B_78]: (r1_tarski('#skF_2'(A_76, B_381, u1_struct_0(B_78)), u1_struct_0(B_78)) | ~m1_connsp_2(u1_struct_0(B_78), A_76, B_381) | ~m1_subset_1(B_381, u1_struct_0(A_76)) | ~v2_pre_topc(A_76) | v2_struct_0(A_76) | ~m1_pre_topc(B_78, A_76) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_44, c_219])).
% 6.17/2.17  tff(c_24, plain, (![A_33, B_41, C_45]: (m1_subset_1('#skF_2'(A_33, B_41, C_45), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_connsp_2(C_45, A_33, B_41) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_41, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.17/2.17  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_88, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_90, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_88])).
% 6.17/2.17  tff(c_121, plain, (r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 6.17/2.17  tff(c_82, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_91, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_82])).
% 6.17/2.17  tff(c_123, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_91])).
% 6.17/2.17  tff(c_78, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_66, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_323])).
% 6.17/2.17  tff(c_868, plain, (![D_511, C_513, G_508, A_512, E_510, B_509]: (r1_tmap_1(B_509, A_512, C_513, G_508) | ~r1_tmap_1(D_511, A_512, k2_tmap_1(B_509, A_512, C_513, D_511), G_508) | ~m1_connsp_2(E_510, B_509, G_508) | ~r1_tarski(E_510, u1_struct_0(D_511)) | ~m1_subset_1(G_508, u1_struct_0(D_511)) | ~m1_subset_1(G_508, u1_struct_0(B_509)) | ~m1_subset_1(E_510, k1_zfmisc_1(u1_struct_0(B_509))) | ~m1_pre_topc(D_511, B_509) | v2_struct_0(D_511) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_509), u1_struct_0(A_512)))) | ~v1_funct_2(C_513, u1_struct_0(B_509), u1_struct_0(A_512)) | ~v1_funct_1(C_513) | ~l1_pre_topc(B_509) | ~v2_pre_topc(B_509) | v2_struct_0(B_509) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512))), inference(cnfTransformation, [status(thm)], [f_280])).
% 6.17/2.17  tff(c_872, plain, (![E_510]: (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_connsp_2(E_510, '#skF_5', '#skF_8') | ~r1_tarski(E_510, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(E_510, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_121, c_868])).
% 6.17/2.17  tff(c_879, plain, (![E_510]: (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_connsp_2(E_510, '#skF_5', '#skF_8') | ~r1_tarski(E_510, u1_struct_0('#skF_7')) | ~m1_subset_1(E_510, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_68, c_66, c_64, c_58, c_56, c_89, c_872])).
% 6.17/2.17  tff(c_881, plain, (![E_514]: (~m1_connsp_2(E_514, '#skF_5', '#skF_8') | ~r1_tarski(E_514, u1_struct_0('#skF_7')) | ~m1_subset_1(E_514, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_62, c_123, c_879])).
% 6.17/2.17  tff(c_893, plain, (![B_41, C_45]: (~m1_connsp_2('#skF_2'('#skF_5', B_41, C_45), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_41, C_45), u1_struct_0('#skF_7')) | ~m1_connsp_2(C_45, '#skF_5', B_41) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_41, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_881])).
% 6.17/2.17  tff(c_918, plain, (![B_41, C_45]: (~m1_connsp_2('#skF_2'('#skF_5', B_41, C_45), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_41, C_45), u1_struct_0('#skF_7')) | ~m1_connsp_2(C_45, '#skF_5', B_41) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_41, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_893])).
% 6.17/2.17  tff(c_931, plain, (![B_517, C_518]: (~m1_connsp_2('#skF_2'('#skF_5', B_517, C_518), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_517, C_518), u1_struct_0('#skF_7')) | ~m1_connsp_2(C_518, '#skF_5', B_517) | ~m1_subset_1(C_518, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_517, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_74, c_918])).
% 6.17/2.17  tff(c_939, plain, (![B_381]: (~m1_connsp_2('#skF_2'('#skF_5', B_381, u1_struct_0('#skF_7')), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', B_381) | ~m1_subset_1(B_381, u1_struct_0('#skF_5')) | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_225, c_931])).
% 6.17/2.17  tff(c_945, plain, (![B_381]: (~m1_connsp_2('#skF_2'('#skF_5', B_381, u1_struct_0('#skF_7')), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', B_381) | ~m1_subset_1(B_381, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_58, c_72, c_939])).
% 6.17/2.17  tff(c_946, plain, (![B_381]: (~m1_connsp_2('#skF_2'('#skF_5', B_381, u1_struct_0('#skF_7')), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', B_381) | ~m1_subset_1(B_381, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_74, c_945])).
% 6.17/2.17  tff(c_947, plain, (~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_946])).
% 6.17/2.17  tff(c_953, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_44, c_947])).
% 6.17/2.17  tff(c_960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_58, c_953])).
% 6.17/2.17  tff(c_962, plain, (m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_946])).
% 6.17/2.17  tff(c_125, plain, (![C_342, A_343, B_344]: (m1_subset_1(C_342, u1_struct_0(A_343)) | ~m1_subset_1(C_342, u1_struct_0(B_344)) | ~m1_pre_topc(B_344, A_343) | v2_struct_0(B_344) | ~l1_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.17/2.17  tff(c_127, plain, (![A_343]: (m1_subset_1('#skF_8', u1_struct_0(A_343)) | ~m1_pre_topc('#skF_7', A_343) | v2_struct_0('#skF_7') | ~l1_pre_topc(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_89, c_125])).
% 6.17/2.17  tff(c_132, plain, (![A_343]: (m1_subset_1('#skF_8', u1_struct_0(A_343)) | ~m1_pre_topc('#skF_7', A_343) | ~l1_pre_topc(A_343) | v2_struct_0(A_343))), inference(negUnitSimplification, [status(thm)], [c_62, c_127])).
% 6.17/2.17  tff(c_233, plain, (![B_386, A_387, C_388]: (m1_connsp_2(B_386, A_387, C_388) | ~r2_hidden(C_388, B_386) | ~v3_pre_topc(B_386, A_387) | ~m1_subset_1(C_388, u1_struct_0(A_387)) | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0(A_387))) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387) | v2_struct_0(A_387))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.17/2.17  tff(c_243, plain, (![B_386, A_343]: (m1_connsp_2(B_386, A_343, '#skF_8') | ~r2_hidden('#skF_8', B_386) | ~v3_pre_topc(B_386, A_343) | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0(A_343))) | ~v2_pre_topc(A_343) | ~m1_pre_topc('#skF_7', A_343) | ~l1_pre_topc(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_132, c_233])).
% 6.17/2.17  tff(c_970, plain, (m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_962, c_243])).
% 6.17/2.17  tff(c_996, plain, (m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_58, c_72, c_970])).
% 6.17/2.17  tff(c_997, plain, (m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_996])).
% 6.17/2.17  tff(c_1044, plain, (~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_997])).
% 6.17/2.17  tff(c_1047, plain, (~v1_tsep_1('#skF_7', '#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_182, c_1044])).
% 6.17/2.17  tff(c_1051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_58, c_72, c_60, c_1047])).
% 6.17/2.17  tff(c_1053, plain, (v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_997])).
% 6.17/2.17  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.17/2.17  tff(c_14, plain, (![A_23, B_24]: (m1_connsp_2('#skF_1'(A_23, B_24), A_23, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.17/2.17  tff(c_158, plain, (![C_351, A_352, B_353]: (m1_subset_1(C_351, k1_zfmisc_1(u1_struct_0(A_352))) | ~m1_connsp_2(C_351, A_352, B_353) | ~m1_subset_1(B_353, u1_struct_0(A_352)) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.17/2.17  tff(c_168, plain, (![A_358, B_359]: (m1_subset_1('#skF_1'(A_358, B_359), k1_zfmisc_1(u1_struct_0(A_358))) | ~m1_subset_1(B_359, u1_struct_0(A_358)) | ~l1_pre_topc(A_358) | ~v2_pre_topc(A_358) | v2_struct_0(A_358))), inference(resolution, [status(thm)], [c_14, c_158])).
% 6.17/2.17  tff(c_4, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.17/2.17  tff(c_172, plain, (![A_360, A_361, B_362]: (~v1_xboole_0(u1_struct_0(A_360)) | ~r2_hidden(A_361, '#skF_1'(A_360, B_362)) | ~m1_subset_1(B_362, u1_struct_0(A_360)) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(resolution, [status(thm)], [c_168, c_4])).
% 6.17/2.17  tff(c_188, plain, (![A_367, B_368, A_369]: (~v1_xboole_0(u1_struct_0(A_367)) | ~m1_subset_1(B_368, u1_struct_0(A_367)) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367) | v1_xboole_0('#skF_1'(A_367, B_368)) | ~m1_subset_1(A_369, '#skF_1'(A_367, B_368)))), inference(resolution, [status(thm)], [c_2, c_172])).
% 6.17/2.17  tff(c_194, plain, (![A_369]: (~v1_xboole_0(u1_struct_0('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | v1_xboole_0('#skF_1'('#skF_7', '#skF_8')) | ~m1_subset_1(A_369, '#skF_1'('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_89, c_188])).
% 6.17/2.17  tff(c_201, plain, (![A_369]: (~v1_xboole_0(u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | v1_xboole_0('#skF_1'('#skF_7', '#skF_8')) | ~m1_subset_1(A_369, '#skF_1'('#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_102, c_194])).
% 6.17/2.17  tff(c_202, plain, (![A_369]: (~v1_xboole_0(u1_struct_0('#skF_7')) | v1_xboole_0('#skF_1'('#skF_7', '#skF_8')) | ~m1_subset_1(A_369, '#skF_1'('#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_62, c_201])).
% 6.17/2.17  tff(c_207, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_202])).
% 6.17/2.17  tff(c_1052, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_997])).
% 6.17/2.17  tff(c_1070, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_1052])).
% 6.17/2.17  tff(c_1073, plain, (v1_xboole_0(u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2, c_1070])).
% 6.17/2.17  tff(c_1076, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1073])).
% 6.17/2.17  tff(c_1078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_1076])).
% 6.17/2.17  tff(c_1080, plain, (r2_hidden('#skF_8', u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_1052])).
% 6.17/2.17  tff(c_1079, plain, (m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_1052])).
% 6.17/2.17  tff(c_241, plain, (![B_386]: (m1_connsp_2(B_386, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_386) | ~v3_pre_topc(B_386, '#skF_5') | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_233])).
% 6.17/2.17  tff(c_250, plain, (![B_386]: (m1_connsp_2(B_386, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_386) | ~v3_pre_topc(B_386, '#skF_5') | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_241])).
% 6.17/2.17  tff(c_268, plain, (![B_390]: (m1_connsp_2(B_390, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_390) | ~v3_pre_topc(B_390, '#skF_5') | ~m1_subset_1(B_390, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_250])).
% 6.17/2.17  tff(c_276, plain, (![B_78]: (m1_connsp_2(u1_struct_0(B_78), '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0(B_78)) | ~v3_pre_topc(u1_struct_0(B_78), '#skF_5') | ~m1_pre_topc(B_78, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_268])).
% 6.17/2.17  tff(c_298, plain, (![B_395]: (m1_connsp_2(u1_struct_0(B_395), '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0(B_395)) | ~v3_pre_topc(u1_struct_0(B_395), '#skF_5') | ~m1_pre_topc(B_395, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_276])).
% 6.17/2.17  tff(c_12, plain, (![C_22, A_19, B_20]: (m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_connsp_2(C_22, A_19, B_20) | ~m1_subset_1(B_20, u1_struct_0(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.17/2.17  tff(c_300, plain, (![B_395]: (m1_subset_1(u1_struct_0(B_395), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_8', u1_struct_0(B_395)) | ~v3_pre_topc(u1_struct_0(B_395), '#skF_5') | ~m1_pre_topc(B_395, '#skF_5'))), inference(resolution, [status(thm)], [c_298, c_12])).
% 6.17/2.17  tff(c_303, plain, (![B_395]: (m1_subset_1(u1_struct_0(B_395), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_8', u1_struct_0(B_395)) | ~v3_pre_topc(u1_struct_0(B_395), '#skF_5') | ~m1_pre_topc(B_395, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_300])).
% 6.17/2.17  tff(c_304, plain, (![B_395]: (m1_subset_1(u1_struct_0(B_395), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden('#skF_8', u1_struct_0(B_395)) | ~v3_pre_topc(u1_struct_0(B_395), '#skF_5') | ~m1_pre_topc(B_395, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_303])).
% 6.17/2.17  tff(c_564, plain, (![A_424, B_425, C_426]: (m1_connsp_2('#skF_2'(A_424, B_425, C_426), A_424, B_425) | ~m1_connsp_2(C_426, A_424, B_425) | ~m1_subset_1(C_426, k1_zfmisc_1(u1_struct_0(A_424))) | ~m1_subset_1(B_425, u1_struct_0(A_424)) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424) | v2_struct_0(A_424))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.17/2.17  tff(c_570, plain, (![B_425, B_395]: (m1_connsp_2('#skF_2'('#skF_5', B_425, u1_struct_0(B_395)), '#skF_5', B_425) | ~m1_connsp_2(u1_struct_0(B_395), '#skF_5', B_425) | ~m1_subset_1(B_425, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_8', u1_struct_0(B_395)) | ~v3_pre_topc(u1_struct_0(B_395), '#skF_5') | ~m1_pre_topc(B_395, '#skF_5'))), inference(resolution, [status(thm)], [c_304, c_564])).
% 6.17/2.17  tff(c_587, plain, (![B_425, B_395]: (m1_connsp_2('#skF_2'('#skF_5', B_425, u1_struct_0(B_395)), '#skF_5', B_425) | ~m1_connsp_2(u1_struct_0(B_395), '#skF_5', B_425) | ~m1_subset_1(B_425, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_8', u1_struct_0(B_395)) | ~v3_pre_topc(u1_struct_0(B_395), '#skF_5') | ~m1_pre_topc(B_395, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_570])).
% 6.17/2.17  tff(c_588, plain, (![B_425, B_395]: (m1_connsp_2('#skF_2'('#skF_5', B_425, u1_struct_0(B_395)), '#skF_5', B_425) | ~m1_connsp_2(u1_struct_0(B_395), '#skF_5', B_425) | ~m1_subset_1(B_425, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_8', u1_struct_0(B_395)) | ~v3_pre_topc(u1_struct_0(B_395), '#skF_5') | ~m1_pre_topc(B_395, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_587])).
% 6.17/2.17  tff(c_1104, plain, (![B_530]: (~m1_connsp_2('#skF_2'('#skF_5', B_530, u1_struct_0('#skF_7')), '#skF_5', '#skF_8') | ~m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', B_530) | ~m1_subset_1(B_530, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_946])).
% 6.17/2.17  tff(c_1108, plain, (~m1_connsp_2(u1_struct_0('#skF_7'), '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_588, c_1104])).
% 6.17/2.17  tff(c_1116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1053, c_1080, c_56, c_1079, c_1108])).
% 6.17/2.17  tff(c_1118, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_202])).
% 6.17/2.17  tff(c_161, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_14, c_158])).
% 6.17/2.17  tff(c_1287, plain, (![B_563, A_564, C_565]: (r2_hidden(B_563, '#skF_3'(A_564, B_563, C_565)) | ~m1_connsp_2(C_565, A_564, B_563) | ~m1_subset_1(C_565, k1_zfmisc_1(u1_struct_0(A_564))) | ~m1_subset_1(B_563, u1_struct_0(A_564)) | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.17/2.17  tff(c_1737, plain, (![B_657, A_658, B_659]: (r2_hidden(B_657, '#skF_3'(A_658, B_657, '#skF_1'(A_658, B_659))) | ~m1_connsp_2('#skF_1'(A_658, B_659), A_658, B_657) | ~m1_subset_1(B_657, u1_struct_0(A_658)) | ~m1_subset_1(B_659, u1_struct_0(A_658)) | ~l1_pre_topc(A_658) | ~v2_pre_topc(A_658) | v2_struct_0(A_658))), inference(resolution, [status(thm)], [c_161, c_1287])).
% 6.17/2.17  tff(c_1528, plain, (![A_611, B_612, C_613]: (m1_subset_1('#skF_3'(A_611, B_612, C_613), k1_zfmisc_1(u1_struct_0(A_611))) | ~m1_connsp_2(C_613, A_611, B_612) | ~m1_subset_1(C_613, k1_zfmisc_1(u1_struct_0(A_611))) | ~m1_subset_1(B_612, u1_struct_0(A_611)) | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611) | v2_struct_0(A_611))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.17/2.17  tff(c_1573, plain, (![A_611, A_3, B_612, C_613]: (~v1_xboole_0(u1_struct_0(A_611)) | ~r2_hidden(A_3, '#skF_3'(A_611, B_612, C_613)) | ~m1_connsp_2(C_613, A_611, B_612) | ~m1_subset_1(C_613, k1_zfmisc_1(u1_struct_0(A_611))) | ~m1_subset_1(B_612, u1_struct_0(A_611)) | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611) | v2_struct_0(A_611))), inference(resolution, [status(thm)], [c_1528, c_4])).
% 6.17/2.17  tff(c_1826, plain, (![A_686, B_687, B_688]: (~v1_xboole_0(u1_struct_0(A_686)) | ~m1_subset_1('#skF_1'(A_686, B_687), k1_zfmisc_1(u1_struct_0(A_686))) | ~m1_connsp_2('#skF_1'(A_686, B_687), A_686, B_688) | ~m1_subset_1(B_688, u1_struct_0(A_686)) | ~m1_subset_1(B_687, u1_struct_0(A_686)) | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(resolution, [status(thm)], [c_1737, c_1573])).
% 6.17/2.17  tff(c_1842, plain, (![A_689, B_690, B_691]: (~v1_xboole_0(u1_struct_0(A_689)) | ~m1_connsp_2('#skF_1'(A_689, B_690), A_689, B_691) | ~m1_subset_1(B_691, u1_struct_0(A_689)) | ~m1_subset_1(B_690, u1_struct_0(A_689)) | ~l1_pre_topc(A_689) | ~v2_pre_topc(A_689) | v2_struct_0(A_689))), inference(resolution, [status(thm)], [c_161, c_1826])).
% 6.17/2.17  tff(c_1869, plain, (![A_692, B_693]: (~v1_xboole_0(u1_struct_0(A_692)) | ~m1_subset_1(B_693, u1_struct_0(A_692)) | ~l1_pre_topc(A_692) | ~v2_pre_topc(A_692) | v2_struct_0(A_692))), inference(resolution, [status(thm)], [c_14, c_1842])).
% 6.17/2.17  tff(c_1878, plain, (~v1_xboole_0(u1_struct_0('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_89, c_1869])).
% 6.17/2.17  tff(c_1886, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_102, c_1118, c_1878])).
% 6.17/2.17  tff(c_1888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1886])).
% 6.17/2.17  tff(c_1889, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 6.17/2.17  tff(c_2606, plain, (![F_839, D_841, A_840, B_842, C_838]: (r1_tmap_1(D_841, A_840, k2_tmap_1(B_842, A_840, C_838, D_841), F_839) | ~r1_tmap_1(B_842, A_840, C_838, F_839) | ~m1_subset_1(F_839, u1_struct_0(D_841)) | ~m1_subset_1(F_839, u1_struct_0(B_842)) | ~m1_pre_topc(D_841, B_842) | v2_struct_0(D_841) | ~m1_subset_1(C_838, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_842), u1_struct_0(A_840)))) | ~v1_funct_2(C_838, u1_struct_0(B_842), u1_struct_0(A_840)) | ~v1_funct_1(C_838) | ~l1_pre_topc(B_842) | ~v2_pre_topc(B_842) | v2_struct_0(B_842) | ~l1_pre_topc(A_840) | ~v2_pre_topc(A_840) | v2_struct_0(A_840))), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.17/2.17  tff(c_2608, plain, (![D_841, F_839]: (r1_tmap_1(D_841, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_841), F_839) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_839) | ~m1_subset_1(F_839, u1_struct_0(D_841)) | ~m1_subset_1(F_839, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_841, '#skF_5') | v2_struct_0(D_841) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_2606])).
% 6.17/2.17  tff(c_2611, plain, (![D_841, F_839]: (r1_tmap_1(D_841, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_841), F_839) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_839) | ~m1_subset_1(F_839, u1_struct_0(D_841)) | ~m1_subset_1(F_839, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_841, '#skF_5') | v2_struct_0(D_841) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_68, c_66, c_2608])).
% 6.17/2.17  tff(c_2613, plain, (![D_843, F_844]: (r1_tmap_1(D_843, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_843), F_844) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_844) | ~m1_subset_1(F_844, u1_struct_0(D_843)) | ~m1_subset_1(F_844, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_843, '#skF_5') | v2_struct_0(D_843))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_2611])).
% 6.17/2.17  tff(c_1890, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 6.17/2.17  tff(c_2616, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2613, c_1890])).
% 6.17/2.17  tff(c_2619, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_89, c_1889, c_2616])).
% 6.17/2.17  tff(c_2621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2619])).
% 6.17/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.17  
% 6.17/2.17  Inference rules
% 6.17/2.17  ----------------------
% 6.17/2.17  #Ref     : 0
% 6.17/2.17  #Sup     : 480
% 6.17/2.17  #Fact    : 0
% 6.17/2.17  #Define  : 0
% 6.17/2.17  #Split   : 13
% 6.17/2.17  #Chain   : 0
% 6.17/2.17  #Close   : 0
% 6.17/2.17  
% 6.17/2.17  Ordering : KBO
% 6.17/2.17  
% 6.17/2.17  Simplification rules
% 6.17/2.17  ----------------------
% 6.17/2.17  #Subsume      : 107
% 6.17/2.17  #Demod        : 498
% 6.17/2.17  #Tautology    : 17
% 6.17/2.17  #SimpNegUnit  : 200
% 6.17/2.17  #BackRed      : 0
% 6.17/2.17  
% 6.17/2.17  #Partial instantiations: 0
% 6.17/2.17  #Strategies tried      : 1
% 6.17/2.17  
% 6.17/2.17  Timing (in seconds)
% 6.17/2.17  ----------------------
% 6.17/2.18  Preprocessing        : 0.45
% 6.17/2.18  Parsing              : 0.23
% 6.17/2.18  CNF conversion       : 0.06
% 6.17/2.18  Main loop            : 0.92
% 6.17/2.18  Inferencing          : 0.35
% 6.17/2.18  Reduction            : 0.27
% 6.17/2.18  Demodulation         : 0.18
% 6.17/2.18  BG Simplification    : 0.04
% 6.17/2.18  Subsumption          : 0.20
% 6.17/2.18  Abstraction          : 0.04
% 6.17/2.18  MUC search           : 0.00
% 6.17/2.18  Cooper               : 0.00
% 6.17/2.18  Total                : 1.43
% 6.17/2.18  Index Insertion      : 0.00
% 6.17/2.18  Index Deletion       : 0.00
% 6.17/2.18  Index Matching       : 0.00
% 6.17/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
