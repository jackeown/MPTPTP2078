%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:30 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 386 expanded)
%              Number of leaves         :   39 ( 166 expanded)
%              Depth                    :   15
%              Number of atoms          :  504 (3070 expanded)
%              Number of equality atoms :   32 ( 151 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_308,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( ( v1_tsep_1(C,B)
                            & m1_pre_topc(C,B)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,A,E,F)
                                    <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_161,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_98,axiom,(
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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_243,axiom,(
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
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_201,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_34,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_72,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_81,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_72])).

tff(c_137,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_118,plain,(
    ! [B_342,A_343] :
      ( v2_pre_topc(B_342)
      | ~ m1_pre_topc(B_342,A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_121,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_130,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_121])).

tff(c_87,plain,(
    ! [B_332,A_333] :
      ( l1_pre_topc(B_332)
      | ~ m1_pre_topc(B_332,A_333)
      | ~ l1_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_87])).

tff(c_99,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_90])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_48,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_44,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [A_336,B_337] :
      ( ~ r2_hidden('#skF_1'(A_336,B_337),B_337)
      | r1_tarski(A_336,B_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_300,plain,(
    ! [B_391,C_392,A_393] :
      ( m1_pre_topc(B_391,C_392)
      | ~ r1_tarski(u1_struct_0(B_391),u1_struct_0(C_392))
      | ~ m1_pre_topc(C_392,A_393)
      | v2_struct_0(C_392)
      | ~ m1_pre_topc(B_391,A_393)
      | ~ v1_tsep_1(B_391,A_393)
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_337,plain,(
    ! [B_397,A_398] :
      ( m1_pre_topc(B_397,B_397)
      | v2_struct_0(B_397)
      | ~ m1_pre_topc(B_397,A_398)
      | ~ v1_tsep_1(B_397,A_398)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(resolution,[status(thm)],[c_112,c_300])).

tff(c_339,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_337])).

tff(c_342,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_339])).

tff(c_343,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_342])).

tff(c_96,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_87])).

tff(c_103,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_96])).

tff(c_24,plain,(
    ! [B_78,A_76] :
      ( m1_subset_1(u1_struct_0(B_78),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_140,plain,(
    ! [C_344,A_345,B_346] :
      ( r2_hidden(C_344,A_345)
      | ~ r2_hidden(C_344,B_346)
      | ~ m1_subset_1(B_346,k1_zfmisc_1(A_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_194,plain,(
    ! [A_358,B_359,A_360] :
      ( r2_hidden('#skF_1'(A_358,B_359),A_360)
      | ~ m1_subset_1(A_358,k1_zfmisc_1(A_360))
      | r1_tarski(A_358,B_359) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_8,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_281,plain,(
    ! [A_385,B_386,A_387,A_388] :
      ( r2_hidden('#skF_1'(A_385,B_386),A_387)
      | ~ m1_subset_1(A_388,k1_zfmisc_1(A_387))
      | ~ m1_subset_1(A_385,k1_zfmisc_1(A_388))
      | r1_tarski(A_385,B_386) ) ),
    inference(resolution,[status(thm)],[c_194,c_8])).

tff(c_572,plain,(
    ! [A_432,B_433,A_434,B_435] :
      ( r2_hidden('#skF_1'(A_432,B_433),u1_struct_0(A_434))
      | ~ m1_subset_1(A_432,k1_zfmisc_1(u1_struct_0(B_435)))
      | r1_tarski(A_432,B_433)
      | ~ m1_pre_topc(B_435,A_434)
      | ~ l1_pre_topc(A_434) ) ),
    inference(resolution,[status(thm)],[c_24,c_281])).

tff(c_646,plain,(
    ! [B_471,B_472,A_473,A_474] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_471),B_472),u1_struct_0(A_473))
      | r1_tarski(u1_struct_0(B_471),B_472)
      | ~ m1_pre_topc(A_474,A_473)
      | ~ l1_pre_topc(A_473)
      | ~ m1_pre_topc(B_471,A_474)
      | ~ l1_pre_topc(A_474) ) ),
    inference(resolution,[status(thm)],[c_24,c_572])).

tff(c_654,plain,(
    ! [B_471,B_472] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_471),B_472),u1_struct_0('#skF_5'))
      | r1_tarski(u1_struct_0(B_471),B_472)
      | ~ l1_pre_topc('#skF_5')
      | ~ m1_pre_topc(B_471,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_646])).

tff(c_713,plain,(
    ! [B_478,B_479] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_478),B_479),u1_struct_0('#skF_5'))
      | r1_tarski(u1_struct_0(B_478),B_479)
      | ~ m1_pre_topc(B_478,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_99,c_654])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_725,plain,(
    ! [B_480] :
      ( r1_tarski(u1_struct_0(B_480),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_480,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_713,c_4])).

tff(c_22,plain,(
    ! [B_73,C_75,A_69] :
      ( v1_tsep_1(B_73,C_75)
      | ~ r1_tarski(u1_struct_0(B_73),u1_struct_0(C_75))
      | ~ m1_pre_topc(C_75,A_69)
      | v2_struct_0(C_75)
      | ~ m1_pre_topc(B_73,A_69)
      | ~ v1_tsep_1(B_73,A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_735,plain,(
    ! [B_480,A_69] :
      ( v1_tsep_1(B_480,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_69)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_480,A_69)
      | ~ v1_tsep_1(B_480,A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69)
      | ~ m1_pre_topc(B_480,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_725,c_22])).

tff(c_814,plain,(
    ! [B_491,A_492] :
      ( v1_tsep_1(B_491,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_492)
      | ~ m1_pre_topc(B_491,A_492)
      | ~ v1_tsep_1(B_491,A_492)
      | ~ l1_pre_topc(A_492)
      | ~ v2_pre_topc(A_492)
      | v2_struct_0(A_492)
      | ~ m1_pre_topc(B_491,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_735])).

tff(c_818,plain,
    ( v1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_814])).

tff(c_825,plain,
    ( v1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_62,c_60,c_56,c_52,c_818])).

tff(c_826,plain,(
    v1_tsep_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_825])).

tff(c_593,plain,(
    ! [E_446,A_443,D_447,B_445,C_444] :
      ( k3_tmap_1(A_443,B_445,C_444,D_447,E_446) = k2_partfun1(u1_struct_0(C_444),u1_struct_0(B_445),E_446,u1_struct_0(D_447))
      | ~ m1_pre_topc(D_447,C_444)
      | ~ m1_subset_1(E_446,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_444),u1_struct_0(B_445))))
      | ~ v1_funct_2(E_446,u1_struct_0(C_444),u1_struct_0(B_445))
      | ~ v1_funct_1(E_446)
      | ~ m1_pre_topc(D_447,A_443)
      | ~ m1_pre_topc(C_444,A_443)
      | ~ l1_pre_topc(B_445)
      | ~ v2_pre_topc(B_445)
      | v2_struct_0(B_445)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_595,plain,(
    ! [A_443,D_447] :
      ( k3_tmap_1(A_443,'#skF_2','#skF_5',D_447,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_447))
      | ~ m1_pre_topc(D_447,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_447,A_443)
      | ~ m1_pre_topc('#skF_5',A_443)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_46,c_593])).

tff(c_598,plain,(
    ! [A_443,D_447] :
      ( k3_tmap_1(A_443,'#skF_2','#skF_5',D_447,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_447))
      | ~ m1_pre_topc(D_447,'#skF_5')
      | ~ m1_pre_topc(D_447,A_443)
      | ~ m1_pre_topc('#skF_5',A_443)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_50,c_48,c_595])).

tff(c_919,plain,(
    ! [A_500,D_501] :
      ( k3_tmap_1(A_500,'#skF_2','#skF_5',D_501,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_501))
      | ~ m1_pre_topc(D_501,'#skF_5')
      | ~ m1_pre_topc(D_501,A_500)
      | ~ m1_pre_topc('#skF_5',A_500)
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_598])).

tff(c_929,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_919])).

tff(c_945,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_52,c_40,c_929])).

tff(c_946,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_945])).

tff(c_483,plain,(
    ! [A_416,B_417,C_418,D_419] :
      ( k2_partfun1(u1_struct_0(A_416),u1_struct_0(B_417),C_418,u1_struct_0(D_419)) = k2_tmap_1(A_416,B_417,C_418,D_419)
      | ~ m1_pre_topc(D_419,A_416)
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_416),u1_struct_0(B_417))))
      | ~ v1_funct_2(C_418,u1_struct_0(A_416),u1_struct_0(B_417))
      | ~ v1_funct_1(C_418)
      | ~ l1_pre_topc(B_417)
      | ~ v2_pre_topc(B_417)
      | v2_struct_0(B_417)
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_485,plain,(
    ! [D_419] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_419)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_419)
      | ~ m1_pre_topc(D_419,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_483])).

tff(c_488,plain,(
    ! [D_419] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_419)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_419)
      | ~ m1_pre_topc(D_419,'#skF_5')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_99,c_68,c_66,c_50,c_48,c_485])).

tff(c_489,plain,(
    ! [D_419] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_419)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_419)
      | ~ m1_pre_topc(D_419,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_70,c_488])).

tff(c_950,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_489])).

tff(c_957,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_950])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_7')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_78])).

tff(c_193,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_80])).

tff(c_962,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_193])).

tff(c_28,plain,(
    ! [C_190,B_174,A_142,D_198,F_204] :
      ( r1_tmap_1(B_174,A_142,C_190,F_204)
      | ~ r1_tmap_1(D_198,A_142,k2_tmap_1(B_174,A_142,C_190,D_198),F_204)
      | ~ m1_subset_1(F_204,u1_struct_0(D_198))
      | ~ m1_subset_1(F_204,u1_struct_0(B_174))
      | ~ m1_pre_topc(D_198,B_174)
      | ~ v1_tsep_1(D_198,B_174)
      | v2_struct_0(D_198)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_174),u1_struct_0(A_142))))
      | ~ v1_funct_2(C_190,u1_struct_0(B_174),u1_struct_0(A_142))
      | ~ v1_funct_1(C_190)
      | ~ l1_pre_topc(B_174)
      | ~ v2_pre_topc(B_174)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_968,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ v1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_962,c_28])).

tff(c_971,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_130,c_99,c_50,c_48,c_46,c_826,c_40,c_82,c_36,c_968])).

tff(c_973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_54,c_58,c_137,c_971])).

tff(c_975,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_1528,plain,(
    ! [C_611,F_612,B_615,D_614,A_613] :
      ( r1_tmap_1(D_614,A_613,k2_tmap_1(B_615,A_613,C_611,D_614),F_612)
      | ~ r1_tmap_1(B_615,A_613,C_611,F_612)
      | ~ m1_subset_1(F_612,u1_struct_0(D_614))
      | ~ m1_subset_1(F_612,u1_struct_0(B_615))
      | ~ m1_pre_topc(D_614,B_615)
      | v2_struct_0(D_614)
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_615),u1_struct_0(A_613))))
      | ~ v1_funct_2(C_611,u1_struct_0(B_615),u1_struct_0(A_613))
      | ~ v1_funct_1(C_611)
      | ~ l1_pre_topc(B_615)
      | ~ v2_pre_topc(B_615)
      | v2_struct_0(B_615)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1530,plain,(
    ! [D_614,F_612] :
      ( r1_tmap_1(D_614,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_614),F_612)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_612)
      | ~ m1_subset_1(F_612,u1_struct_0(D_614))
      | ~ m1_subset_1(F_612,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_614,'#skF_5')
      | v2_struct_0(D_614)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_1528])).

tff(c_1533,plain,(
    ! [D_614,F_612] :
      ( r1_tmap_1(D_614,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_614),F_612)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_612)
      | ~ m1_subset_1(F_612,u1_struct_0(D_614))
      | ~ m1_subset_1(F_612,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_614,'#skF_5')
      | v2_struct_0(D_614)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_130,c_99,c_50,c_48,c_1530])).

tff(c_1574,plain,(
    ! [D_637,F_638] :
      ( r1_tmap_1(D_637,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_637),F_638)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_638)
      | ~ m1_subset_1(F_638,u1_struct_0(D_637))
      | ~ m1_subset_1(F_638,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_637,'#skF_5')
      | v2_struct_0(D_637) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_54,c_1533])).

tff(c_1427,plain,(
    ! [D_601,C_598,E_600,A_597,B_599] :
      ( k3_tmap_1(A_597,B_599,C_598,D_601,E_600) = k2_partfun1(u1_struct_0(C_598),u1_struct_0(B_599),E_600,u1_struct_0(D_601))
      | ~ m1_pre_topc(D_601,C_598)
      | ~ m1_subset_1(E_600,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_598),u1_struct_0(B_599))))
      | ~ v1_funct_2(E_600,u1_struct_0(C_598),u1_struct_0(B_599))
      | ~ v1_funct_1(E_600)
      | ~ m1_pre_topc(D_601,A_597)
      | ~ m1_pre_topc(C_598,A_597)
      | ~ l1_pre_topc(B_599)
      | ~ v2_pre_topc(B_599)
      | v2_struct_0(B_599)
      | ~ l1_pre_topc(A_597)
      | ~ v2_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1429,plain,(
    ! [A_597,D_601] :
      ( k3_tmap_1(A_597,'#skF_2','#skF_5',D_601,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_601))
      | ~ m1_pre_topc(D_601,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_601,A_597)
      | ~ m1_pre_topc('#skF_5',A_597)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_597)
      | ~ v2_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(resolution,[status(thm)],[c_46,c_1427])).

tff(c_1432,plain,(
    ! [A_597,D_601] :
      ( k3_tmap_1(A_597,'#skF_2','#skF_5',D_601,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_601))
      | ~ m1_pre_topc(D_601,'#skF_5')
      | ~ m1_pre_topc(D_601,A_597)
      | ~ m1_pre_topc('#skF_5',A_597)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_597)
      | ~ v2_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_50,c_48,c_1429])).

tff(c_1463,plain,(
    ! [A_609,D_610] :
      ( k3_tmap_1(A_609,'#skF_2','#skF_5',D_610,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_610))
      | ~ m1_pre_topc(D_610,'#skF_5')
      | ~ m1_pre_topc(D_610,A_609)
      | ~ m1_pre_topc('#skF_5',A_609)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1432])).

tff(c_1473,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1463])).

tff(c_1489,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_52,c_40,c_1473])).

tff(c_1490,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1489])).

tff(c_1326,plain,(
    ! [A_570,B_571,C_572,D_573] :
      ( k2_partfun1(u1_struct_0(A_570),u1_struct_0(B_571),C_572,u1_struct_0(D_573)) = k2_tmap_1(A_570,B_571,C_572,D_573)
      | ~ m1_pre_topc(D_573,A_570)
      | ~ m1_subset_1(C_572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_570),u1_struct_0(B_571))))
      | ~ v1_funct_2(C_572,u1_struct_0(A_570),u1_struct_0(B_571))
      | ~ v1_funct_1(C_572)
      | ~ l1_pre_topc(B_571)
      | ~ v2_pre_topc(B_571)
      | v2_struct_0(B_571)
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570)
      | v2_struct_0(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1328,plain,(
    ! [D_573] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_573)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_573)
      | ~ m1_pre_topc(D_573,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_1326])).

tff(c_1331,plain,(
    ! [D_573] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_573)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_573)
      | ~ m1_pre_topc(D_573,'#skF_5')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_99,c_68,c_66,c_50,c_48,c_1328])).

tff(c_1332,plain,(
    ! [D_573] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_573)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_573)
      | ~ m1_pre_topc(D_573,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_70,c_1331])).

tff(c_1494,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_1332])).

tff(c_1501,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1494])).

tff(c_974,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_1506,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_974])).

tff(c_1579,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1574,c_1506])).

tff(c_1586,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82,c_36,c_975,c_1579])).

tff(c_1588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.81  
% 4.91/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.82  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.91/1.82  
% 4.91/1.82  %Foreground sorts:
% 4.91/1.82  
% 4.91/1.82  
% 4.91/1.82  %Background operators:
% 4.91/1.82  
% 4.91/1.82  
% 4.91/1.82  %Foreground operators:
% 4.91/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.91/1.82  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.91/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.91/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.91/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.91/1.82  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.91/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.91/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.91/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.91/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.91/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.91/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.91/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.91/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.91/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.91/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.91/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.91/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.91/1.82  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.91/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.91/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.91/1.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.91/1.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.91/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.91/1.82  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.91/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.91/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.91/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.91/1.82  
% 4.99/1.84  tff(f_308, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 4.99/1.84  tff(f_48, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.99/1.84  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.99/1.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.99/1.84  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 4.99/1.84  tff(f_161, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.99/1.84  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.99/1.84  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.99/1.84  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.99/1.84  tff(f_243, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.99/1.84  tff(f_201, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.99/1.84  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_34, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_82, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 4.99/1.84  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_72, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_81, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_72])).
% 4.99/1.84  tff(c_137, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_81])).
% 4.99/1.84  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_62, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_118, plain, (![B_342, A_343]: (v2_pre_topc(B_342) | ~m1_pre_topc(B_342, A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.99/1.84  tff(c_121, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_118])).
% 4.99/1.84  tff(c_130, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_121])).
% 4.99/1.84  tff(c_87, plain, (![B_332, A_333]: (l1_pre_topc(B_332) | ~m1_pre_topc(B_332, A_333) | ~l1_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.99/1.84  tff(c_90, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_87])).
% 4.99/1.84  tff(c_99, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_90])).
% 4.99/1.84  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_48, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_44, plain, (v1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.99/1.84  tff(c_107, plain, (![A_336, B_337]: (~r2_hidden('#skF_1'(A_336, B_337), B_337) | r1_tarski(A_336, B_337))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.99/1.84  tff(c_112, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_107])).
% 4.99/1.84  tff(c_300, plain, (![B_391, C_392, A_393]: (m1_pre_topc(B_391, C_392) | ~r1_tarski(u1_struct_0(B_391), u1_struct_0(C_392)) | ~m1_pre_topc(C_392, A_393) | v2_struct_0(C_392) | ~m1_pre_topc(B_391, A_393) | ~v1_tsep_1(B_391, A_393) | ~l1_pre_topc(A_393) | ~v2_pre_topc(A_393) | v2_struct_0(A_393))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.99/1.84  tff(c_337, plain, (![B_397, A_398]: (m1_pre_topc(B_397, B_397) | v2_struct_0(B_397) | ~m1_pre_topc(B_397, A_398) | ~v1_tsep_1(B_397, A_398) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398) | v2_struct_0(A_398))), inference(resolution, [status(thm)], [c_112, c_300])).
% 4.99/1.84  tff(c_339, plain, (m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_337])).
% 4.99/1.84  tff(c_342, plain, (m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_339])).
% 4.99/1.84  tff(c_343, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_342])).
% 4.99/1.84  tff(c_96, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_87])).
% 4.99/1.84  tff(c_103, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_96])).
% 4.99/1.84  tff(c_24, plain, (![B_78, A_76]: (m1_subset_1(u1_struct_0(B_78), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_pre_topc(B_78, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.99/1.84  tff(c_140, plain, (![C_344, A_345, B_346]: (r2_hidden(C_344, A_345) | ~r2_hidden(C_344, B_346) | ~m1_subset_1(B_346, k1_zfmisc_1(A_345)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.99/1.84  tff(c_194, plain, (![A_358, B_359, A_360]: (r2_hidden('#skF_1'(A_358, B_359), A_360) | ~m1_subset_1(A_358, k1_zfmisc_1(A_360)) | r1_tarski(A_358, B_359))), inference(resolution, [status(thm)], [c_6, c_140])).
% 4.99/1.84  tff(c_8, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.99/1.84  tff(c_281, plain, (![A_385, B_386, A_387, A_388]: (r2_hidden('#skF_1'(A_385, B_386), A_387) | ~m1_subset_1(A_388, k1_zfmisc_1(A_387)) | ~m1_subset_1(A_385, k1_zfmisc_1(A_388)) | r1_tarski(A_385, B_386))), inference(resolution, [status(thm)], [c_194, c_8])).
% 4.99/1.84  tff(c_572, plain, (![A_432, B_433, A_434, B_435]: (r2_hidden('#skF_1'(A_432, B_433), u1_struct_0(A_434)) | ~m1_subset_1(A_432, k1_zfmisc_1(u1_struct_0(B_435))) | r1_tarski(A_432, B_433) | ~m1_pre_topc(B_435, A_434) | ~l1_pre_topc(A_434))), inference(resolution, [status(thm)], [c_24, c_281])).
% 4.99/1.84  tff(c_646, plain, (![B_471, B_472, A_473, A_474]: (r2_hidden('#skF_1'(u1_struct_0(B_471), B_472), u1_struct_0(A_473)) | r1_tarski(u1_struct_0(B_471), B_472) | ~m1_pre_topc(A_474, A_473) | ~l1_pre_topc(A_473) | ~m1_pre_topc(B_471, A_474) | ~l1_pre_topc(A_474))), inference(resolution, [status(thm)], [c_24, c_572])).
% 4.99/1.84  tff(c_654, plain, (![B_471, B_472]: (r2_hidden('#skF_1'(u1_struct_0(B_471), B_472), u1_struct_0('#skF_5')) | r1_tarski(u1_struct_0(B_471), B_472) | ~l1_pre_topc('#skF_5') | ~m1_pre_topc(B_471, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_646])).
% 4.99/1.84  tff(c_713, plain, (![B_478, B_479]: (r2_hidden('#skF_1'(u1_struct_0(B_478), B_479), u1_struct_0('#skF_5')) | r1_tarski(u1_struct_0(B_478), B_479) | ~m1_pre_topc(B_478, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_99, c_654])).
% 4.99/1.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.99/1.84  tff(c_725, plain, (![B_480]: (r1_tarski(u1_struct_0(B_480), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_480, '#skF_4'))), inference(resolution, [status(thm)], [c_713, c_4])).
% 4.99/1.84  tff(c_22, plain, (![B_73, C_75, A_69]: (v1_tsep_1(B_73, C_75) | ~r1_tarski(u1_struct_0(B_73), u1_struct_0(C_75)) | ~m1_pre_topc(C_75, A_69) | v2_struct_0(C_75) | ~m1_pre_topc(B_73, A_69) | ~v1_tsep_1(B_73, A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.99/1.84  tff(c_735, plain, (![B_480, A_69]: (v1_tsep_1(B_480, '#skF_5') | ~m1_pre_topc('#skF_5', A_69) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_480, A_69) | ~v1_tsep_1(B_480, A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69) | ~m1_pre_topc(B_480, '#skF_4'))), inference(resolution, [status(thm)], [c_725, c_22])).
% 4.99/1.84  tff(c_814, plain, (![B_491, A_492]: (v1_tsep_1(B_491, '#skF_5') | ~m1_pre_topc('#skF_5', A_492) | ~m1_pre_topc(B_491, A_492) | ~v1_tsep_1(B_491, A_492) | ~l1_pre_topc(A_492) | ~v2_pre_topc(A_492) | v2_struct_0(A_492) | ~m1_pre_topc(B_491, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_735])).
% 4.99/1.84  tff(c_818, plain, (v1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_814])).
% 4.99/1.84  tff(c_825, plain, (v1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_62, c_60, c_56, c_52, c_818])).
% 4.99/1.84  tff(c_826, plain, (v1_tsep_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_825])).
% 4.99/1.84  tff(c_593, plain, (![E_446, A_443, D_447, B_445, C_444]: (k3_tmap_1(A_443, B_445, C_444, D_447, E_446)=k2_partfun1(u1_struct_0(C_444), u1_struct_0(B_445), E_446, u1_struct_0(D_447)) | ~m1_pre_topc(D_447, C_444) | ~m1_subset_1(E_446, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_444), u1_struct_0(B_445)))) | ~v1_funct_2(E_446, u1_struct_0(C_444), u1_struct_0(B_445)) | ~v1_funct_1(E_446) | ~m1_pre_topc(D_447, A_443) | ~m1_pre_topc(C_444, A_443) | ~l1_pre_topc(B_445) | ~v2_pre_topc(B_445) | v2_struct_0(B_445) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.99/1.84  tff(c_595, plain, (![A_443, D_447]: (k3_tmap_1(A_443, '#skF_2', '#skF_5', D_447, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_447)) | ~m1_pre_topc(D_447, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_447, A_443) | ~m1_pre_topc('#skF_5', A_443) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(resolution, [status(thm)], [c_46, c_593])).
% 4.99/1.84  tff(c_598, plain, (![A_443, D_447]: (k3_tmap_1(A_443, '#skF_2', '#skF_5', D_447, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_447)) | ~m1_pre_topc(D_447, '#skF_5') | ~m1_pre_topc(D_447, A_443) | ~m1_pre_topc('#skF_5', A_443) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_50, c_48, c_595])).
% 4.99/1.84  tff(c_919, plain, (![A_500, D_501]: (k3_tmap_1(A_500, '#skF_2', '#skF_5', D_501, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_501)) | ~m1_pre_topc(D_501, '#skF_5') | ~m1_pre_topc(D_501, A_500) | ~m1_pre_topc('#skF_5', A_500) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(negUnitSimplification, [status(thm)], [c_70, c_598])).
% 4.99/1.84  tff(c_929, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_919])).
% 4.99/1.84  tff(c_945, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_52, c_40, c_929])).
% 4.99/1.84  tff(c_946, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_945])).
% 4.99/1.84  tff(c_483, plain, (![A_416, B_417, C_418, D_419]: (k2_partfun1(u1_struct_0(A_416), u1_struct_0(B_417), C_418, u1_struct_0(D_419))=k2_tmap_1(A_416, B_417, C_418, D_419) | ~m1_pre_topc(D_419, A_416) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_416), u1_struct_0(B_417)))) | ~v1_funct_2(C_418, u1_struct_0(A_416), u1_struct_0(B_417)) | ~v1_funct_1(C_418) | ~l1_pre_topc(B_417) | ~v2_pre_topc(B_417) | v2_struct_0(B_417) | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | v2_struct_0(A_416))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.99/1.84  tff(c_485, plain, (![D_419]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_419))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_419) | ~m1_pre_topc(D_419, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_483])).
% 4.99/1.84  tff(c_488, plain, (![D_419]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_419))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_419) | ~m1_pre_topc(D_419, '#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_99, c_68, c_66, c_50, c_48, c_485])).
% 4.99/1.84  tff(c_489, plain, (![D_419]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_419))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_419) | ~m1_pre_topc(D_419, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_70, c_488])).
% 4.99/1.84  tff(c_950, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_946, c_489])).
% 4.99/1.84  tff(c_957, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_950])).
% 4.99/1.84  tff(c_78, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_7') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_308])).
% 4.99/1.84  tff(c_80, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_78])).
% 4.99/1.84  tff(c_193, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_137, c_80])).
% 4.99/1.84  tff(c_962, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_957, c_193])).
% 4.99/1.84  tff(c_28, plain, (![C_190, B_174, A_142, D_198, F_204]: (r1_tmap_1(B_174, A_142, C_190, F_204) | ~r1_tmap_1(D_198, A_142, k2_tmap_1(B_174, A_142, C_190, D_198), F_204) | ~m1_subset_1(F_204, u1_struct_0(D_198)) | ~m1_subset_1(F_204, u1_struct_0(B_174)) | ~m1_pre_topc(D_198, B_174) | ~v1_tsep_1(D_198, B_174) | v2_struct_0(D_198) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_174), u1_struct_0(A_142)))) | ~v1_funct_2(C_190, u1_struct_0(B_174), u1_struct_0(A_142)) | ~v1_funct_1(C_190) | ~l1_pre_topc(B_174) | ~v2_pre_topc(B_174) | v2_struct_0(B_174) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.99/1.84  tff(c_968, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~v1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_962, c_28])).
% 4.99/1.84  tff(c_971, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_130, c_99, c_50, c_48, c_46, c_826, c_40, c_82, c_36, c_968])).
% 4.99/1.84  tff(c_973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_54, c_58, c_137, c_971])).
% 4.99/1.84  tff(c_975, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 4.99/1.84  tff(c_1528, plain, (![C_611, F_612, B_615, D_614, A_613]: (r1_tmap_1(D_614, A_613, k2_tmap_1(B_615, A_613, C_611, D_614), F_612) | ~r1_tmap_1(B_615, A_613, C_611, F_612) | ~m1_subset_1(F_612, u1_struct_0(D_614)) | ~m1_subset_1(F_612, u1_struct_0(B_615)) | ~m1_pre_topc(D_614, B_615) | v2_struct_0(D_614) | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_615), u1_struct_0(A_613)))) | ~v1_funct_2(C_611, u1_struct_0(B_615), u1_struct_0(A_613)) | ~v1_funct_1(C_611) | ~l1_pre_topc(B_615) | ~v2_pre_topc(B_615) | v2_struct_0(B_615) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613) | v2_struct_0(A_613))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.99/1.84  tff(c_1530, plain, (![D_614, F_612]: (r1_tmap_1(D_614, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_614), F_612) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_612) | ~m1_subset_1(F_612, u1_struct_0(D_614)) | ~m1_subset_1(F_612, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_614, '#skF_5') | v2_struct_0(D_614) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_1528])).
% 4.99/1.84  tff(c_1533, plain, (![D_614, F_612]: (r1_tmap_1(D_614, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_614), F_612) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_612) | ~m1_subset_1(F_612, u1_struct_0(D_614)) | ~m1_subset_1(F_612, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_614, '#skF_5') | v2_struct_0(D_614) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_130, c_99, c_50, c_48, c_1530])).
% 4.99/1.84  tff(c_1574, plain, (![D_637, F_638]: (r1_tmap_1(D_637, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_637), F_638) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_638) | ~m1_subset_1(F_638, u1_struct_0(D_637)) | ~m1_subset_1(F_638, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_637, '#skF_5') | v2_struct_0(D_637))), inference(negUnitSimplification, [status(thm)], [c_70, c_54, c_1533])).
% 4.99/1.84  tff(c_1427, plain, (![D_601, C_598, E_600, A_597, B_599]: (k3_tmap_1(A_597, B_599, C_598, D_601, E_600)=k2_partfun1(u1_struct_0(C_598), u1_struct_0(B_599), E_600, u1_struct_0(D_601)) | ~m1_pre_topc(D_601, C_598) | ~m1_subset_1(E_600, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_598), u1_struct_0(B_599)))) | ~v1_funct_2(E_600, u1_struct_0(C_598), u1_struct_0(B_599)) | ~v1_funct_1(E_600) | ~m1_pre_topc(D_601, A_597) | ~m1_pre_topc(C_598, A_597) | ~l1_pre_topc(B_599) | ~v2_pre_topc(B_599) | v2_struct_0(B_599) | ~l1_pre_topc(A_597) | ~v2_pre_topc(A_597) | v2_struct_0(A_597))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.99/1.84  tff(c_1429, plain, (![A_597, D_601]: (k3_tmap_1(A_597, '#skF_2', '#skF_5', D_601, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_601)) | ~m1_pre_topc(D_601, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_601, A_597) | ~m1_pre_topc('#skF_5', A_597) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_597) | ~v2_pre_topc(A_597) | v2_struct_0(A_597))), inference(resolution, [status(thm)], [c_46, c_1427])).
% 4.99/1.84  tff(c_1432, plain, (![A_597, D_601]: (k3_tmap_1(A_597, '#skF_2', '#skF_5', D_601, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_601)) | ~m1_pre_topc(D_601, '#skF_5') | ~m1_pre_topc(D_601, A_597) | ~m1_pre_topc('#skF_5', A_597) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_597) | ~v2_pre_topc(A_597) | v2_struct_0(A_597))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_50, c_48, c_1429])).
% 4.99/1.84  tff(c_1463, plain, (![A_609, D_610]: (k3_tmap_1(A_609, '#skF_2', '#skF_5', D_610, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_610)) | ~m1_pre_topc(D_610, '#skF_5') | ~m1_pre_topc(D_610, A_609) | ~m1_pre_topc('#skF_5', A_609) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(negUnitSimplification, [status(thm)], [c_70, c_1432])).
% 4.99/1.84  tff(c_1473, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1463])).
% 4.99/1.84  tff(c_1489, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_52, c_40, c_1473])).
% 4.99/1.84  tff(c_1490, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_1489])).
% 4.99/1.84  tff(c_1326, plain, (![A_570, B_571, C_572, D_573]: (k2_partfun1(u1_struct_0(A_570), u1_struct_0(B_571), C_572, u1_struct_0(D_573))=k2_tmap_1(A_570, B_571, C_572, D_573) | ~m1_pre_topc(D_573, A_570) | ~m1_subset_1(C_572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_570), u1_struct_0(B_571)))) | ~v1_funct_2(C_572, u1_struct_0(A_570), u1_struct_0(B_571)) | ~v1_funct_1(C_572) | ~l1_pre_topc(B_571) | ~v2_pre_topc(B_571) | v2_struct_0(B_571) | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570) | v2_struct_0(A_570))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.99/1.84  tff(c_1328, plain, (![D_573]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_573))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_573) | ~m1_pre_topc(D_573, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_1326])).
% 4.99/1.84  tff(c_1331, plain, (![D_573]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_573))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_573) | ~m1_pre_topc(D_573, '#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_99, c_68, c_66, c_50, c_48, c_1328])).
% 4.99/1.84  tff(c_1332, plain, (![D_573]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_573))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_573) | ~m1_pre_topc(D_573, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_70, c_1331])).
% 4.99/1.84  tff(c_1494, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1490, c_1332])).
% 4.99/1.84  tff(c_1501, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1494])).
% 4.99/1.84  tff(c_974, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 4.99/1.84  tff(c_1506, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_974])).
% 4.99/1.84  tff(c_1579, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1574, c_1506])).
% 4.99/1.84  tff(c_1586, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82, c_36, c_975, c_1579])).
% 4.99/1.84  tff(c_1588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1586])).
% 4.99/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/1.84  
% 4.99/1.84  Inference rules
% 4.99/1.84  ----------------------
% 4.99/1.84  #Ref     : 0
% 4.99/1.84  #Sup     : 329
% 4.99/1.84  #Fact    : 0
% 4.99/1.84  #Define  : 0
% 4.99/1.84  #Split   : 12
% 4.99/1.84  #Chain   : 0
% 4.99/1.84  #Close   : 0
% 4.99/1.84  
% 4.99/1.84  Ordering : KBO
% 4.99/1.84  
% 4.99/1.84  Simplification rules
% 4.99/1.84  ----------------------
% 4.99/1.84  #Subsume      : 81
% 4.99/1.84  #Demod        : 313
% 4.99/1.84  #Tautology    : 70
% 4.99/1.84  #SimpNegUnit  : 78
% 4.99/1.84  #BackRed      : 4
% 4.99/1.84  
% 4.99/1.84  #Partial instantiations: 0
% 4.99/1.85  #Strategies tried      : 1
% 4.99/1.85  
% 4.99/1.85  Timing (in seconds)
% 4.99/1.85  ----------------------
% 4.99/1.85  Preprocessing        : 0.40
% 4.99/1.85  Parsing              : 0.20
% 4.99/1.85  CNF conversion       : 0.05
% 4.99/1.85  Main loop            : 0.64
% 4.99/1.85  Inferencing          : 0.23
% 4.99/1.85  Reduction            : 0.19
% 4.99/1.85  Demodulation         : 0.13
% 4.99/1.85  BG Simplification    : 0.03
% 4.99/1.85  Subsumption          : 0.15
% 4.99/1.85  Abstraction          : 0.02
% 4.99/1.85  MUC search           : 0.00
% 4.99/1.85  Cooper               : 0.00
% 4.99/1.85  Total                : 1.10
% 4.99/1.85  Index Insertion      : 0.00
% 4.99/1.85  Index Deletion       : 0.00
% 4.99/1.85  Index Matching       : 0.00
% 4.99/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
