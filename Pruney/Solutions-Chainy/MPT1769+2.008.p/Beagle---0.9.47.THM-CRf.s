%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:18 EST 2020

% Result     : Theorem 10.24s
% Output     : CNFRefutation 10.24s
% Verified   : 
% Statistics : Number of formulae       :  205 (8941 expanded)
%              Number of leaves         :   40 (2896 expanded)
%              Depth                    :   18
%              Number of atoms          :  709 (37739 expanded)
%              Number of equality atoms :   93 (2774 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_205,negated_conjecture,(
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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_136,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_104,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_148,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_190,plain,(
    ! [C_222,B_223,A_224] :
      ( v1_xboole_0(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(B_223,A_224)))
      | ~ v1_xboole_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_204,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_190])).

tff(c_208,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_52,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_42,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_36,plain,(
    '#skF_6' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_40,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_87,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_88,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_34,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_6'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_89,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_969,plain,(
    ! [B_370,E_367,F_368,A_365,C_366,D_369] :
      ( F_368 = E_367
      | ~ r1_funct_2(A_365,B_370,C_366,D_369,E_367,F_368)
      | ~ m1_subset_1(F_368,k1_zfmisc_1(k2_zfmisc_1(C_366,D_369)))
      | ~ v1_funct_2(F_368,C_366,D_369)
      | ~ v1_funct_1(F_368)
      | ~ m1_subset_1(E_367,k1_zfmisc_1(k2_zfmisc_1(A_365,B_370)))
      | ~ v1_funct_2(E_367,A_365,B_370)
      | ~ v1_funct_1(E_367)
      | v1_xboole_0(D_369)
      | v1_xboole_0(B_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_971,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_89,c_969])).

tff(c_974,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_42,c_87,c_88,c_971])).

tff(c_975,plain,(
    '#skF_7' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_974])).

tff(c_487,plain,(
    ! [B_280,A_275,E_277,C_276,D_279,F_278] :
      ( F_278 = E_277
      | ~ r1_funct_2(A_275,B_280,C_276,D_279,E_277,F_278)
      | ~ m1_subset_1(F_278,k1_zfmisc_1(k2_zfmisc_1(C_276,D_279)))
      | ~ v1_funct_2(F_278,C_276,D_279)
      | ~ v1_funct_1(F_278)
      | ~ m1_subset_1(E_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_280)))
      | ~ v1_funct_2(E_277,A_275,B_280)
      | ~ v1_funct_1(E_277)
      | v1_xboole_0(D_279)
      | v1_xboole_0(B_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_489,plain,
    ( '#skF_7' = '#skF_9'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_9')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_89,c_487])).

tff(c_492,plain,
    ( '#skF_7' = '#skF_9'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_42,c_87,c_88,c_489])).

tff(c_493,plain,(
    '#skF_7' = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_492])).

tff(c_82,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_84,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82])).

tff(c_267,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_496,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_267])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_56,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_85,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_56])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_758,plain,(
    ! [E_327,D_323,C_325,A_324,B_326] :
      ( k3_tmap_1(A_324,B_326,C_325,D_323,E_327) = k2_partfun1(u1_struct_0(C_325),u1_struct_0(B_326),E_327,u1_struct_0(D_323))
      | ~ m1_pre_topc(D_323,C_325)
      | ~ m1_subset_1(E_327,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_325),u1_struct_0(B_326))))
      | ~ v1_funct_2(E_327,u1_struct_0(C_325),u1_struct_0(B_326))
      | ~ v1_funct_1(E_327)
      | ~ m1_pre_topc(D_323,A_324)
      | ~ m1_pre_topc(C_325,A_324)
      | ~ l1_pre_topc(B_326)
      | ~ v2_pre_topc(B_326)
      | v2_struct_0(B_326)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_760,plain,(
    ! [A_324,D_323] :
      ( k3_tmap_1(A_324,'#skF_4','#skF_3',D_323,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_323))
      | ~ m1_pre_topc(D_323,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_323,A_324)
      | ~ m1_pre_topc('#skF_3',A_324)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(resolution,[status(thm)],[c_88,c_758])).

tff(c_768,plain,(
    ! [A_324,D_323] :
      ( k3_tmap_1(A_324,'#skF_4','#skF_3',D_323,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_323))
      | ~ m1_pre_topc(D_323,'#skF_3')
      | ~ m1_pre_topc(D_323,A_324)
      | ~ m1_pre_topc('#skF_3',A_324)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_42,c_87,c_760])).

tff(c_806,plain,(
    ! [A_331,D_332] :
      ( k3_tmap_1(A_331,'#skF_4','#skF_3',D_332,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_332))
      | ~ m1_pre_topc(D_332,'#skF_3')
      | ~ m1_pre_topc(D_332,A_331)
      | ~ m1_pre_topc('#skF_3',A_331)
      | ~ l1_pre_topc(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_768])).

tff(c_810,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_806])).

tff(c_818,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_85,c_60,c_810])).

tff(c_819,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_818])).

tff(c_710,plain,(
    ! [A_317,B_318,C_319,D_320] :
      ( k2_partfun1(u1_struct_0(A_317),u1_struct_0(B_318),C_319,u1_struct_0(D_320)) = k2_tmap_1(A_317,B_318,C_319,D_320)
      | ~ m1_pre_topc(D_320,A_317)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_317),u1_struct_0(B_318))))
      | ~ v1_funct_2(C_319,u1_struct_0(A_317),u1_struct_0(B_318))
      | ~ v1_funct_1(C_319)
      | ~ l1_pre_topc(B_318)
      | ~ v2_pre_topc(B_318)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_712,plain,(
    ! [D_320] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_320)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_320)
      | ~ m1_pre_topc(D_320,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_88,c_710])).

tff(c_720,plain,(
    ! [D_320] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_320)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_320)
      | ~ m1_pre_topc(D_320,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_42,c_87,c_712])).

tff(c_721,plain,(
    ! [D_320] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_320)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_320)
      | ~ m1_pre_topc(D_320,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_720])).

tff(c_827,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_721])).

tff(c_834,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_827])).

tff(c_76,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_86,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_76])).

tff(c_333,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_86])).

tff(c_839,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_333])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_839])).

tff(c_844,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_7','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_978,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_844])).

tff(c_1399,plain,(
    ! [B_442,D_439,E_443,A_440,C_441] :
      ( k3_tmap_1(A_440,B_442,C_441,D_439,E_443) = k2_partfun1(u1_struct_0(C_441),u1_struct_0(B_442),E_443,u1_struct_0(D_439))
      | ~ m1_pre_topc(D_439,C_441)
      | ~ m1_subset_1(E_443,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_441),u1_struct_0(B_442))))
      | ~ v1_funct_2(E_443,u1_struct_0(C_441),u1_struct_0(B_442))
      | ~ v1_funct_1(E_443)
      | ~ m1_pre_topc(D_439,A_440)
      | ~ m1_pre_topc(C_441,A_440)
      | ~ l1_pre_topc(B_442)
      | ~ v2_pre_topc(B_442)
      | v2_struct_0(B_442)
      | ~ l1_pre_topc(A_440)
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1401,plain,(
    ! [A_440,D_439] :
      ( k3_tmap_1(A_440,'#skF_4','#skF_3',D_439,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_439))
      | ~ m1_pre_topc(D_439,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_439,A_440)
      | ~ m1_pre_topc('#skF_3',A_440)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_440)
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440) ) ),
    inference(resolution,[status(thm)],[c_88,c_1399])).

tff(c_1409,plain,(
    ! [A_440,D_439] :
      ( k3_tmap_1(A_440,'#skF_4','#skF_3',D_439,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_439))
      | ~ m1_pre_topc(D_439,'#skF_3')
      | ~ m1_pre_topc(D_439,A_440)
      | ~ m1_pre_topc('#skF_3',A_440)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_440)
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_42,c_87,c_1401])).

tff(c_1416,plain,(
    ! [A_444,D_445] :
      ( k3_tmap_1(A_444,'#skF_4','#skF_3',D_445,'#skF_9') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_445))
      | ~ m1_pre_topc(D_445,'#skF_3')
      | ~ m1_pre_topc(D_445,A_444)
      | ~ m1_pre_topc('#skF_3',A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1409])).

tff(c_1420,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1416])).

tff(c_1428,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_85,c_60,c_1420])).

tff(c_1429,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1428])).

tff(c_1312,plain,(
    ! [A_422,B_423,C_424,D_425] :
      ( k2_partfun1(u1_struct_0(A_422),u1_struct_0(B_423),C_424,u1_struct_0(D_425)) = k2_tmap_1(A_422,B_423,C_424,D_425)
      | ~ m1_pre_topc(D_425,A_422)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_422),u1_struct_0(B_423))))
      | ~ v1_funct_2(C_424,u1_struct_0(A_422),u1_struct_0(B_423))
      | ~ v1_funct_1(C_424)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1314,plain,(
    ! [D_425] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_425)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_425)
      | ~ m1_pre_topc(D_425,'#skF_3')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_88,c_1312])).

tff(c_1322,plain,(
    ! [D_425] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_425)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_425)
      | ~ m1_pre_topc(D_425,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_42,c_87,c_1314])).

tff(c_1323,plain,(
    ! [D_425] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_9',u1_struct_0(D_425)) = k2_tmap_1('#skF_3','#skF_4','#skF_9',D_425)
      | ~ m1_pre_topc(D_425,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1322])).

tff(c_1437,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_1323])).

tff(c_1444,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9') = k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1437])).

tff(c_843,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1449,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tmap_1('#skF_3','#skF_4','#skF_9','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_843])).

tff(c_1451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_978,c_1449])).

tff(c_1452,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_1453,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_113,plain,(
    ! [A_207,B_208] :
      ( r2_hidden('#skF_2'(A_207,B_208),A_207)
      | r1_tarski(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [A_207,B_208] :
      ( ~ v1_xboole_0(A_207)
      | r1_tarski(A_207,B_208) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_129,plain,(
    ! [B_211,A_212] :
      ( B_211 = A_212
      | ~ r1_tarski(B_211,A_212)
      | ~ r1_tarski(A_212,B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,(
    ! [B_213,A_214] :
      ( B_213 = A_214
      | ~ r1_tarski(B_213,A_214)
      | ~ v1_xboole_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_123,c_129])).

tff(c_170,plain,(
    ! [B_208,A_207] :
      ( B_208 = A_207
      | ~ v1_xboole_0(B_208)
      | ~ v1_xboole_0(A_207) ) ),
    inference(resolution,[status(thm)],[c_123,c_152])).

tff(c_1460,plain,(
    ! [A_446] :
      ( A_446 = '#skF_7'
      | ~ v1_xboole_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_1452,c_170])).

tff(c_1467,plain,(
    u1_struct_0('#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1453,c_1460])).

tff(c_205,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_190])).

tff(c_1487,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_1467,c_205])).

tff(c_1456,plain,(
    ! [A_207] :
      ( A_207 = '#skF_7'
      | ~ v1_xboole_0(A_207) ) ),
    inference(resolution,[status(thm)],[c_1452,c_170])).

tff(c_1493,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1487,c_1456])).

tff(c_1495,plain,(
    u1_struct_0('#skF_4') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_1467])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_207,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_190])).

tff(c_1505,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_1506,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1505])).

tff(c_1509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_1506])).

tff(c_1510,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_1531,plain,(
    ! [A_450] :
      ( A_450 = '#skF_8'
      | ~ v1_xboole_0(A_450) ) ),
    inference(resolution,[status(thm)],[c_1510,c_170])).

tff(c_1540,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1487,c_1531])).

tff(c_1541,plain,(
    u1_struct_0('#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1495])).

tff(c_1542,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1493])).

tff(c_1628,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_1542,c_1541,c_1540,c_84])).

tff(c_1629,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1628])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1478,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_3'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_87])).

tff(c_1566,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1542,c_1540,c_1478])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1631,plain,(
    ! [A_453,A_454,B_455] :
      ( v1_xboole_0(A_453)
      | ~ v1_xboole_0(A_454)
      | ~ r1_tarski(A_453,k2_zfmisc_1(B_455,A_454)) ) ),
    inference(resolution,[status(thm)],[c_20,c_190])).

tff(c_1654,plain,(
    ! [B_456,A_457] :
      ( v1_xboole_0(k2_zfmisc_1(B_456,A_457))
      | ~ v1_xboole_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_16,c_1631])).

tff(c_1514,plain,(
    ! [A_207] :
      ( A_207 = '#skF_8'
      | ~ v1_xboole_0(A_207) ) ),
    inference(resolution,[status(thm)],[c_1510,c_170])).

tff(c_1666,plain,(
    ! [B_459,A_460] :
      ( k2_zfmisc_1(B_459,A_460) = '#skF_8'
      | ~ v1_xboole_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_1654,c_1514])).

tff(c_1672,plain,(
    ! [B_459] : k2_zfmisc_1(B_459,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1510,c_1666])).

tff(c_1524,plain,(
    ! [C_447,A_448,B_449] :
      ( m1_pre_topc(C_447,A_448)
      | ~ m1_pre_topc(C_447,B_449)
      | ~ m1_pre_topc(B_449,A_448)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1529,plain,(
    ! [A_448] :
      ( m1_pre_topc('#skF_5',A_448)
      | ~ m1_pre_topc('#skF_3',A_448)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448) ) ),
    inference(resolution,[status(thm)],[c_60,c_1524])).

tff(c_2176,plain,(
    ! [B_532,D_529,E_533,C_531,A_530] :
      ( k3_tmap_1(A_530,B_532,C_531,D_529,E_533) = k2_partfun1(u1_struct_0(C_531),u1_struct_0(B_532),E_533,u1_struct_0(D_529))
      | ~ m1_pre_topc(D_529,C_531)
      | ~ m1_subset_1(E_533,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_531),u1_struct_0(B_532))))
      | ~ v1_funct_2(E_533,u1_struct_0(C_531),u1_struct_0(B_532))
      | ~ v1_funct_1(E_533)
      | ~ m1_pre_topc(D_529,A_530)
      | ~ m1_pre_topc(C_531,A_530)
      | ~ l1_pre_topc(B_532)
      | ~ v2_pre_topc(B_532)
      | v2_struct_0(B_532)
      | ~ l1_pre_topc(A_530)
      | ~ v2_pre_topc(A_530)
      | v2_struct_0(A_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3905,plain,(
    ! [A_645,D_644,A_648,B_647,C_646] :
      ( k3_tmap_1(A_648,B_647,C_646,D_644,A_645) = k2_partfun1(u1_struct_0(C_646),u1_struct_0(B_647),A_645,u1_struct_0(D_644))
      | ~ m1_pre_topc(D_644,C_646)
      | ~ v1_funct_2(A_645,u1_struct_0(C_646),u1_struct_0(B_647))
      | ~ v1_funct_1(A_645)
      | ~ m1_pre_topc(D_644,A_648)
      | ~ m1_pre_topc(C_646,A_648)
      | ~ l1_pre_topc(B_647)
      | ~ v2_pre_topc(B_647)
      | v2_struct_0(B_647)
      | ~ l1_pre_topc(A_648)
      | ~ v2_pre_topc(A_648)
      | v2_struct_0(A_648)
      | ~ r1_tarski(A_645,k2_zfmisc_1(u1_struct_0(C_646),u1_struct_0(B_647))) ) ),
    inference(resolution,[status(thm)],[c_20,c_2176])).

tff(c_7340,plain,(
    ! [A_737,B_738,C_739,A_740] :
      ( k3_tmap_1(A_737,B_738,C_739,'#skF_5',A_740) = k2_partfun1(u1_struct_0(C_739),u1_struct_0(B_738),A_740,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',C_739)
      | ~ v1_funct_2(A_740,u1_struct_0(C_739),u1_struct_0(B_738))
      | ~ v1_funct_1(A_740)
      | ~ m1_pre_topc(C_739,A_737)
      | ~ l1_pre_topc(B_738)
      | ~ v2_pre_topc(B_738)
      | v2_struct_0(B_738)
      | v2_struct_0(A_737)
      | ~ r1_tarski(A_740,k2_zfmisc_1(u1_struct_0(C_739),u1_struct_0(B_738)))
      | ~ m1_pre_topc('#skF_3',A_737)
      | ~ l1_pre_topc(A_737)
      | ~ v2_pre_topc(A_737) ) ),
    inference(resolution,[status(thm)],[c_1529,c_3905])).

tff(c_7346,plain,(
    ! [B_738,A_740] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_738),A_740,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3',B_738,'#skF_3','#skF_5',A_740)
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ v1_funct_2(A_740,u1_struct_0('#skF_3'),u1_struct_0(B_738))
      | ~ v1_funct_1(A_740)
      | ~ l1_pre_topc(B_738)
      | ~ v2_pre_topc(B_738)
      | v2_struct_0(B_738)
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_740,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_738)))
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_85,c_7340])).

tff(c_7354,plain,(
    ! [B_738,A_740] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_738),A_740,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3',B_738,'#skF_3','#skF_5',A_740)
      | ~ v1_funct_2(A_740,u1_struct_0('#skF_3'),u1_struct_0(B_738))
      | ~ v1_funct_1(A_740)
      | ~ l1_pre_topc(B_738)
      | ~ v2_pre_topc(B_738)
      | v2_struct_0(B_738)
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_740,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_738))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_85,c_60,c_7346])).

tff(c_10214,plain,(
    ! [B_793,A_794] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_793),A_794,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3',B_793,'#skF_3','#skF_5',A_794)
      | ~ v1_funct_2(A_794,u1_struct_0('#skF_3'),u1_struct_0(B_793))
      | ~ v1_funct_1(A_794)
      | ~ l1_pre_topc(B_793)
      | ~ v2_pre_topc(B_793)
      | v2_struct_0(B_793)
      | ~ r1_tarski(A_794,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_793))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_7354])).

tff(c_10217,plain,(
    ! [A_794] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),A_794,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',A_794)
      | ~ v1_funct_2(A_794,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(A_794)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_794,k2_zfmisc_1(u1_struct_0('#skF_3'),'#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_10214])).

tff(c_10227,plain,(
    ! [A_794] :
      ( k2_partfun1(u1_struct_0('#skF_3'),'#skF_8',A_794,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',A_794)
      | ~ v1_funct_2(A_794,u1_struct_0('#skF_3'),'#skF_8')
      | ~ v1_funct_1(A_794)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_794,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_66,c_64,c_1541,c_1541,c_10217])).

tff(c_10254,plain,(
    ! [A_804] :
      ( k2_partfun1(u1_struct_0('#skF_3'),'#skF_8',A_804,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',A_804)
      | ~ v1_funct_2(A_804,u1_struct_0('#skF_3'),'#skF_8')
      | ~ v1_funct_1(A_804)
      | ~ r1_tarski(A_804,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_10227])).

tff(c_1844,plain,(
    ! [A_499,B_500,C_501,D_502] :
      ( k2_partfun1(u1_struct_0(A_499),u1_struct_0(B_500),C_501,u1_struct_0(D_502)) = k2_tmap_1(A_499,B_500,C_501,D_502)
      | ~ m1_pre_topc(D_502,A_499)
      | ~ m1_subset_1(C_501,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_499),u1_struct_0(B_500))))
      | ~ v1_funct_2(C_501,u1_struct_0(A_499),u1_struct_0(B_500))
      | ~ v1_funct_1(C_501)
      | ~ l1_pre_topc(B_500)
      | ~ v2_pre_topc(B_500)
      | v2_struct_0(B_500)
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3349,plain,(
    ! [A_607,B_608,A_609,D_610] :
      ( k2_partfun1(u1_struct_0(A_607),u1_struct_0(B_608),A_609,u1_struct_0(D_610)) = k2_tmap_1(A_607,B_608,A_609,D_610)
      | ~ m1_pre_topc(D_610,A_607)
      | ~ v1_funct_2(A_609,u1_struct_0(A_607),u1_struct_0(B_608))
      | ~ v1_funct_1(A_609)
      | ~ l1_pre_topc(B_608)
      | ~ v2_pre_topc(B_608)
      | v2_struct_0(B_608)
      | ~ l1_pre_topc(A_607)
      | ~ v2_pre_topc(A_607)
      | v2_struct_0(A_607)
      | ~ r1_tarski(A_609,k2_zfmisc_1(u1_struct_0(A_607),u1_struct_0(B_608))) ) ),
    inference(resolution,[status(thm)],[c_20,c_1844])).

tff(c_7643,plain,(
    ! [A_750,B_751,D_752] :
      ( k2_partfun1(u1_struct_0(A_750),u1_struct_0(B_751),k2_zfmisc_1(u1_struct_0(A_750),u1_struct_0(B_751)),u1_struct_0(D_752)) = k2_tmap_1(A_750,B_751,k2_zfmisc_1(u1_struct_0(A_750),u1_struct_0(B_751)),D_752)
      | ~ m1_pre_topc(D_752,A_750)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_750),u1_struct_0(B_751)),u1_struct_0(A_750),u1_struct_0(B_751))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_750),u1_struct_0(B_751)))
      | ~ l1_pre_topc(B_751)
      | ~ v2_pre_topc(B_751)
      | v2_struct_0(B_751)
      | ~ l1_pre_topc(A_750)
      | ~ v2_pre_topc(A_750)
      | v2_struct_0(A_750) ) ),
    inference(resolution,[status(thm)],[c_16,c_3349])).

tff(c_7662,plain,(
    ! [A_750,D_752] :
      ( k2_partfun1(u1_struct_0(A_750),'#skF_8',k2_zfmisc_1(u1_struct_0(A_750),u1_struct_0('#skF_4')),u1_struct_0(D_752)) = k2_tmap_1(A_750,'#skF_4',k2_zfmisc_1(u1_struct_0(A_750),u1_struct_0('#skF_4')),D_752)
      | ~ m1_pre_topc(D_752,A_750)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_750),u1_struct_0('#skF_4')),u1_struct_0(A_750),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_750),u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_750)
      | ~ v2_pre_topc(A_750)
      | v2_struct_0(A_750) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_7643])).

tff(c_7680,plain,(
    ! [A_750,D_752] :
      ( k2_partfun1(u1_struct_0(A_750),'#skF_8','#skF_8',u1_struct_0(D_752)) = k2_tmap_1(A_750,'#skF_4','#skF_8',D_752)
      | ~ m1_pre_topc(D_752,A_750)
      | ~ v1_funct_2('#skF_8',u1_struct_0(A_750),'#skF_8')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_750)
      | ~ v2_pre_topc(A_750)
      | v2_struct_0(A_750) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_1672,c_1541,c_1541,c_1672,c_1541,c_1672,c_1541,c_1672,c_1541,c_7662])).

tff(c_7681,plain,(
    ! [A_750,D_752] :
      ( k2_partfun1(u1_struct_0(A_750),'#skF_8','#skF_8',u1_struct_0(D_752)) = k2_tmap_1(A_750,'#skF_4','#skF_8',D_752)
      | ~ m1_pre_topc(D_752,A_750)
      | ~ v1_funct_2('#skF_8',u1_struct_0(A_750),'#skF_8')
      | ~ l1_pre_topc(A_750)
      | ~ v2_pre_topc(A_750)
      | v2_struct_0(A_750) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7680])).

tff(c_10261,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8') = k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_3'),'#skF_8')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_3'),'#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10254,c_7681])).

tff(c_10306,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8') = k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48,c_1566,c_72,c_70,c_1566,c_60,c_10261])).

tff(c_10307,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8') = k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10306])).

tff(c_1564,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8')
    | ~ r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_1540,c_1541,c_1542,c_86])).

tff(c_1565,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1564])).

tff(c_10342,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10307,c_1565])).

tff(c_10345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_10342])).

tff(c_10346,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1628])).

tff(c_10546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10346,c_1565])).

tff(c_10547,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1564])).

tff(c_10551,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8'),'#skF_8')
    | r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1542,c_1541,c_1540,c_1541,c_84])).

tff(c_10552,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10551])).

tff(c_10790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10547,c_10552])).

tff(c_10792,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_10551])).

tff(c_10549,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1542,c_1478])).

tff(c_10873,plain,(
    ! [A_885,A_886,B_887] :
      ( v1_xboole_0(A_885)
      | ~ v1_xboole_0(A_886)
      | ~ r1_tarski(A_885,k2_zfmisc_1(B_887,A_886)) ) ),
    inference(resolution,[status(thm)],[c_20,c_190])).

tff(c_10896,plain,(
    ! [B_888,A_889] :
      ( v1_xboole_0(k2_zfmisc_1(B_888,A_889))
      | ~ v1_xboole_0(A_889) ) ),
    inference(resolution,[status(thm)],[c_16,c_10873])).

tff(c_10904,plain,(
    ! [B_890,A_891] :
      ( k2_zfmisc_1(B_890,A_891) = '#skF_8'
      | ~ v1_xboole_0(A_891) ) ),
    inference(resolution,[status(thm)],[c_10896,c_1514])).

tff(c_10910,plain,(
    ! [B_890] : k2_zfmisc_1(B_890,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1510,c_10904])).

tff(c_11095,plain,(
    ! [E_931,A_928,C_929,B_930,D_927] :
      ( k3_tmap_1(A_928,B_930,C_929,D_927,E_931) = k2_partfun1(u1_struct_0(C_929),u1_struct_0(B_930),E_931,u1_struct_0(D_927))
      | ~ m1_pre_topc(D_927,C_929)
      | ~ m1_subset_1(E_931,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_929),u1_struct_0(B_930))))
      | ~ v1_funct_2(E_931,u1_struct_0(C_929),u1_struct_0(B_930))
      | ~ v1_funct_1(E_931)
      | ~ m1_pre_topc(D_927,A_928)
      | ~ m1_pre_topc(C_929,A_928)
      | ~ l1_pre_topc(B_930)
      | ~ v2_pre_topc(B_930)
      | v2_struct_0(B_930)
      | ~ l1_pre_topc(A_928)
      | ~ v2_pre_topc(A_928)
      | v2_struct_0(A_928) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12087,plain,(
    ! [D_1008,B_1006,A_1005,A_1007,C_1009] :
      ( k3_tmap_1(A_1005,B_1006,C_1009,D_1008,A_1007) = k2_partfun1(u1_struct_0(C_1009),u1_struct_0(B_1006),A_1007,u1_struct_0(D_1008))
      | ~ m1_pre_topc(D_1008,C_1009)
      | ~ v1_funct_2(A_1007,u1_struct_0(C_1009),u1_struct_0(B_1006))
      | ~ v1_funct_1(A_1007)
      | ~ m1_pre_topc(D_1008,A_1005)
      | ~ m1_pre_topc(C_1009,A_1005)
      | ~ l1_pre_topc(B_1006)
      | ~ v2_pre_topc(B_1006)
      | v2_struct_0(B_1006)
      | ~ l1_pre_topc(A_1005)
      | ~ v2_pre_topc(A_1005)
      | v2_struct_0(A_1005)
      | ~ r1_tarski(A_1007,k2_zfmisc_1(u1_struct_0(C_1009),u1_struct_0(B_1006))) ) ),
    inference(resolution,[status(thm)],[c_20,c_11095])).

tff(c_15366,plain,(
    ! [A_1136,B_1137,C_1138,A_1139] :
      ( k3_tmap_1(A_1136,B_1137,C_1138,'#skF_5',A_1139) = k2_partfun1(u1_struct_0(C_1138),u1_struct_0(B_1137),A_1139,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_5',C_1138)
      | ~ v1_funct_2(A_1139,u1_struct_0(C_1138),u1_struct_0(B_1137))
      | ~ v1_funct_1(A_1139)
      | ~ m1_pre_topc(C_1138,A_1136)
      | ~ l1_pre_topc(B_1137)
      | ~ v2_pre_topc(B_1137)
      | v2_struct_0(B_1137)
      | v2_struct_0(A_1136)
      | ~ r1_tarski(A_1139,k2_zfmisc_1(u1_struct_0(C_1138),u1_struct_0(B_1137)))
      | ~ m1_pre_topc('#skF_3',A_1136)
      | ~ l1_pre_topc(A_1136)
      | ~ v2_pre_topc(A_1136) ) ),
    inference(resolution,[status(thm)],[c_1529,c_12087])).

tff(c_15372,plain,(
    ! [B_1137,A_1139] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_1137),A_1139,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3',B_1137,'#skF_3','#skF_5',A_1139)
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ v1_funct_2(A_1139,u1_struct_0('#skF_3'),u1_struct_0(B_1137))
      | ~ v1_funct_1(A_1139)
      | ~ l1_pre_topc(B_1137)
      | ~ v2_pre_topc(B_1137)
      | v2_struct_0(B_1137)
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_1139,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1137)))
      | ~ m1_pre_topc('#skF_3','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_85,c_15366])).

tff(c_15380,plain,(
    ! [B_1137,A_1139] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_1137),A_1139,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3',B_1137,'#skF_3','#skF_5',A_1139)
      | ~ v1_funct_2(A_1139,u1_struct_0('#skF_3'),u1_struct_0(B_1137))
      | ~ v1_funct_1(A_1139)
      | ~ l1_pre_topc(B_1137)
      | ~ v2_pre_topc(B_1137)
      | v2_struct_0(B_1137)
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_1139,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1137))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_85,c_60,c_15372])).

tff(c_18480,plain,(
    ! [B_1198,A_1199] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_1198),A_1199,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3',B_1198,'#skF_3','#skF_5',A_1199)
      | ~ v1_funct_2(A_1199,u1_struct_0('#skF_3'),u1_struct_0(B_1198))
      | ~ v1_funct_1(A_1199)
      | ~ l1_pre_topc(B_1198)
      | ~ v2_pre_topc(B_1198)
      | v2_struct_0(B_1198)
      | ~ r1_tarski(A_1199,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1198))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_15380])).

tff(c_18483,plain,(
    ! [A_1199] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),A_1199,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',A_1199)
      | ~ v1_funct_2(A_1199,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(A_1199)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_1199,k2_zfmisc_1(u1_struct_0('#skF_3'),'#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_18480])).

tff(c_18493,plain,(
    ! [A_1199] :
      ( k2_partfun1(u1_struct_0('#skF_3'),'#skF_8',A_1199,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',A_1199)
      | ~ v1_funct_2(A_1199,u1_struct_0('#skF_3'),'#skF_8')
      | ~ v1_funct_1(A_1199)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_1199,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10910,c_66,c_64,c_1541,c_1541,c_18483])).

tff(c_19409,plain,(
    ! [A_1216] :
      ( k2_partfun1(u1_struct_0('#skF_3'),'#skF_8',A_1216,u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5',A_1216)
      | ~ v1_funct_2(A_1216,u1_struct_0('#skF_3'),'#skF_8')
      | ~ v1_funct_1(A_1216)
      | ~ r1_tarski(A_1216,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_18493])).

tff(c_11028,plain,(
    ! [A_911,B_912,C_913,D_914] :
      ( k2_partfun1(u1_struct_0(A_911),u1_struct_0(B_912),C_913,u1_struct_0(D_914)) = k2_tmap_1(A_911,B_912,C_913,D_914)
      | ~ m1_pre_topc(D_914,A_911)
      | ~ m1_subset_1(C_913,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_911),u1_struct_0(B_912))))
      | ~ v1_funct_2(C_913,u1_struct_0(A_911),u1_struct_0(B_912))
      | ~ v1_funct_1(C_913)
      | ~ l1_pre_topc(B_912)
      | ~ v2_pre_topc(B_912)
      | v2_struct_0(B_912)
      | ~ l1_pre_topc(A_911)
      | ~ v2_pre_topc(A_911)
      | v2_struct_0(A_911) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_11470,plain,(
    ! [A_976,B_977,A_978,D_979] :
      ( k2_partfun1(u1_struct_0(A_976),u1_struct_0(B_977),A_978,u1_struct_0(D_979)) = k2_tmap_1(A_976,B_977,A_978,D_979)
      | ~ m1_pre_topc(D_979,A_976)
      | ~ v1_funct_2(A_978,u1_struct_0(A_976),u1_struct_0(B_977))
      | ~ v1_funct_1(A_978)
      | ~ l1_pre_topc(B_977)
      | ~ v2_pre_topc(B_977)
      | v2_struct_0(B_977)
      | ~ l1_pre_topc(A_976)
      | ~ v2_pre_topc(A_976)
      | v2_struct_0(A_976)
      | ~ r1_tarski(A_978,k2_zfmisc_1(u1_struct_0(A_976),u1_struct_0(B_977))) ) ),
    inference(resolution,[status(thm)],[c_20,c_11028])).

tff(c_15727,plain,(
    ! [A_1155,B_1156,D_1157] :
      ( k2_partfun1(u1_struct_0(A_1155),u1_struct_0(B_1156),k2_zfmisc_1(u1_struct_0(A_1155),u1_struct_0(B_1156)),u1_struct_0(D_1157)) = k2_tmap_1(A_1155,B_1156,k2_zfmisc_1(u1_struct_0(A_1155),u1_struct_0(B_1156)),D_1157)
      | ~ m1_pre_topc(D_1157,A_1155)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1155),u1_struct_0(B_1156)),u1_struct_0(A_1155),u1_struct_0(B_1156))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1155),u1_struct_0(B_1156)))
      | ~ l1_pre_topc(B_1156)
      | ~ v2_pre_topc(B_1156)
      | v2_struct_0(B_1156)
      | ~ l1_pre_topc(A_1155)
      | ~ v2_pre_topc(A_1155)
      | v2_struct_0(A_1155) ) ),
    inference(resolution,[status(thm)],[c_16,c_11470])).

tff(c_15746,plain,(
    ! [A_1155,D_1157] :
      ( k2_partfun1(u1_struct_0(A_1155),'#skF_8',k2_zfmisc_1(u1_struct_0(A_1155),u1_struct_0('#skF_4')),u1_struct_0(D_1157)) = k2_tmap_1(A_1155,'#skF_4',k2_zfmisc_1(u1_struct_0(A_1155),u1_struct_0('#skF_4')),D_1157)
      | ~ m1_pre_topc(D_1157,A_1155)
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1155),u1_struct_0('#skF_4')),u1_struct_0(A_1155),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1155),u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1155)
      | ~ v2_pre_topc(A_1155)
      | v2_struct_0(A_1155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1541,c_15727])).

tff(c_15764,plain,(
    ! [A_1155,D_1157] :
      ( k2_partfun1(u1_struct_0(A_1155),'#skF_8','#skF_8',u1_struct_0(D_1157)) = k2_tmap_1(A_1155,'#skF_4','#skF_8',D_1157)
      | ~ m1_pre_topc(D_1157,A_1155)
      | ~ v1_funct_2('#skF_8',u1_struct_0(A_1155),'#skF_8')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1155)
      | ~ v2_pre_topc(A_1155)
      | v2_struct_0(A_1155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_10910,c_1541,c_1541,c_10910,c_1541,c_10910,c_1541,c_10910,c_1541,c_15746])).

tff(c_15765,plain,(
    ! [A_1155,D_1157] :
      ( k2_partfun1(u1_struct_0(A_1155),'#skF_8','#skF_8',u1_struct_0(D_1157)) = k2_tmap_1(A_1155,'#skF_4','#skF_8',D_1157)
      | ~ m1_pre_topc(D_1157,A_1155)
      | ~ v1_funct_2('#skF_8',u1_struct_0(A_1155),'#skF_8')
      | ~ l1_pre_topc(A_1155)
      | ~ v2_pre_topc(A_1155)
      | v2_struct_0(A_1155) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_15764])).

tff(c_19416,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8') = k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_3'),'#skF_8')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_3'),'#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_19409,c_15765])).

tff(c_19454,plain,
    ( k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8') = k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48,c_10549,c_72,c_70,c_10549,c_60,c_19416])).

tff(c_19455,plain,(
    k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8') = k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_19454])).

tff(c_10548,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k3_tmap_1('#skF_3','#skF_4','#skF_3','#skF_5','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1564])).

tff(c_19484,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),'#skF_8',k2_tmap_1('#skF_3','#skF_4','#skF_8','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19455,c_10548])).

tff(c_19486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10792,c_19484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.24/3.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.24/3.66  
% 10.24/3.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.24/3.66  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 10.24/3.66  
% 10.24/3.66  %Foreground sorts:
% 10.24/3.66  
% 10.24/3.66  
% 10.24/3.66  %Background operators:
% 10.24/3.66  
% 10.24/3.66  
% 10.24/3.66  %Foreground operators:
% 10.24/3.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.24/3.66  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 10.24/3.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.24/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.24/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.24/3.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.24/3.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.24/3.66  tff('#skF_7', type, '#skF_7': $i).
% 10.24/3.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.24/3.66  tff('#skF_5', type, '#skF_5': $i).
% 10.24/3.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.24/3.66  tff('#skF_6', type, '#skF_6': $i).
% 10.24/3.66  tff('#skF_3', type, '#skF_3': $i).
% 10.24/3.66  tff('#skF_9', type, '#skF_9': $i).
% 10.24/3.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.24/3.66  tff('#skF_8', type, '#skF_8': $i).
% 10.24/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.24/3.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.24/3.66  tff('#skF_4', type, '#skF_4': $i).
% 10.24/3.66  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 10.24/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.24/3.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.24/3.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.24/3.66  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.24/3.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.24/3.66  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 10.24/3.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.24/3.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.24/3.66  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 10.24/3.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.24/3.66  
% 10.24/3.69  tff(f_205, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 10.24/3.69  tff(f_55, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 10.24/3.69  tff(f_77, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 10.24/3.69  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 10.24/3.69  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 10.24/3.69  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.24/3.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.24/3.69  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.24/3.69  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.24/3.69  tff(f_148, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 10.24/3.69  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_190, plain, (![C_222, B_223, A_224]: (v1_xboole_0(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(B_223, A_224))) | ~v1_xboole_0(A_224))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.24/3.69  tff(c_204, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_190])).
% 10.24/3.69  tff(c_208, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_204])).
% 10.24/3.69  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_52, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_42, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_36, plain, ('#skF_6'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_40, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_87, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 10.24/3.69  tff(c_38, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_88, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 10.24/3.69  tff(c_34, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_6'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_89, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 10.24/3.69  tff(c_969, plain, (![B_370, E_367, F_368, A_365, C_366, D_369]: (F_368=E_367 | ~r1_funct_2(A_365, B_370, C_366, D_369, E_367, F_368) | ~m1_subset_1(F_368, k1_zfmisc_1(k2_zfmisc_1(C_366, D_369))) | ~v1_funct_2(F_368, C_366, D_369) | ~v1_funct_1(F_368) | ~m1_subset_1(E_367, k1_zfmisc_1(k2_zfmisc_1(A_365, B_370))) | ~v1_funct_2(E_367, A_365, B_370) | ~v1_funct_1(E_367) | v1_xboole_0(D_369) | v1_xboole_0(B_370))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.24/3.69  tff(c_971, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_89, c_969])).
% 10.24/3.69  tff(c_974, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_42, c_87, c_88, c_971])).
% 10.24/3.69  tff(c_975, plain, ('#skF_7'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_208, c_974])).
% 10.24/3.69  tff(c_487, plain, (![B_280, A_275, E_277, C_276, D_279, F_278]: (F_278=E_277 | ~r1_funct_2(A_275, B_280, C_276, D_279, E_277, F_278) | ~m1_subset_1(F_278, k1_zfmisc_1(k2_zfmisc_1(C_276, D_279))) | ~v1_funct_2(F_278, C_276, D_279) | ~v1_funct_1(F_278) | ~m1_subset_1(E_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_280))) | ~v1_funct_2(E_277, A_275, B_280) | ~v1_funct_1(E_277) | v1_xboole_0(D_279) | v1_xboole_0(B_280))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.24/3.69  tff(c_489, plain, ('#skF_7'='#skF_9' | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_89, c_487])).
% 10.24/3.69  tff(c_492, plain, ('#skF_7'='#skF_9' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_42, c_87, c_88, c_489])).
% 10.24/3.69  tff(c_493, plain, ('#skF_7'='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_208, c_492])).
% 10.24/3.69  tff(c_82, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_84, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82])).
% 10.24/3.69  tff(c_267, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 10.24/3.69  tff(c_496, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_267])).
% 10.24/3.69  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_56, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_85, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_56])).
% 10.24/3.69  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_758, plain, (![E_327, D_323, C_325, A_324, B_326]: (k3_tmap_1(A_324, B_326, C_325, D_323, E_327)=k2_partfun1(u1_struct_0(C_325), u1_struct_0(B_326), E_327, u1_struct_0(D_323)) | ~m1_pre_topc(D_323, C_325) | ~m1_subset_1(E_327, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_325), u1_struct_0(B_326)))) | ~v1_funct_2(E_327, u1_struct_0(C_325), u1_struct_0(B_326)) | ~v1_funct_1(E_327) | ~m1_pre_topc(D_323, A_324) | ~m1_pre_topc(C_325, A_324) | ~l1_pre_topc(B_326) | ~v2_pre_topc(B_326) | v2_struct_0(B_326) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.24/3.69  tff(c_760, plain, (![A_324, D_323]: (k3_tmap_1(A_324, '#skF_4', '#skF_3', D_323, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_323)) | ~m1_pre_topc(D_323, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_323, A_324) | ~m1_pre_topc('#skF_3', A_324) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(resolution, [status(thm)], [c_88, c_758])).
% 10.24/3.69  tff(c_768, plain, (![A_324, D_323]: (k3_tmap_1(A_324, '#skF_4', '#skF_3', D_323, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_323)) | ~m1_pre_topc(D_323, '#skF_3') | ~m1_pre_topc(D_323, A_324) | ~m1_pre_topc('#skF_3', A_324) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_42, c_87, c_760])).
% 10.24/3.69  tff(c_806, plain, (![A_331, D_332]: (k3_tmap_1(A_331, '#skF_4', '#skF_3', D_332, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_332)) | ~m1_pre_topc(D_332, '#skF_3') | ~m1_pre_topc(D_332, A_331) | ~m1_pre_topc('#skF_3', A_331) | ~l1_pre_topc(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331))), inference(negUnitSimplification, [status(thm)], [c_68, c_768])).
% 10.24/3.69  tff(c_810, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_806])).
% 10.24/3.69  tff(c_818, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_85, c_60, c_810])).
% 10.24/3.69  tff(c_819, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_74, c_818])).
% 10.24/3.69  tff(c_710, plain, (![A_317, B_318, C_319, D_320]: (k2_partfun1(u1_struct_0(A_317), u1_struct_0(B_318), C_319, u1_struct_0(D_320))=k2_tmap_1(A_317, B_318, C_319, D_320) | ~m1_pre_topc(D_320, A_317) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_317), u1_struct_0(B_318)))) | ~v1_funct_2(C_319, u1_struct_0(A_317), u1_struct_0(B_318)) | ~v1_funct_1(C_319) | ~l1_pre_topc(B_318) | ~v2_pre_topc(B_318) | v2_struct_0(B_318) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317) | v2_struct_0(A_317))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.24/3.69  tff(c_712, plain, (![D_320]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_320))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_320) | ~m1_pre_topc(D_320, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_88, c_710])).
% 10.24/3.69  tff(c_720, plain, (![D_320]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_320))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_320) | ~m1_pre_topc(D_320, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_42, c_87, c_712])).
% 10.24/3.69  tff(c_721, plain, (![D_320]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_320))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_320) | ~m1_pre_topc(D_320, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_720])).
% 10.24/3.69  tff(c_827, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_819, c_721])).
% 10.24/3.69  tff(c_834, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_827])).
% 10.24/3.69  tff(c_76, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_86, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_76])).
% 10.24/3.69  tff(c_333, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_86])).
% 10.24/3.69  tff(c_839, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_834, c_333])).
% 10.24/3.69  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_496, c_839])).
% 10.24/3.69  tff(c_844, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_7', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 10.24/3.69  tff(c_978, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_975, c_844])).
% 10.24/3.69  tff(c_1399, plain, (![B_442, D_439, E_443, A_440, C_441]: (k3_tmap_1(A_440, B_442, C_441, D_439, E_443)=k2_partfun1(u1_struct_0(C_441), u1_struct_0(B_442), E_443, u1_struct_0(D_439)) | ~m1_pre_topc(D_439, C_441) | ~m1_subset_1(E_443, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_441), u1_struct_0(B_442)))) | ~v1_funct_2(E_443, u1_struct_0(C_441), u1_struct_0(B_442)) | ~v1_funct_1(E_443) | ~m1_pre_topc(D_439, A_440) | ~m1_pre_topc(C_441, A_440) | ~l1_pre_topc(B_442) | ~v2_pre_topc(B_442) | v2_struct_0(B_442) | ~l1_pre_topc(A_440) | ~v2_pre_topc(A_440) | v2_struct_0(A_440))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.24/3.69  tff(c_1401, plain, (![A_440, D_439]: (k3_tmap_1(A_440, '#skF_4', '#skF_3', D_439, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_439)) | ~m1_pre_topc(D_439, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_439, A_440) | ~m1_pre_topc('#skF_3', A_440) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_440) | ~v2_pre_topc(A_440) | v2_struct_0(A_440))), inference(resolution, [status(thm)], [c_88, c_1399])).
% 10.24/3.69  tff(c_1409, plain, (![A_440, D_439]: (k3_tmap_1(A_440, '#skF_4', '#skF_3', D_439, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_439)) | ~m1_pre_topc(D_439, '#skF_3') | ~m1_pre_topc(D_439, A_440) | ~m1_pre_topc('#skF_3', A_440) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_440) | ~v2_pre_topc(A_440) | v2_struct_0(A_440))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_42, c_87, c_1401])).
% 10.24/3.69  tff(c_1416, plain, (![A_444, D_445]: (k3_tmap_1(A_444, '#skF_4', '#skF_3', D_445, '#skF_9')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_445)) | ~m1_pre_topc(D_445, '#skF_3') | ~m1_pre_topc(D_445, A_444) | ~m1_pre_topc('#skF_3', A_444) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(negUnitSimplification, [status(thm)], [c_68, c_1409])).
% 10.24/3.69  tff(c_1420, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1416])).
% 10.24/3.69  tff(c_1428, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_85, c_60, c_1420])).
% 10.24/3.69  tff(c_1429, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_74, c_1428])).
% 10.24/3.69  tff(c_1312, plain, (![A_422, B_423, C_424, D_425]: (k2_partfun1(u1_struct_0(A_422), u1_struct_0(B_423), C_424, u1_struct_0(D_425))=k2_tmap_1(A_422, B_423, C_424, D_425) | ~m1_pre_topc(D_425, A_422) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_422), u1_struct_0(B_423)))) | ~v1_funct_2(C_424, u1_struct_0(A_422), u1_struct_0(B_423)) | ~v1_funct_1(C_424) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.24/3.69  tff(c_1314, plain, (![D_425]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_425))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_425) | ~m1_pre_topc(D_425, '#skF_3') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_88, c_1312])).
% 10.24/3.69  tff(c_1322, plain, (![D_425]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_425))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_425) | ~m1_pre_topc(D_425, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_42, c_87, c_1314])).
% 10.24/3.69  tff(c_1323, plain, (![D_425]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_9', u1_struct_0(D_425))=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', D_425) | ~m1_pre_topc(D_425, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_1322])).
% 10.24/3.69  tff(c_1437, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1429, c_1323])).
% 10.24/3.69  tff(c_1444, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9')=k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1437])).
% 10.24/3.69  tff(c_843, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 10.24/3.69  tff(c_1449, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tmap_1('#skF_3', '#skF_4', '#skF_9', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_843])).
% 10.24/3.69  tff(c_1451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_978, c_1449])).
% 10.24/3.69  tff(c_1452, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_204])).
% 10.24/3.69  tff(c_1453, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_204])).
% 10.24/3.69  tff(c_113, plain, (![A_207, B_208]: (r2_hidden('#skF_2'(A_207, B_208), A_207) | r1_tarski(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.24/3.69  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.24/3.69  tff(c_123, plain, (![A_207, B_208]: (~v1_xboole_0(A_207) | r1_tarski(A_207, B_208))), inference(resolution, [status(thm)], [c_113, c_2])).
% 10.24/3.69  tff(c_129, plain, (![B_211, A_212]: (B_211=A_212 | ~r1_tarski(B_211, A_212) | ~r1_tarski(A_212, B_211))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.24/3.69  tff(c_152, plain, (![B_213, A_214]: (B_213=A_214 | ~r1_tarski(B_213, A_214) | ~v1_xboole_0(A_214))), inference(resolution, [status(thm)], [c_123, c_129])).
% 10.24/3.69  tff(c_170, plain, (![B_208, A_207]: (B_208=A_207 | ~v1_xboole_0(B_208) | ~v1_xboole_0(A_207))), inference(resolution, [status(thm)], [c_123, c_152])).
% 10.24/3.69  tff(c_1460, plain, (![A_446]: (A_446='#skF_7' | ~v1_xboole_0(A_446))), inference(resolution, [status(thm)], [c_1452, c_170])).
% 10.24/3.69  tff(c_1467, plain, (u1_struct_0('#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_1453, c_1460])).
% 10.24/3.69  tff(c_205, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_88, c_190])).
% 10.24/3.69  tff(c_1487, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_1467, c_205])).
% 10.24/3.69  tff(c_1456, plain, (![A_207]: (A_207='#skF_7' | ~v1_xboole_0(A_207))), inference(resolution, [status(thm)], [c_1452, c_170])).
% 10.24/3.69  tff(c_1493, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_1487, c_1456])).
% 10.24/3.69  tff(c_1495, plain, (u1_struct_0('#skF_4')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1493, c_1467])).
% 10.24/3.69  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_207, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_190])).
% 10.24/3.69  tff(c_1505, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_207])).
% 10.24/3.69  tff(c_1506, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1505])).
% 10.24/3.69  tff(c_1509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1487, c_1506])).
% 10.24/3.69  tff(c_1510, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_207])).
% 10.24/3.69  tff(c_1531, plain, (![A_450]: (A_450='#skF_8' | ~v1_xboole_0(A_450))), inference(resolution, [status(thm)], [c_1510, c_170])).
% 10.24/3.69  tff(c_1540, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_1487, c_1531])).
% 10.24/3.69  tff(c_1541, plain, (u1_struct_0('#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1495])).
% 10.24/3.69  tff(c_1542, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1493])).
% 10.24/3.69  tff(c_1628, plain, (r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_1542, c_1541, c_1540, c_84])).
% 10.24/3.69  tff(c_1629, plain, (r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1628])).
% 10.24/3.69  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.24/3.69  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.24/3.69  tff(c_1478, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_3'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_87])).
% 10.24/3.69  tff(c_1566, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1542, c_1540, c_1478])).
% 10.24/3.69  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.24/3.69  tff(c_1631, plain, (![A_453, A_454, B_455]: (v1_xboole_0(A_453) | ~v1_xboole_0(A_454) | ~r1_tarski(A_453, k2_zfmisc_1(B_455, A_454)))), inference(resolution, [status(thm)], [c_20, c_190])).
% 10.24/3.69  tff(c_1654, plain, (![B_456, A_457]: (v1_xboole_0(k2_zfmisc_1(B_456, A_457)) | ~v1_xboole_0(A_457))), inference(resolution, [status(thm)], [c_16, c_1631])).
% 10.24/3.69  tff(c_1514, plain, (![A_207]: (A_207='#skF_8' | ~v1_xboole_0(A_207))), inference(resolution, [status(thm)], [c_1510, c_170])).
% 10.24/3.69  tff(c_1666, plain, (![B_459, A_460]: (k2_zfmisc_1(B_459, A_460)='#skF_8' | ~v1_xboole_0(A_460))), inference(resolution, [status(thm)], [c_1654, c_1514])).
% 10.24/3.69  tff(c_1672, plain, (![B_459]: (k2_zfmisc_1(B_459, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_1510, c_1666])).
% 10.24/3.69  tff(c_1524, plain, (![C_447, A_448, B_449]: (m1_pre_topc(C_447, A_448) | ~m1_pre_topc(C_447, B_449) | ~m1_pre_topc(B_449, A_448) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.24/3.69  tff(c_1529, plain, (![A_448]: (m1_pre_topc('#skF_5', A_448) | ~m1_pre_topc('#skF_3', A_448) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448))), inference(resolution, [status(thm)], [c_60, c_1524])).
% 10.24/3.69  tff(c_2176, plain, (![B_532, D_529, E_533, C_531, A_530]: (k3_tmap_1(A_530, B_532, C_531, D_529, E_533)=k2_partfun1(u1_struct_0(C_531), u1_struct_0(B_532), E_533, u1_struct_0(D_529)) | ~m1_pre_topc(D_529, C_531) | ~m1_subset_1(E_533, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_531), u1_struct_0(B_532)))) | ~v1_funct_2(E_533, u1_struct_0(C_531), u1_struct_0(B_532)) | ~v1_funct_1(E_533) | ~m1_pre_topc(D_529, A_530) | ~m1_pre_topc(C_531, A_530) | ~l1_pre_topc(B_532) | ~v2_pre_topc(B_532) | v2_struct_0(B_532) | ~l1_pre_topc(A_530) | ~v2_pre_topc(A_530) | v2_struct_0(A_530))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.24/3.69  tff(c_3905, plain, (![A_645, D_644, A_648, B_647, C_646]: (k3_tmap_1(A_648, B_647, C_646, D_644, A_645)=k2_partfun1(u1_struct_0(C_646), u1_struct_0(B_647), A_645, u1_struct_0(D_644)) | ~m1_pre_topc(D_644, C_646) | ~v1_funct_2(A_645, u1_struct_0(C_646), u1_struct_0(B_647)) | ~v1_funct_1(A_645) | ~m1_pre_topc(D_644, A_648) | ~m1_pre_topc(C_646, A_648) | ~l1_pre_topc(B_647) | ~v2_pre_topc(B_647) | v2_struct_0(B_647) | ~l1_pre_topc(A_648) | ~v2_pre_topc(A_648) | v2_struct_0(A_648) | ~r1_tarski(A_645, k2_zfmisc_1(u1_struct_0(C_646), u1_struct_0(B_647))))), inference(resolution, [status(thm)], [c_20, c_2176])).
% 10.24/3.69  tff(c_7340, plain, (![A_737, B_738, C_739, A_740]: (k3_tmap_1(A_737, B_738, C_739, '#skF_5', A_740)=k2_partfun1(u1_struct_0(C_739), u1_struct_0(B_738), A_740, u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', C_739) | ~v1_funct_2(A_740, u1_struct_0(C_739), u1_struct_0(B_738)) | ~v1_funct_1(A_740) | ~m1_pre_topc(C_739, A_737) | ~l1_pre_topc(B_738) | ~v2_pre_topc(B_738) | v2_struct_0(B_738) | v2_struct_0(A_737) | ~r1_tarski(A_740, k2_zfmisc_1(u1_struct_0(C_739), u1_struct_0(B_738))) | ~m1_pre_topc('#skF_3', A_737) | ~l1_pre_topc(A_737) | ~v2_pre_topc(A_737))), inference(resolution, [status(thm)], [c_1529, c_3905])).
% 10.24/3.69  tff(c_7346, plain, (![B_738, A_740]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_738), A_740, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', B_738, '#skF_3', '#skF_5', A_740) | ~m1_pre_topc('#skF_5', '#skF_3') | ~v1_funct_2(A_740, u1_struct_0('#skF_3'), u1_struct_0(B_738)) | ~v1_funct_1(A_740) | ~l1_pre_topc(B_738) | ~v2_pre_topc(B_738) | v2_struct_0(B_738) | v2_struct_0('#skF_3') | ~r1_tarski(A_740, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_738))) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_85, c_7340])).
% 10.24/3.69  tff(c_7354, plain, (![B_738, A_740]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_738), A_740, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', B_738, '#skF_3', '#skF_5', A_740) | ~v1_funct_2(A_740, u1_struct_0('#skF_3'), u1_struct_0(B_738)) | ~v1_funct_1(A_740) | ~l1_pre_topc(B_738) | ~v2_pre_topc(B_738) | v2_struct_0(B_738) | v2_struct_0('#skF_3') | ~r1_tarski(A_740, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_738))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_85, c_60, c_7346])).
% 10.24/3.69  tff(c_10214, plain, (![B_793, A_794]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_793), A_794, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', B_793, '#skF_3', '#skF_5', A_794) | ~v1_funct_2(A_794, u1_struct_0('#skF_3'), u1_struct_0(B_793)) | ~v1_funct_1(A_794) | ~l1_pre_topc(B_793) | ~v2_pre_topc(B_793) | v2_struct_0(B_793) | ~r1_tarski(A_794, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_793))))), inference(negUnitSimplification, [status(thm)], [c_74, c_7354])).
% 10.24/3.69  tff(c_10217, plain, (![A_794]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), A_794, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', A_794) | ~v1_funct_2(A_794, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(A_794) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_794, k2_zfmisc_1(u1_struct_0('#skF_3'), '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1541, c_10214])).
% 10.24/3.69  tff(c_10227, plain, (![A_794]: (k2_partfun1(u1_struct_0('#skF_3'), '#skF_8', A_794, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', A_794) | ~v1_funct_2(A_794, u1_struct_0('#skF_3'), '#skF_8') | ~v1_funct_1(A_794) | v2_struct_0('#skF_4') | ~r1_tarski(A_794, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_66, c_64, c_1541, c_1541, c_10217])).
% 10.24/3.69  tff(c_10254, plain, (![A_804]: (k2_partfun1(u1_struct_0('#skF_3'), '#skF_8', A_804, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', A_804) | ~v1_funct_2(A_804, u1_struct_0('#skF_3'), '#skF_8') | ~v1_funct_1(A_804) | ~r1_tarski(A_804, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_68, c_10227])).
% 10.24/3.69  tff(c_1844, plain, (![A_499, B_500, C_501, D_502]: (k2_partfun1(u1_struct_0(A_499), u1_struct_0(B_500), C_501, u1_struct_0(D_502))=k2_tmap_1(A_499, B_500, C_501, D_502) | ~m1_pre_topc(D_502, A_499) | ~m1_subset_1(C_501, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_499), u1_struct_0(B_500)))) | ~v1_funct_2(C_501, u1_struct_0(A_499), u1_struct_0(B_500)) | ~v1_funct_1(C_501) | ~l1_pre_topc(B_500) | ~v2_pre_topc(B_500) | v2_struct_0(B_500) | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.24/3.69  tff(c_3349, plain, (![A_607, B_608, A_609, D_610]: (k2_partfun1(u1_struct_0(A_607), u1_struct_0(B_608), A_609, u1_struct_0(D_610))=k2_tmap_1(A_607, B_608, A_609, D_610) | ~m1_pre_topc(D_610, A_607) | ~v1_funct_2(A_609, u1_struct_0(A_607), u1_struct_0(B_608)) | ~v1_funct_1(A_609) | ~l1_pre_topc(B_608) | ~v2_pre_topc(B_608) | v2_struct_0(B_608) | ~l1_pre_topc(A_607) | ~v2_pre_topc(A_607) | v2_struct_0(A_607) | ~r1_tarski(A_609, k2_zfmisc_1(u1_struct_0(A_607), u1_struct_0(B_608))))), inference(resolution, [status(thm)], [c_20, c_1844])).
% 10.24/3.69  tff(c_7643, plain, (![A_750, B_751, D_752]: (k2_partfun1(u1_struct_0(A_750), u1_struct_0(B_751), k2_zfmisc_1(u1_struct_0(A_750), u1_struct_0(B_751)), u1_struct_0(D_752))=k2_tmap_1(A_750, B_751, k2_zfmisc_1(u1_struct_0(A_750), u1_struct_0(B_751)), D_752) | ~m1_pre_topc(D_752, A_750) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_750), u1_struct_0(B_751)), u1_struct_0(A_750), u1_struct_0(B_751)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_750), u1_struct_0(B_751))) | ~l1_pre_topc(B_751) | ~v2_pre_topc(B_751) | v2_struct_0(B_751) | ~l1_pre_topc(A_750) | ~v2_pre_topc(A_750) | v2_struct_0(A_750))), inference(resolution, [status(thm)], [c_16, c_3349])).
% 10.24/3.69  tff(c_7662, plain, (![A_750, D_752]: (k2_partfun1(u1_struct_0(A_750), '#skF_8', k2_zfmisc_1(u1_struct_0(A_750), u1_struct_0('#skF_4')), u1_struct_0(D_752))=k2_tmap_1(A_750, '#skF_4', k2_zfmisc_1(u1_struct_0(A_750), u1_struct_0('#skF_4')), D_752) | ~m1_pre_topc(D_752, A_750) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_750), u1_struct_0('#skF_4')), u1_struct_0(A_750), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_750), u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_750) | ~v2_pre_topc(A_750) | v2_struct_0(A_750))), inference(superposition, [status(thm), theory('equality')], [c_1541, c_7643])).
% 10.24/3.69  tff(c_7680, plain, (![A_750, D_752]: (k2_partfun1(u1_struct_0(A_750), '#skF_8', '#skF_8', u1_struct_0(D_752))=k2_tmap_1(A_750, '#skF_4', '#skF_8', D_752) | ~m1_pre_topc(D_752, A_750) | ~v1_funct_2('#skF_8', u1_struct_0(A_750), '#skF_8') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_750) | ~v2_pre_topc(A_750) | v2_struct_0(A_750))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_1672, c_1541, c_1541, c_1672, c_1541, c_1672, c_1541, c_1672, c_1541, c_7662])).
% 10.24/3.69  tff(c_7681, plain, (![A_750, D_752]: (k2_partfun1(u1_struct_0(A_750), '#skF_8', '#skF_8', u1_struct_0(D_752))=k2_tmap_1(A_750, '#skF_4', '#skF_8', D_752) | ~m1_pre_topc(D_752, A_750) | ~v1_funct_2('#skF_8', u1_struct_0(A_750), '#skF_8') | ~l1_pre_topc(A_750) | ~v2_pre_topc(A_750) | v2_struct_0(A_750))), inference(negUnitSimplification, [status(thm)], [c_68, c_7680])).
% 10.24/3.69  tff(c_10261, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8')=k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_3'), '#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_3'), '#skF_8') | ~v1_funct_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10254, c_7681])).
% 10.24/3.69  tff(c_10306, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8')=k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48, c_1566, c_72, c_70, c_1566, c_60, c_10261])).
% 10.24/3.69  tff(c_10307, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8')=k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_10306])).
% 10.24/3.69  tff(c_1564, plain, (~r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8') | ~r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_1540, c_1541, c_1542, c_86])).
% 10.24/3.69  tff(c_1565, plain, (~r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1564])).
% 10.24/3.69  tff(c_10342, plain, (~r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10307, c_1565])).
% 10.24/3.69  tff(c_10345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1629, c_10342])).
% 10.24/3.69  tff(c_10346, plain, (r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_1628])).
% 10.24/3.69  tff(c_10546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10346, c_1565])).
% 10.24/3.69  tff(c_10547, plain, (~r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_1564])).
% 10.24/3.69  tff(c_10551, plain, (r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8'), '#skF_8') | r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1542, c_1541, c_1540, c_1541, c_84])).
% 10.24/3.69  tff(c_10552, plain, (r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_10551])).
% 10.24/3.69  tff(c_10790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10547, c_10552])).
% 10.24/3.69  tff(c_10792, plain, (~r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_10551])).
% 10.24/3.69  tff(c_10549, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1542, c_1478])).
% 10.24/3.69  tff(c_10873, plain, (![A_885, A_886, B_887]: (v1_xboole_0(A_885) | ~v1_xboole_0(A_886) | ~r1_tarski(A_885, k2_zfmisc_1(B_887, A_886)))), inference(resolution, [status(thm)], [c_20, c_190])).
% 10.24/3.69  tff(c_10896, plain, (![B_888, A_889]: (v1_xboole_0(k2_zfmisc_1(B_888, A_889)) | ~v1_xboole_0(A_889))), inference(resolution, [status(thm)], [c_16, c_10873])).
% 10.24/3.69  tff(c_10904, plain, (![B_890, A_891]: (k2_zfmisc_1(B_890, A_891)='#skF_8' | ~v1_xboole_0(A_891))), inference(resolution, [status(thm)], [c_10896, c_1514])).
% 10.24/3.69  tff(c_10910, plain, (![B_890]: (k2_zfmisc_1(B_890, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_1510, c_10904])).
% 10.24/3.69  tff(c_11095, plain, (![E_931, A_928, C_929, B_930, D_927]: (k3_tmap_1(A_928, B_930, C_929, D_927, E_931)=k2_partfun1(u1_struct_0(C_929), u1_struct_0(B_930), E_931, u1_struct_0(D_927)) | ~m1_pre_topc(D_927, C_929) | ~m1_subset_1(E_931, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_929), u1_struct_0(B_930)))) | ~v1_funct_2(E_931, u1_struct_0(C_929), u1_struct_0(B_930)) | ~v1_funct_1(E_931) | ~m1_pre_topc(D_927, A_928) | ~m1_pre_topc(C_929, A_928) | ~l1_pre_topc(B_930) | ~v2_pre_topc(B_930) | v2_struct_0(B_930) | ~l1_pre_topc(A_928) | ~v2_pre_topc(A_928) | v2_struct_0(A_928))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.24/3.69  tff(c_12087, plain, (![D_1008, B_1006, A_1005, A_1007, C_1009]: (k3_tmap_1(A_1005, B_1006, C_1009, D_1008, A_1007)=k2_partfun1(u1_struct_0(C_1009), u1_struct_0(B_1006), A_1007, u1_struct_0(D_1008)) | ~m1_pre_topc(D_1008, C_1009) | ~v1_funct_2(A_1007, u1_struct_0(C_1009), u1_struct_0(B_1006)) | ~v1_funct_1(A_1007) | ~m1_pre_topc(D_1008, A_1005) | ~m1_pre_topc(C_1009, A_1005) | ~l1_pre_topc(B_1006) | ~v2_pre_topc(B_1006) | v2_struct_0(B_1006) | ~l1_pre_topc(A_1005) | ~v2_pre_topc(A_1005) | v2_struct_0(A_1005) | ~r1_tarski(A_1007, k2_zfmisc_1(u1_struct_0(C_1009), u1_struct_0(B_1006))))), inference(resolution, [status(thm)], [c_20, c_11095])).
% 10.24/3.69  tff(c_15366, plain, (![A_1136, B_1137, C_1138, A_1139]: (k3_tmap_1(A_1136, B_1137, C_1138, '#skF_5', A_1139)=k2_partfun1(u1_struct_0(C_1138), u1_struct_0(B_1137), A_1139, u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_5', C_1138) | ~v1_funct_2(A_1139, u1_struct_0(C_1138), u1_struct_0(B_1137)) | ~v1_funct_1(A_1139) | ~m1_pre_topc(C_1138, A_1136) | ~l1_pre_topc(B_1137) | ~v2_pre_topc(B_1137) | v2_struct_0(B_1137) | v2_struct_0(A_1136) | ~r1_tarski(A_1139, k2_zfmisc_1(u1_struct_0(C_1138), u1_struct_0(B_1137))) | ~m1_pre_topc('#skF_3', A_1136) | ~l1_pre_topc(A_1136) | ~v2_pre_topc(A_1136))), inference(resolution, [status(thm)], [c_1529, c_12087])).
% 10.24/3.69  tff(c_15372, plain, (![B_1137, A_1139]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_1137), A_1139, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', B_1137, '#skF_3', '#skF_5', A_1139) | ~m1_pre_topc('#skF_5', '#skF_3') | ~v1_funct_2(A_1139, u1_struct_0('#skF_3'), u1_struct_0(B_1137)) | ~v1_funct_1(A_1139) | ~l1_pre_topc(B_1137) | ~v2_pre_topc(B_1137) | v2_struct_0(B_1137) | v2_struct_0('#skF_3') | ~r1_tarski(A_1139, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_1137))) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_85, c_15366])).
% 10.24/3.69  tff(c_15380, plain, (![B_1137, A_1139]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_1137), A_1139, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', B_1137, '#skF_3', '#skF_5', A_1139) | ~v1_funct_2(A_1139, u1_struct_0('#skF_3'), u1_struct_0(B_1137)) | ~v1_funct_1(A_1139) | ~l1_pre_topc(B_1137) | ~v2_pre_topc(B_1137) | v2_struct_0(B_1137) | v2_struct_0('#skF_3') | ~r1_tarski(A_1139, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_1137))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_85, c_60, c_15372])).
% 10.24/3.69  tff(c_18480, plain, (![B_1198, A_1199]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_1198), A_1199, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', B_1198, '#skF_3', '#skF_5', A_1199) | ~v1_funct_2(A_1199, u1_struct_0('#skF_3'), u1_struct_0(B_1198)) | ~v1_funct_1(A_1199) | ~l1_pre_topc(B_1198) | ~v2_pre_topc(B_1198) | v2_struct_0(B_1198) | ~r1_tarski(A_1199, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_1198))))), inference(negUnitSimplification, [status(thm)], [c_74, c_15380])).
% 10.24/3.69  tff(c_18483, plain, (![A_1199]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), A_1199, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', A_1199) | ~v1_funct_2(A_1199, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(A_1199) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_1199, k2_zfmisc_1(u1_struct_0('#skF_3'), '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1541, c_18480])).
% 10.24/3.69  tff(c_18493, plain, (![A_1199]: (k2_partfun1(u1_struct_0('#skF_3'), '#skF_8', A_1199, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', A_1199) | ~v1_funct_2(A_1199, u1_struct_0('#skF_3'), '#skF_8') | ~v1_funct_1(A_1199) | v2_struct_0('#skF_4') | ~r1_tarski(A_1199, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10910, c_66, c_64, c_1541, c_1541, c_18483])).
% 10.24/3.69  tff(c_19409, plain, (![A_1216]: (k2_partfun1(u1_struct_0('#skF_3'), '#skF_8', A_1216, u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', A_1216) | ~v1_funct_2(A_1216, u1_struct_0('#skF_3'), '#skF_8') | ~v1_funct_1(A_1216) | ~r1_tarski(A_1216, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_68, c_18493])).
% 10.24/3.69  tff(c_11028, plain, (![A_911, B_912, C_913, D_914]: (k2_partfun1(u1_struct_0(A_911), u1_struct_0(B_912), C_913, u1_struct_0(D_914))=k2_tmap_1(A_911, B_912, C_913, D_914) | ~m1_pre_topc(D_914, A_911) | ~m1_subset_1(C_913, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_911), u1_struct_0(B_912)))) | ~v1_funct_2(C_913, u1_struct_0(A_911), u1_struct_0(B_912)) | ~v1_funct_1(C_913) | ~l1_pre_topc(B_912) | ~v2_pre_topc(B_912) | v2_struct_0(B_912) | ~l1_pre_topc(A_911) | ~v2_pre_topc(A_911) | v2_struct_0(A_911))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.24/3.69  tff(c_11470, plain, (![A_976, B_977, A_978, D_979]: (k2_partfun1(u1_struct_0(A_976), u1_struct_0(B_977), A_978, u1_struct_0(D_979))=k2_tmap_1(A_976, B_977, A_978, D_979) | ~m1_pre_topc(D_979, A_976) | ~v1_funct_2(A_978, u1_struct_0(A_976), u1_struct_0(B_977)) | ~v1_funct_1(A_978) | ~l1_pre_topc(B_977) | ~v2_pre_topc(B_977) | v2_struct_0(B_977) | ~l1_pre_topc(A_976) | ~v2_pre_topc(A_976) | v2_struct_0(A_976) | ~r1_tarski(A_978, k2_zfmisc_1(u1_struct_0(A_976), u1_struct_0(B_977))))), inference(resolution, [status(thm)], [c_20, c_11028])).
% 10.24/3.69  tff(c_15727, plain, (![A_1155, B_1156, D_1157]: (k2_partfun1(u1_struct_0(A_1155), u1_struct_0(B_1156), k2_zfmisc_1(u1_struct_0(A_1155), u1_struct_0(B_1156)), u1_struct_0(D_1157))=k2_tmap_1(A_1155, B_1156, k2_zfmisc_1(u1_struct_0(A_1155), u1_struct_0(B_1156)), D_1157) | ~m1_pre_topc(D_1157, A_1155) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1155), u1_struct_0(B_1156)), u1_struct_0(A_1155), u1_struct_0(B_1156)) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1155), u1_struct_0(B_1156))) | ~l1_pre_topc(B_1156) | ~v2_pre_topc(B_1156) | v2_struct_0(B_1156) | ~l1_pre_topc(A_1155) | ~v2_pre_topc(A_1155) | v2_struct_0(A_1155))), inference(resolution, [status(thm)], [c_16, c_11470])).
% 10.24/3.69  tff(c_15746, plain, (![A_1155, D_1157]: (k2_partfun1(u1_struct_0(A_1155), '#skF_8', k2_zfmisc_1(u1_struct_0(A_1155), u1_struct_0('#skF_4')), u1_struct_0(D_1157))=k2_tmap_1(A_1155, '#skF_4', k2_zfmisc_1(u1_struct_0(A_1155), u1_struct_0('#skF_4')), D_1157) | ~m1_pre_topc(D_1157, A_1155) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(A_1155), u1_struct_0('#skF_4')), u1_struct_0(A_1155), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(A_1155), u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1155) | ~v2_pre_topc(A_1155) | v2_struct_0(A_1155))), inference(superposition, [status(thm), theory('equality')], [c_1541, c_15727])).
% 10.24/3.69  tff(c_15764, plain, (![A_1155, D_1157]: (k2_partfun1(u1_struct_0(A_1155), '#skF_8', '#skF_8', u1_struct_0(D_1157))=k2_tmap_1(A_1155, '#skF_4', '#skF_8', D_1157) | ~m1_pre_topc(D_1157, A_1155) | ~v1_funct_2('#skF_8', u1_struct_0(A_1155), '#skF_8') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1155) | ~v2_pre_topc(A_1155) | v2_struct_0(A_1155))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_10910, c_1541, c_1541, c_10910, c_1541, c_10910, c_1541, c_10910, c_1541, c_15746])).
% 10.24/3.69  tff(c_15765, plain, (![A_1155, D_1157]: (k2_partfun1(u1_struct_0(A_1155), '#skF_8', '#skF_8', u1_struct_0(D_1157))=k2_tmap_1(A_1155, '#skF_4', '#skF_8', D_1157) | ~m1_pre_topc(D_1157, A_1155) | ~v1_funct_2('#skF_8', u1_struct_0(A_1155), '#skF_8') | ~l1_pre_topc(A_1155) | ~v2_pre_topc(A_1155) | v2_struct_0(A_1155))), inference(negUnitSimplification, [status(thm)], [c_68, c_15764])).
% 10.24/3.69  tff(c_19416, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8')=k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_3'), '#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_3'), '#skF_8') | ~v1_funct_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_19409, c_15765])).
% 10.24/3.69  tff(c_19454, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8')=k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48, c_10549, c_72, c_70, c_10549, c_60, c_19416])).
% 10.24/3.69  tff(c_19455, plain, (k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8')=k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_19454])).
% 10.24/3.69  tff(c_10548, plain, (r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k3_tmap_1('#skF_3', '#skF_4', '#skF_3', '#skF_5', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_1564])).
% 10.24/3.69  tff(c_19484, plain, (r2_funct_2(u1_struct_0('#skF_5'), '#skF_8', k2_tmap_1('#skF_3', '#skF_4', '#skF_8', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19455, c_10548])).
% 10.24/3.69  tff(c_19486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10792, c_19484])).
% 10.24/3.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.24/3.69  
% 10.24/3.69  Inference rules
% 10.24/3.69  ----------------------
% 10.24/3.69  #Ref     : 0
% 10.24/3.69  #Sup     : 5289
% 10.24/3.69  #Fact    : 0
% 10.24/3.69  #Define  : 0
% 10.24/3.69  #Split   : 46
% 10.24/3.69  #Chain   : 0
% 10.24/3.69  #Close   : 0
% 10.24/3.69  
% 10.24/3.69  Ordering : KBO
% 10.24/3.69  
% 10.24/3.69  Simplification rules
% 10.24/3.69  ----------------------
% 10.24/3.69  #Subsume      : 2790
% 10.24/3.69  #Demod        : 3403
% 10.24/3.69  #Tautology    : 966
% 10.24/3.69  #SimpNegUnit  : 133
% 10.24/3.69  #BackRed      : 73
% 10.24/3.69  
% 10.24/3.69  #Partial instantiations: 0
% 10.24/3.69  #Strategies tried      : 1
% 10.24/3.69  
% 10.24/3.69  Timing (in seconds)
% 10.24/3.69  ----------------------
% 10.24/3.69  Preprocessing        : 0.41
% 10.24/3.69  Parsing              : 0.21
% 10.24/3.69  CNF conversion       : 0.06
% 10.24/3.69  Main loop            : 2.49
% 10.24/3.69  Inferencing          : 0.77
% 10.24/3.69  Reduction            : 0.71
% 10.24/3.69  Demodulation         : 0.53
% 10.24/3.69  BG Simplification    : 0.08
% 10.24/3.69  Subsumption          : 0.80
% 10.24/3.69  Abstraction          : 0.13
% 10.24/3.69  MUC search           : 0.00
% 10.24/3.69  Cooper               : 0.00
% 10.24/3.69  Total                : 2.96
% 10.24/3.69  Index Insertion      : 0.00
% 10.24/3.69  Index Deletion       : 0.00
% 10.24/3.69  Index Matching       : 0.00
% 10.24/3.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
