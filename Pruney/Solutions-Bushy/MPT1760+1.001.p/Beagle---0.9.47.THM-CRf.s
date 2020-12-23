%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1760+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:21 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :  244 (1030 expanded)
%              Number of leaves         :   34 ( 377 expanded)
%              Depth                    :   12
%              Number of atoms          :  677 (9154 expanded)
%              Number of equality atoms :   16 (  90 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_partfun1 > k2_tmap_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_213,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(B),u1_struct_0(C))
                          & v5_pre_topc(E,B,C)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(A),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                           => ( ( v1_funct_1(k2_tmap_1(A,B,F,D))
                                & v1_funct_2(k2_tmap_1(A,B,F,D),u1_struct_0(D),u1_struct_0(B))
                                & v5_pre_topc(k2_tmap_1(A,B,F,D),D,B)
                                & m1_subset_1(k2_tmap_1(A,B,F,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                             => ( v1_funct_1(k2_tmap_1(A,C,k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),F,E),D))
                                & v1_funct_2(k2_tmap_1(A,C,k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),F,E),D),u1_struct_0(D),u1_struct_0(C))
                                & v5_pre_topc(k2_tmap_1(A,C,k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),F,E),D),D,C)
                                & m1_subset_1(k2_tmap_1(A,C,k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),F,E),D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(C)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tmap_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_151,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(B),u1_struct_0(C))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(A),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                         => ( ( v5_pre_topc(E,B,C)
                              & v5_pre_topc(k2_tmap_1(A,B,F,D),D,B) )
                           => v5_pre_topc(k2_tmap_1(A,C,k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),F,E),D),D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v1_xboole_0(B)
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & v1_funct_2(E,B,C)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k5_relat_1(D,E))
        & v1_funct_2(k5_relat_1(D,E),A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_36,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_30,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_38,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_44,plain,(
    v5_pre_topc('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_2549,plain,(
    ! [E_312,D_308,A_307,B_311,C_309,F_310] :
      ( k1_partfun1(A_307,B_311,C_309,D_308,E_312,F_310) = k5_relat_1(E_312,F_310)
      | ~ m1_subset_1(F_310,k1_zfmisc_1(k2_zfmisc_1(C_309,D_308)))
      | ~ v1_funct_1(F_310)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(A_307,B_311)))
      | ~ v1_funct_1(E_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2557,plain,(
    ! [A_307,B_311,E_312] :
      ( k1_partfun1(A_307,B_311,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_312,'#skF_5') = k5_relat_1(E_312,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(A_307,B_311)))
      | ~ v1_funct_1(E_312) ) ),
    inference(resolution,[status(thm)],[c_42,c_2549])).

tff(c_2613,plain,(
    ! [A_316,B_317,E_318] :
      ( k1_partfun1(A_316,B_317,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_318,'#skF_5') = k5_relat_1(E_318,'#skF_5')
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ v1_funct_1(E_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2557])).

tff(c_2622,plain,
    ( k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5') = k5_relat_1('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_2613])).

tff(c_2634,plain,(
    k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5') = k5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2622])).

tff(c_3892,plain,(
    ! [C_386,A_390,D_388,F_387,B_385,E_389] :
      ( v5_pre_topc(k2_tmap_1(A_390,C_386,k1_partfun1(u1_struct_0(A_390),u1_struct_0(B_385),u1_struct_0(B_385),u1_struct_0(C_386),F_387,E_389),D_388),D_388,C_386)
      | ~ v5_pre_topc(k2_tmap_1(A_390,B_385,F_387,D_388),D_388,B_385)
      | ~ v5_pre_topc(E_389,B_385,C_386)
      | ~ m1_subset_1(F_387,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_390),u1_struct_0(B_385))))
      | ~ v1_funct_2(F_387,u1_struct_0(A_390),u1_struct_0(B_385))
      | ~ v1_funct_1(F_387)
      | ~ m1_subset_1(E_389,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_385),u1_struct_0(C_386))))
      | ~ v1_funct_2(E_389,u1_struct_0(B_385),u1_struct_0(C_386))
      | ~ v1_funct_1(E_389)
      | ~ m1_pre_topc(D_388,A_390)
      | v2_struct_0(D_388)
      | ~ l1_pre_topc(C_386)
      | ~ v2_pre_topc(C_386)
      | v2_struct_0(C_386)
      | ~ l1_pre_topc(B_385)
      | ~ v2_pre_topc(B_385)
      | v2_struct_0(B_385)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_3901,plain,(
    ! [D_388] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_388),D_388,'#skF_3')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_388),D_388,'#skF_2')
      | ~ v5_pre_topc('#skF_5','#skF_2','#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_388,'#skF_1')
      | v2_struct_0(D_388)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2634,c_3892])).

tff(c_3909,plain,(
    ! [D_388] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_388),D_388,'#skF_3')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_388),D_388,'#skF_2')
      | ~ m1_pre_topc(D_388,'#skF_1')
      | v2_struct_0(D_388)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_56,c_54,c_48,c_46,c_42,c_40,c_38,c_36,c_44,c_3901])).

tff(c_3911,plain,(
    ! [D_391] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_391),D_391,'#skF_3')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_391),D_391,'#skF_2')
      | ~ m1_pre_topc(D_391,'#skF_1')
      | v2_struct_0(D_391) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_58,c_3909])).

tff(c_73,plain,(
    ! [B_149,A_150] :
      ( l1_pre_topc(B_149)
      | ~ m1_pre_topc(B_149,A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_73])).

tff(c_79,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_76])).

tff(c_12,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2781,plain,(
    ! [A_325,B_326,C_327,D_328] :
      ( v1_funct_1(k2_tmap_1(A_325,B_326,C_327,D_328))
      | ~ l1_struct_0(D_328)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_325),u1_struct_0(B_326))))
      | ~ v1_funct_2(C_327,u1_struct_0(A_325),u1_struct_0(B_326))
      | ~ v1_funct_1(C_327)
      | ~ l1_struct_0(B_326)
      | ~ l1_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2798,plain,(
    ! [D_328] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_328))
      | ~ l1_struct_0(D_328)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_2781])).

tff(c_2820,plain,(
    ! [D_328] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_328))
      | ~ l1_struct_0(D_328)
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2798])).

tff(c_2831,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2820])).

tff(c_2834,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_2831])).

tff(c_2838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2834])).

tff(c_2840,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2820])).

tff(c_34,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_32,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_28,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_2794,plain,(
    ! [D_328] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_328))
      | ~ l1_struct_0(D_328)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'))
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_2781])).

tff(c_2814,plain,(
    ! [D_328] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_328))
      | ~ l1_struct_0(D_328)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2794])).

tff(c_2927,plain,(
    ! [D_328] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_328))
      | ~ l1_struct_0(D_328)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2840,c_2814])).

tff(c_2928,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2927])).

tff(c_2931,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_2928])).

tff(c_2935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2931])).

tff(c_2937,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2927])).

tff(c_2854,plain,(
    ! [C_334,B_330,E_331,D_333,A_332] :
      ( v1_funct_1(k5_relat_1(D_333,E_331))
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(B_330,C_334)))
      | ~ v1_funct_2(E_331,B_330,C_334)
      | ~ v1_funct_1(E_331)
      | ~ m1_subset_1(D_333,k1_zfmisc_1(k2_zfmisc_1(A_332,B_330)))
      | ~ v1_funct_2(D_333,A_332,B_330)
      | ~ v1_funct_1(D_333)
      | v1_xboole_0(B_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2870,plain,(
    ! [D_333,A_332] :
      ( v1_funct_1(k5_relat_1(D_333,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_333,k1_zfmisc_1(k2_zfmisc_1(A_332,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_333,A_332,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_333)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_2854])).

tff(c_2892,plain,(
    ! [D_333,A_332] :
      ( v1_funct_1(k5_relat_1(D_333,'#skF_5'))
      | ~ m1_subset_1(D_333,k1_zfmisc_1(k2_zfmisc_1(A_332,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_333,A_332,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_333)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2870])).

tff(c_3380,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2892])).

tff(c_16,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3383,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3380,c_16])).

tff(c_3386,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2840,c_3383])).

tff(c_3388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3386])).

tff(c_3390,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2892])).

tff(c_3103,plain,(
    ! [E_345,B_344,A_346,D_347,C_348] :
      ( v1_funct_2(k5_relat_1(D_347,E_345),A_346,C_348)
      | ~ m1_subset_1(E_345,k1_zfmisc_1(k2_zfmisc_1(B_344,C_348)))
      | ~ v1_funct_2(E_345,B_344,C_348)
      | ~ v1_funct_1(E_345)
      | ~ m1_subset_1(D_347,k1_zfmisc_1(k2_zfmisc_1(A_346,B_344)))
      | ~ v1_funct_2(D_347,A_346,B_344)
      | ~ v1_funct_1(D_347)
      | v1_xboole_0(B_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3125,plain,(
    ! [D_347,A_346] :
      ( v1_funct_2(k5_relat_1(D_347,'#skF_5'),A_346,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_347,k1_zfmisc_1(k2_zfmisc_1(A_346,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_347,A_346,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_347)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_3103])).

tff(c_3156,plain,(
    ! [D_347,A_346] :
      ( v1_funct_2(k5_relat_1(D_347,'#skF_5'),A_346,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_347,k1_zfmisc_1(k2_zfmisc_1(A_346,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_347,A_346,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_347)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3125])).

tff(c_3700,plain,(
    ! [D_364,A_365] :
      ( v1_funct_2(k5_relat_1(D_364,'#skF_5'),A_365,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_364,k1_zfmisc_1(k2_zfmisc_1(A_365,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_364,A_365,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_364) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3390,c_3156])).

tff(c_3735,plain,
    ( v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_3700])).

tff(c_3766,plain,(
    v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3735])).

tff(c_2796,plain,(
    ! [D_328] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_328))
      | ~ l1_struct_0(D_328)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_2781])).

tff(c_2817,plain,(
    ! [D_328] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_328))
      | ~ l1_struct_0(D_328)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2796])).

tff(c_2821,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2817])).

tff(c_2824,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_2821])).

tff(c_2828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2824])).

tff(c_2830,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2817])).

tff(c_2839,plain,(
    ! [D_328] :
      ( ~ l1_struct_0('#skF_3')
      | v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_328))
      | ~ l1_struct_0(D_328) ) ),
    inference(splitRight,[status(thm)],[c_2820])).

tff(c_2844,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2839])).

tff(c_2847,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_2844])).

tff(c_2851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2847])).

tff(c_2853,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2839])).

tff(c_80,plain,(
    ! [A_156,E_152,C_155,D_153,F_151,B_154] :
      ( v1_funct_1(k1_partfun1(A_156,B_154,C_155,D_153,E_152,F_151))
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_155,D_153)))
      | ~ v1_funct_1(F_151)
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_1(E_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_86,plain,(
    ! [A_156,B_154,E_152] :
      ( v1_funct_1(k1_partfun1(A_156,B_154,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_152,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_1(E_152) ) ),
    inference(resolution,[status(thm)],[c_42,c_80])).

tff(c_95,plain,(
    ! [A_156,B_154,E_152] :
      ( v1_funct_1(k1_partfun1(A_156,B_154,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_152,'#skF_5'))
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_1(E_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_86])).

tff(c_2715,plain,
    ( v1_funct_1(k5_relat_1('#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2634,c_95])).

tff(c_2721,plain,(
    v1_funct_1(k5_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_2715])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] :
      ( m1_subset_1(k1_partfun1(A_1,B_2,C_3,D_4,E_5,F_6),k1_zfmisc_1(k2_zfmisc_1(A_1,D_4)))
      | ~ m1_subset_1(F_6,k1_zfmisc_1(k2_zfmisc_1(C_3,D_4)))
      | ~ v1_funct_1(F_6)
      | ~ m1_subset_1(E_5,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_1(E_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2712,plain,
    ( m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2634,c_2])).

tff(c_2719,plain,(
    m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_48,c_42,c_2712])).

tff(c_2953,plain,(
    ! [A_337,B_338,C_339,D_340] :
      ( v1_funct_2(k2_tmap_1(A_337,B_338,C_339,D_340),u1_struct_0(D_340),u1_struct_0(B_338))
      | ~ l1_struct_0(D_340)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_337),u1_struct_0(B_338))))
      | ~ v1_funct_2(C_339,u1_struct_0(A_337),u1_struct_0(B_338))
      | ~ v1_funct_1(C_339)
      | ~ l1_struct_0(B_338)
      | ~ l1_struct_0(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2959,plain,(
    ! [D_340] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_340),u1_struct_0(D_340),u1_struct_0('#skF_3'))
      | ~ l1_struct_0(D_340)
      | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k5_relat_1('#skF_6','#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2719,c_2953])).

tff(c_2981,plain,(
    ! [D_340] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_340),u1_struct_0(D_340),u1_struct_0('#skF_3'))
      | ~ l1_struct_0(D_340)
      | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2830,c_2853,c_2721,c_2959])).

tff(c_3882,plain,(
    ! [D_384] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_384),u1_struct_0(D_384),u1_struct_0('#skF_3'))
      | ~ l1_struct_0(D_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3766,c_2981])).

tff(c_1379,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( v1_funct_1(k2_tmap_1(A_246,B_247,C_248,D_249))
      | ~ l1_struct_0(D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_246),u1_struct_0(B_247))))
      | ~ v1_funct_2(C_248,u1_struct_0(A_246),u1_struct_0(B_247))
      | ~ v1_funct_1(C_248)
      | ~ l1_struct_0(B_247)
      | ~ l1_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1383,plain,(
    ! [D_249] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_249))
      | ~ l1_struct_0(D_249)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_1379])).

tff(c_1391,plain,(
    ! [D_249] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_249))
      | ~ l1_struct_0(D_249)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1383])).

tff(c_1395,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1391])).

tff(c_1398,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1395])).

tff(c_1402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1398])).

tff(c_1404,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1391])).

tff(c_1385,plain,(
    ! [D_249] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_249))
      | ~ l1_struct_0(D_249)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_1379])).

tff(c_1394,plain,(
    ! [D_249] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_249))
      | ~ l1_struct_0(D_249)
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1385])).

tff(c_1405,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1394])).

tff(c_1408,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1405])).

tff(c_1412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1408])).

tff(c_1413,plain,(
    ! [D_249] :
      ( ~ l1_struct_0('#skF_3')
      | v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_249))
      | ~ l1_struct_0(D_249) ) ),
    inference(splitRight,[status(thm)],[c_1394])).

tff(c_1415,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1413])).

tff(c_1438,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1415])).

tff(c_1442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1438])).

tff(c_1444,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1413])).

tff(c_1335,plain,(
    ! [D_238,E_242,F_240,A_237,C_239,B_241] :
      ( k1_partfun1(A_237,B_241,C_239,D_238,E_242,F_240) = k5_relat_1(E_242,F_240)
      | ~ m1_subset_1(F_240,k1_zfmisc_1(k2_zfmisc_1(C_239,D_238)))
      | ~ v1_funct_1(F_240)
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_237,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1341,plain,(
    ! [A_237,B_241,E_242] :
      ( k1_partfun1(A_237,B_241,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_242,'#skF_5') = k5_relat_1(E_242,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_237,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(resolution,[status(thm)],[c_42,c_1335])).

tff(c_1538,plain,(
    ! [A_265,B_266,E_267] :
      ( k1_partfun1(A_265,B_266,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_267,'#skF_5') = k5_relat_1(E_267,'#skF_5')
      | ~ m1_subset_1(E_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_1(E_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1341])).

tff(c_1553,plain,
    ( k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5') = k5_relat_1('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_1538])).

tff(c_1569,plain,(
    k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5') = k5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1553])).

tff(c_1581,plain,
    ( v1_funct_1(k5_relat_1('#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1569,c_95])).

tff(c_1587,plain,(
    v1_funct_1(k5_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1581])).

tff(c_1578,plain,
    ( m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1569,c_2])).

tff(c_1585,plain,(
    m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_48,c_42,c_1578])).

tff(c_1414,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1394])).

tff(c_1381,plain,(
    ! [D_249] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_249))
      | ~ l1_struct_0(D_249)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'))
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_1379])).

tff(c_1388,plain,(
    ! [D_249] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_249))
      | ~ l1_struct_0(D_249)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1381])).

tff(c_1459,plain,(
    ! [D_249] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_249))
      | ~ l1_struct_0(D_249)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1388])).

tff(c_1460,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1459])).

tff(c_1463,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1460])).

tff(c_1467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1463])).

tff(c_1469,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1459])).

tff(c_2081,plain,(
    ! [A_289,B_290,C_291,D_292] :
      ( m1_subset_1(k2_tmap_1(A_289,B_290,C_291,D_292),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_292),u1_struct_0(B_290))))
      | ~ l1_struct_0(D_292)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_289),u1_struct_0(B_290))))
      | ~ v1_funct_2(C_291,u1_struct_0(A_289),u1_struct_0(B_290))
      | ~ v1_funct_1(C_291)
      | ~ l1_struct_0(B_290)
      | ~ l1_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_144,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( v1_funct_1(k2_tmap_1(A_175,B_176,C_177,D_178))
      | ~ l1_struct_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175),u1_struct_0(B_176))))
      | ~ v1_funct_2(C_177,u1_struct_0(A_175),u1_struct_0(B_176))
      | ~ v1_funct_1(C_177)
      | ~ l1_struct_0(B_176)
      | ~ l1_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_150,plain,(
    ! [D_178] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_178))
      | ~ l1_struct_0(D_178)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_144])).

tff(c_159,plain,(
    ! [D_178] :
      ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_178))
      | ~ l1_struct_0(D_178)
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_150])).

tff(c_170,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_173,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_170])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_173])).

tff(c_179,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_146,plain,(
    ! [D_178] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_178))
      | ~ l1_struct_0(D_178)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'))
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_153,plain,(
    ! [D_178] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_178))
      | ~ l1_struct_0(D_178)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_146])).

tff(c_224,plain,(
    ! [D_178] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),D_178))
      | ~ l1_struct_0(D_178)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_153])).

tff(c_225,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_228,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_228])).

tff(c_234,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_148,plain,(
    ! [D_178] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_178))
      | ~ l1_struct_0(D_178)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_144])).

tff(c_156,plain,(
    ! [D_178] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_6',D_178))
      | ~ l1_struct_0(D_178)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_148])).

tff(c_160,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_163,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_160])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_163])).

tff(c_169,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_178,plain,(
    ! [D_178] :
      ( ~ l1_struct_0('#skF_3')
      | v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_5',D_178))
      | ~ l1_struct_0(D_178) ) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_180,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_203,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_180])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_203])).

tff(c_209,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_100,plain,(
    ! [A_166,D_167,C_168,E_171,F_169,B_170] :
      ( k1_partfun1(A_166,B_170,C_168,D_167,E_171,F_169) = k5_relat_1(E_171,F_169)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(C_168,D_167)))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_166,B_170)))
      | ~ v1_funct_1(E_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_106,plain,(
    ! [A_166,B_170,E_171] :
      ( k1_partfun1(A_166,B_170,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_171,'#skF_5') = k5_relat_1(E_171,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_166,B_170)))
      | ~ v1_funct_1(E_171) ) ),
    inference(resolution,[status(thm)],[c_42,c_100])).

tff(c_303,plain,(
    ! [A_194,B_195,E_196] :
      ( k1_partfun1(A_194,B_195,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),E_196,'#skF_5') = k5_relat_1(E_196,'#skF_5')
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_1(E_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_106])).

tff(c_318,plain,
    ( k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5') = k5_relat_1('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_334,plain,(
    k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5') = k5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_318])).

tff(c_345,plain,
    ( v1_funct_1(k5_relat_1('#skF_6','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_95])).

tff(c_351,plain,(
    v1_funct_1(k5_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_345])).

tff(c_342,plain,
    ( m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_2])).

tff(c_349,plain,(
    m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_48,c_42,c_342])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( v1_funct_1(k2_tmap_1(A_7,B_8,C_9,D_10))
      | ~ l1_struct_0(D_10)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7),u1_struct_0(B_8))))
      | ~ v1_funct_2(C_9,u1_struct_0(A_7),u1_struct_0(B_8))
      | ~ v1_funct_1(C_9)
      | ~ l1_struct_0(B_8)
      | ~ l1_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_357,plain,(
    ! [D_10] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_10))
      | ~ l1_struct_0(D_10)
      | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k5_relat_1('#skF_6','#skF_5'))
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_349,c_10])).

tff(c_370,plain,(
    ! [D_10] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_10))
      | ~ l1_struct_0(D_10)
      | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_209,c_351,c_357])).

tff(c_1152,plain,(
    ~ v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_394,plain,(
    ! [E_198,D_200,B_197,C_201,A_199] :
      ( v1_funct_1(k5_relat_1(D_200,E_198))
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(B_197,C_201)))
      | ~ v1_funct_2(E_198,B_197,C_201)
      | ~ v1_funct_1(E_198)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_199,B_197)))
      | ~ v1_funct_2(D_200,A_199,B_197)
      | ~ v1_funct_1(D_200)
      | v1_xboole_0(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_408,plain,(
    ! [D_200,A_199] :
      ( v1_funct_1(k5_relat_1(D_200,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_199,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_200,A_199,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_200)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_394])).

tff(c_427,plain,(
    ! [D_200,A_199] :
      ( v1_funct_1(k5_relat_1(D_200,'#skF_5'))
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_199,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_200,A_199,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_200)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_408])).

tff(c_571,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_574,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_571,c_16])).

tff(c_577,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_574])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_577])).

tff(c_581,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_619,plain,(
    ! [C_217,D_216,A_215,B_213,E_214] :
      ( v1_funct_2(k5_relat_1(D_216,E_214),A_215,C_217)
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(B_213,C_217)))
      | ~ v1_funct_2(E_214,B_213,C_217)
      | ~ v1_funct_1(E_214)
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(A_215,B_213)))
      | ~ v1_funct_2(D_216,A_215,B_213)
      | ~ v1_funct_1(D_216)
      | v1_xboole_0(B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_637,plain,(
    ! [D_216,A_215] :
      ( v1_funct_2(k5_relat_1(D_216,'#skF_5'),A_215,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(A_215,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_216,A_215,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_216)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_619])).

tff(c_668,plain,(
    ! [D_216,A_215] :
      ( v1_funct_2(k5_relat_1(D_216,'#skF_5'),A_215,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_216,k1_zfmisc_1(k2_zfmisc_1(A_215,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_216,A_215,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_216)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_637])).

tff(c_1252,plain,(
    ! [D_231,A_232] :
      ( v1_funct_2(k5_relat_1(D_231,'#skF_5'),A_232,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_231,k1_zfmisc_1(k2_zfmisc_1(A_232,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_231,A_232,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_231) ) ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_668])).

tff(c_1287,plain,
    ( v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_1252])).

tff(c_1318,plain,(
    v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1287])).

tff(c_1320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1152,c_1318])).

tff(c_1323,plain,(
    ! [D_233] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),D_233))
      | ~ l1_struct_0(D_233) ) ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_26,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_98,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_338,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_98])).

tff(c_1326,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1323,c_338])).

tff(c_1330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_1326])).

tff(c_1331,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1333,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1331])).

tff(c_1573,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1569,c_1333])).

tff(c_2096,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1(k5_relat_1('#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k5_relat_1('#skF_6','#skF_5'))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2081,c_1573])).

tff(c_2121,plain,(
    ~ v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1444,c_1587,c_1585,c_1469,c_2096])).

tff(c_1630,plain,(
    ! [D_271,E_269,B_268,C_272,A_270] :
      ( v1_funct_1(k5_relat_1(D_271,E_269))
      | ~ m1_subset_1(E_269,k1_zfmisc_1(k2_zfmisc_1(B_268,C_272)))
      | ~ v1_funct_2(E_269,B_268,C_272)
      | ~ v1_funct_1(E_269)
      | ~ m1_subset_1(D_271,k1_zfmisc_1(k2_zfmisc_1(A_270,B_268)))
      | ~ v1_funct_2(D_271,A_270,B_268)
      | ~ v1_funct_1(D_271)
      | v1_xboole_0(B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1644,plain,(
    ! [D_271,A_270] :
      ( v1_funct_1(k5_relat_1(D_271,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_271,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_271,A_270,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_271)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1630])).

tff(c_1663,plain,(
    ! [D_271,A_270] :
      ( v1_funct_1(k5_relat_1(D_271,'#skF_5'))
      | ~ m1_subset_1(D_271,k1_zfmisc_1(k2_zfmisc_1(A_270,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_271,A_270,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_271)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1644])).

tff(c_1984,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1663])).

tff(c_1987,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1984,c_16])).

tff(c_1990,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1987])).

tff(c_1992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1990])).

tff(c_1994,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1663])).

tff(c_1873,plain,(
    ! [D_285,A_284,C_286,E_283,B_282] :
      ( v1_funct_2(k5_relat_1(D_285,E_283),A_284,C_286)
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(B_282,C_286)))
      | ~ v1_funct_2(E_283,B_282,C_286)
      | ~ v1_funct_1(E_283)
      | ~ m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1(A_284,B_282)))
      | ~ v1_funct_2(D_285,A_284,B_282)
      | ~ v1_funct_1(D_285)
      | v1_xboole_0(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1893,plain,(
    ! [D_285,A_284] :
      ( v1_funct_2(k5_relat_1(D_285,'#skF_5'),A_284,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1(A_284,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_285,A_284,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_285)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1873])).

tff(c_1925,plain,(
    ! [D_285,A_284] :
      ( v1_funct_2(k5_relat_1(D_285,'#skF_5'),A_284,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1(A_284,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_285,A_284,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_285)
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1893])).

tff(c_2472,plain,(
    ! [D_302,A_303] :
      ( v1_funct_2(k5_relat_1(D_302,'#skF_5'),A_303,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1(A_303,u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_302,A_303,u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_302) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1994,c_1925])).

tff(c_2507,plain,
    ( v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_2472])).

tff(c_2538,plain,(
    v1_funct_2(k5_relat_1('#skF_6','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2507])).

tff(c_2540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2121,c_2538])).

tff(c_2541,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_3',k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1331])).

tff(c_3490,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),'#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2634,c_2634,c_2541])).

tff(c_3491,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3490])).

tff(c_3885,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3882,c_3491])).

tff(c_3889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2937,c_3885])).

tff(c_3890,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_3',k5_relat_1('#skF_6','#skF_5'),'#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3490])).

tff(c_3914,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_6','#skF_4'),'#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3911,c_3890])).

tff(c_3917,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30,c_3914])).

tff(c_3919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3917])).

%------------------------------------------------------------------------------
