%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1335+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:49 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 676 expanded)
%              Number of leaves         :   41 ( 262 expanded)
%              Depth                    :   17
%              Number of atoms          :  278 (3471 expanded)
%              Number of equality atoms :   15 ( 134 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k1_partfun1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & l1_pre_topc(C) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ( ( v5_pre_topc(D,A,C)
                            & v5_pre_topc(E,C,B) )
                         => v5_pre_topc(k1_partfun1(u1_struct_0(A),u1_struct_0(C),u1_struct_0(C),u1_struct_0(B),D,E),A,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_49,axiom,(
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

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_60,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_18,plain,(
    ! [A_36] :
      ( l1_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3005,plain,(
    ! [C_364,F_366,B_361,E_365,D_363,A_362] :
      ( k1_partfun1(A_362,B_361,C_364,D_363,E_365,F_366) = k5_relat_1(E_365,F_366)
      | ~ m1_subset_1(F_366,k1_zfmisc_1(k2_zfmisc_1(C_364,D_363)))
      | ~ v1_funct_1(F_366)
      | ~ m1_subset_1(E_365,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361)))
      | ~ v1_funct_1(E_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3019,plain,(
    ! [A_362,B_361,E_365] :
      ( k1_partfun1(A_362,B_361,u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),E_365,'#skF_7') = k5_relat_1(E_365,'#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_365,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361)))
      | ~ v1_funct_1(E_365) ) ),
    inference(resolution,[status(thm)],[c_48,c_3005])).

tff(c_3102,plain,(
    ! [A_377,B_378,E_379] :
      ( k1_partfun1(A_377,B_378,u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),E_379,'#skF_7') = k5_relat_1(E_379,'#skF_7')
      | ~ m1_subset_1(E_379,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378)))
      | ~ v1_funct_1(E_379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3019])).

tff(c_3124,plain,
    ( k1_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_3102])).

tff(c_3138,plain,(
    k1_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_7') = k5_relat_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3124])).

tff(c_42,plain,(
    ~ v5_pre_topc(k1_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_6','#skF_7'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3149,plain,(
    ~ v5_pre_topc(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3138,c_42])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2879,plain,(
    ! [E_328,F_326,A_325,C_327,D_323,B_324] :
      ( v1_funct_1(k1_partfun1(A_325,B_324,C_327,D_323,E_328,F_326))
      | ~ m1_subset_1(F_326,k1_zfmisc_1(k2_zfmisc_1(C_327,D_323)))
      | ~ v1_funct_1(F_326)
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324)))
      | ~ v1_funct_1(E_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2890,plain,(
    ! [A_325,B_324,E_328] :
      ( v1_funct_1(k1_partfun1(A_325,B_324,u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),E_328,'#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324)))
      | ~ v1_funct_1(E_328) ) ),
    inference(resolution,[status(thm)],[c_48,c_2879])).

tff(c_2901,plain,(
    ! [A_325,B_324,E_328] :
      ( v1_funct_1(k1_partfun1(A_325,B_324,u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),E_328,'#skF_7'))
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324)))
      | ~ v1_funct_1(E_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2890])).

tff(c_3153,plain,
    ( v1_funct_1(k5_relat_1('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3138,c_2901])).

tff(c_3157,plain,(
    v1_funct_1(k5_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_3153])).

tff(c_3159,plain,(
    ! [E_385,F_383,B_381,C_384,D_380,A_382] :
      ( m1_subset_1(k1_partfun1(A_382,B_381,C_384,D_380,E_385,F_383),k1_zfmisc_1(k2_zfmisc_1(A_382,D_380)))
      | ~ m1_subset_1(F_383,k1_zfmisc_1(k2_zfmisc_1(C_384,D_380)))
      | ~ v1_funct_1(F_383)
      | ~ m1_subset_1(E_385,k1_zfmisc_1(k2_zfmisc_1(A_382,B_381)))
      | ~ v1_funct_1(E_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3179,plain,
    ( m1_subset_1(k5_relat_1('#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3138,c_3159])).

tff(c_3191,plain,(
    m1_subset_1(k5_relat_1('#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_3179])).

tff(c_3346,plain,(
    ! [A_389,B_390,C_391] :
      ( v4_pre_topc('#skF_1'(A_389,B_390,C_391),B_390)
      | v5_pre_topc(C_391,A_389,B_390)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_389),u1_struct_0(B_390))))
      | ~ v1_funct_2(C_391,u1_struct_0(A_389),u1_struct_0(B_390))
      | ~ v1_funct_1(C_391)
      | ~ l1_pre_topc(B_390)
      | ~ l1_pre_topc(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3352,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')),'#skF_4')
    | v5_pre_topc(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_4')
    | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_3191,c_3346])).

tff(c_3383,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')),'#skF_4')
    | v5_pre_topc(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_4')
    | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3157,c_3352])).

tff(c_3384,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')),'#skF_4')
    | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_3149,c_3383])).

tff(c_3448,plain,(
    ~ v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3384])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2670,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( k8_relset_1(A_297,B_298,C_299,D_300) = k10_relat_1(C_299,D_300)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2702,plain,(
    ! [D_302] : k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_7',D_302) = k10_relat_1('#skF_7',D_302) ),
    inference(resolution,[status(thm)],[c_48,c_2670])).

tff(c_16,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( m1_subset_1(k8_relset_1(A_32,B_33,C_34,D_35),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2708,plain,(
    ! [D_302] :
      ( m1_subset_1(k10_relat_1('#skF_7',D_302),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2702,c_16])).

tff(c_2716,plain,(
    ! [D_303] : m1_subset_1(k10_relat_1('#skF_7',D_303),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2708])).

tff(c_36,plain,(
    ! [C_63,B_62,A_61] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2719,plain,(
    ! [A_61,D_303] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_61,k10_relat_1('#skF_7',D_303)) ) ),
    inference(resolution,[status(thm)],[c_2716,c_36])).

tff(c_2720,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2719])).

tff(c_50,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3997,plain,(
    ! [E_424,C_427,D_426,A_425,B_428] :
      ( v1_funct_2(k5_relat_1(D_426,E_424),A_425,C_427)
      | ~ m1_subset_1(E_424,k1_zfmisc_1(k2_zfmisc_1(B_428,C_427)))
      | ~ v1_funct_2(E_424,B_428,C_427)
      | ~ v1_funct_1(E_424)
      | ~ m1_subset_1(D_426,k1_zfmisc_1(k2_zfmisc_1(A_425,B_428)))
      | ~ v1_funct_2(D_426,A_425,B_428)
      | ~ v1_funct_1(D_426)
      | v1_xboole_0(B_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4024,plain,(
    ! [D_426,A_425] :
      ( v1_funct_2(k5_relat_1(D_426,'#skF_7'),A_425,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_426,k1_zfmisc_1(k2_zfmisc_1(A_425,u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(D_426,A_425,u1_struct_0('#skF_5'))
      | ~ v1_funct_1(D_426)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_3997])).

tff(c_4054,plain,(
    ! [D_426,A_425] :
      ( v1_funct_2(k5_relat_1(D_426,'#skF_7'),A_425,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_426,k1_zfmisc_1(k2_zfmisc_1(A_425,u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(D_426,A_425,u1_struct_0('#skF_5'))
      | ~ v1_funct_1(D_426)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4024])).

tff(c_4129,plain,(
    ! [D_429,A_430] :
      ( v1_funct_2(k5_relat_1(D_429,'#skF_7'),A_430,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_429,k1_zfmisc_1(k2_zfmisc_1(A_430,u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(D_429,A_430,u1_struct_0('#skF_5'))
      | ~ v1_funct_1(D_429) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2720,c_4054])).

tff(c_4162,plain,
    ( v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_4129])).

tff(c_4181,plain,(
    v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4162])).

tff(c_4183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3448,c_4181])).

tff(c_4184,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3384])).

tff(c_4185,plain,(
    v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3384])).

tff(c_4408,plain,(
    ! [A_446,B_447,C_448] :
      ( m1_subset_1('#skF_1'(A_446,B_447,C_448),k1_zfmisc_1(u1_struct_0(B_447)))
      | v5_pre_topc(C_448,A_446,B_447)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_446),u1_struct_0(B_447))))
      | ~ v1_funct_2(C_448,u1_struct_0(A_446),u1_struct_0(B_447))
      | ~ v1_funct_1(C_448)
      | ~ l1_pre_topc(B_447)
      | ~ l1_pre_topc(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4416,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_4')
    | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_3191,c_4408])).

tff(c_4450,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3157,c_4185,c_4416])).

tff(c_4451,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3149,c_4450])).

tff(c_44,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2686,plain,(
    ! [D_300] : k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_7',D_300) = k10_relat_1('#skF_7',D_300) ),
    inference(resolution,[status(thm)],[c_48,c_2670])).

tff(c_5113,plain,(
    ! [A_471,B_472,C_473,D_474] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_471),u1_struct_0(B_472),C_473,D_474),A_471)
      | ~ v4_pre_topc(D_474,B_472)
      | ~ m1_subset_1(D_474,k1_zfmisc_1(u1_struct_0(B_472)))
      | ~ v5_pre_topc(C_473,A_471,B_472)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_471),u1_struct_0(B_472))))
      | ~ v1_funct_2(C_473,u1_struct_0(A_471),u1_struct_0(B_472))
      | ~ v1_funct_1(C_473)
      | ~ l1_pre_topc(B_472)
      | ~ l1_pre_topc(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5147,plain,(
    ! [D_474] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),'#skF_7',D_474),'#skF_5')
      | ~ v4_pre_topc(D_474,'#skF_4')
      | ~ m1_subset_1(D_474,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_5113])).

tff(c_5259,plain,(
    ! [D_475] :
      ( v4_pre_topc(k10_relat_1('#skF_7',D_475),'#skF_5')
      | ~ v4_pre_topc(D_475,'#skF_4')
      | ~ m1_subset_1(D_475,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_52,c_50,c_44,c_2686,c_5147])).

tff(c_5266,plain,
    ( v4_pre_topc(k10_relat_1('#skF_7','#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7'))),'#skF_5')
    | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4451,c_5259])).

tff(c_5290,plain,(
    v4_pre_topc(k10_relat_1('#skF_7','#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7'))),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4184,c_5266])).

tff(c_2714,plain,(
    ! [D_302] : m1_subset_1(k10_relat_1('#skF_7',D_302),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2708])).

tff(c_46,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2687,plain,(
    ! [D_300] : k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),'#skF_6',D_300) = k10_relat_1('#skF_6',D_300) ),
    inference(resolution,[status(thm)],[c_54,c_2670])).

tff(c_5149,plain,(
    ! [D_474] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),'#skF_6',D_474),'#skF_3')
      | ~ v4_pre_topc(D_474,'#skF_5')
      | ~ m1_subset_1(D_474,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v5_pre_topc('#skF_6','#skF_3','#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_5113])).

tff(c_5296,plain,(
    ! [D_476] :
      ( v4_pre_topc(k10_relat_1('#skF_6',D_476),'#skF_3')
      | ~ v4_pre_topc(D_476,'#skF_5')
      | ~ m1_subset_1(D_476,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_58,c_56,c_46,c_2687,c_5149])).

tff(c_5339,plain,(
    ! [D_477] :
      ( v4_pre_topc(k10_relat_1('#skF_6',k10_relat_1('#skF_7',D_477)),'#skF_3')
      | ~ v4_pre_topc(k10_relat_1('#skF_7',D_477),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2714,c_5296])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_82,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_86,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_32,plain,(
    ! [B_56,C_58,A_55] :
      ( k10_relat_1(k5_relat_1(B_56,C_58),A_55) = k10_relat_1(B_56,k10_relat_1(C_58,A_55))
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k8_relset_1(A_51,B_52,C_53,D_54) = k10_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3217,plain,(
    ! [D_54] : k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),k5_relat_1('#skF_6','#skF_7'),D_54) = k10_relat_1(k5_relat_1('#skF_6','#skF_7'),D_54) ),
    inference(resolution,[status(thm)],[c_3191,c_30])).

tff(c_4946,plain,(
    ! [A_466,B_467,C_468] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_466),u1_struct_0(B_467),C_468,'#skF_1'(A_466,B_467,C_468)),A_466)
      | v5_pre_topc(C_468,A_466,B_467)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_466),u1_struct_0(B_467))))
      | ~ v1_funct_2(C_468,u1_struct_0(A_466),u1_struct_0(B_467))
      | ~ v1_funct_1(C_468)
      | ~ l1_pre_topc(B_467)
      | ~ l1_pre_topc(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4958,plain,
    ( ~ v4_pre_topc(k10_relat_1(k5_relat_1('#skF_6','#skF_7'),'#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7'))),'#skF_3')
    | v5_pre_topc(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_4')
    | ~ m1_subset_1(k5_relat_1('#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k5_relat_1('#skF_6','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k5_relat_1('#skF_6','#skF_7'))
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3217,c_4946])).

tff(c_4980,plain,
    ( ~ v4_pre_topc(k10_relat_1(k5_relat_1('#skF_6','#skF_7'),'#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7'))),'#skF_3')
    | v5_pre_topc(k5_relat_1('#skF_6','#skF_7'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3157,c_4185,c_3191,c_4958])).

tff(c_4981,plain,(
    ~ v4_pre_topc(k10_relat_1(k5_relat_1('#skF_6','#skF_7'),'#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7'))),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3149,c_4980])).

tff(c_4992,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_6',k10_relat_1('#skF_7','#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')))),'#skF_3')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4981])).

tff(c_4994,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_6',k10_relat_1('#skF_7','#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7')))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_4992])).

tff(c_5342,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_7','#skF_1'('#skF_3','#skF_4',k5_relat_1('#skF_6','#skF_7'))),'#skF_5') ),
    inference(resolution,[status(thm)],[c_5339,c_4994])).

tff(c_5346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5290,c_5342])).

tff(c_5348,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2719])).

tff(c_22,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5351,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5348,c_22])).

tff(c_5359,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5351])).

tff(c_5364,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_5359])).

tff(c_5368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5364])).

%------------------------------------------------------------------------------
