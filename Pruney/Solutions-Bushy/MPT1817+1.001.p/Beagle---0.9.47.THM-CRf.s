%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1817+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:28 EST 2020

% Result     : Theorem 52.75s
% Output     : CNFRefutation 52.99s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 561 expanded)
%              Number of leaves         :   46 ( 245 expanded)
%              Depth                    :   12
%              Number of atoms          :  844 (6422 expanded)
%              Number of equality atoms :   36 ( 240 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v5_relat_1 > v4_relat_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_1 > #skF_9 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_379,negated_conjecture,(
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
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_borsuk_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & v1_borsuk_1(E,A)
                          & m1_pre_topc(E,A) )
                       => ( A = k1_tsep_1(A,D,E)
                         => ( ( v1_funct_1(C)
                              & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                              & v5_pre_topc(C,A,B)
                              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                          <=> ( v1_funct_1(k2_tmap_1(A,B,C,D))
                              & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B)
                              & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B))))
                              & v1_funct_1(k2_tmap_1(A,B,C,E))
                              & v1_funct_2(k2_tmap_1(A,B,C,E),u1_struct_0(E),u1_struct_0(B))
                              & v5_pre_topc(k2_tmap_1(A,B,C,E),E,B)
                              & m1_subset_1(k2_tmap_1(A,B,C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_tmap_1)).

tff(f_216,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_84,axiom,(
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

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_314,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_borsuk_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_borsuk_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).

tff(f_288,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( A = k1_tsep_1(A,D,E)
                          & r4_tsep_1(A,D,E) )
                       => ( ( v1_funct_1(C)
                            & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                            & v5_pre_topc(C,A,B)
                            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k2_tmap_1(A,B,C,D))
                            & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B))))
                            & v1_funct_1(k2_tmap_1(A,B,C,E))
                            & v1_funct_2(k2_tmap_1(A,B,C,E),u1_struct_0(E),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,E),E,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

tff(c_102,plain,(
    m1_pre_topc('#skF_9','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_130,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_124,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_128,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_126,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_122,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_120,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_118,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_116,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_114,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_133623,plain,(
    ! [A_3445,B_3446,C_3447,D_3448] :
      ( k2_partfun1(A_3445,B_3446,C_3447,D_3448) = k7_relat_1(C_3447,D_3448)
      | ~ m1_subset_1(C_3447,k1_zfmisc_1(k2_zfmisc_1(A_3445,B_3446)))
      | ~ v1_funct_1(C_3447) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_133625,plain,(
    ! [D_3448] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_3448) = k7_relat_1('#skF_7',D_3448)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_114,c_133623])).

tff(c_133628,plain,(
    ! [D_3448] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_3448) = k7_relat_1('#skF_7',D_3448) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_133625])).

tff(c_134545,plain,(
    ! [A_3564,B_3565,C_3566,D_3567] :
      ( k2_partfun1(u1_struct_0(A_3564),u1_struct_0(B_3565),C_3566,u1_struct_0(D_3567)) = k2_tmap_1(A_3564,B_3565,C_3566,D_3567)
      | ~ m1_pre_topc(D_3567,A_3564)
      | ~ m1_subset_1(C_3566,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3564),u1_struct_0(B_3565))))
      | ~ v1_funct_2(C_3566,u1_struct_0(A_3564),u1_struct_0(B_3565))
      | ~ v1_funct_1(C_3566)
      | ~ l1_pre_topc(B_3565)
      | ~ v2_pre_topc(B_3565)
      | v2_struct_0(B_3565)
      | ~ l1_pre_topc(A_3564)
      | ~ v2_pre_topc(A_3564)
      | v2_struct_0(A_3564) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_134562,plain,(
    ! [D_3567] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0(D_3567)) = k2_tmap_1('#skF_5','#skF_6','#skF_7',D_3567)
      | ~ m1_pre_topc(D_3567,'#skF_5')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_114,c_134545])).

tff(c_134584,plain,(
    ! [D_3567] :
      ( k7_relat_1('#skF_7',u1_struct_0(D_3567)) = k2_tmap_1('#skF_5','#skF_6','#skF_7',D_3567)
      | ~ m1_pre_topc(D_3567,'#skF_5')
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_122,c_120,c_118,c_116,c_133628,c_134562])).

tff(c_134623,plain,(
    ! [D_3568] :
      ( k7_relat_1('#skF_7',u1_struct_0(D_3568)) = k2_tmap_1('#skF_5','#skF_6','#skF_7',D_3568)
      | ~ m1_pre_topc(D_3568,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_124,c_134584])).

tff(c_133611,plain,(
    ! [A_3436,B_3437,C_3438,D_3439] :
      ( v1_funct_1(k2_partfun1(A_3436,B_3437,C_3438,D_3439))
      | ~ m1_subset_1(C_3438,k1_zfmisc_1(k2_zfmisc_1(A_3436,B_3437)))
      | ~ v1_funct_1(C_3438) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_133613,plain,(
    ! [D_3439] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_3439))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_114,c_133611])).

tff(c_133616,plain,(
    ! [D_3439] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_3439)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_133613])).

tff(c_133629,plain,(
    ! [D_3439] : v1_funct_1(k7_relat_1('#skF_7',D_3439)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133628,c_133616])).

tff(c_134659,plain,(
    ! [D_3569] :
      ( v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_3569))
      | ~ m1_pre_topc(D_3569,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134623,c_133629])).

tff(c_108,plain,(
    m1_pre_topc('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_132593,plain,(
    ! [A_3286,B_3287,C_3288,D_3289] :
      ( k2_partfun1(A_3286,B_3287,C_3288,D_3289) = k7_relat_1(C_3288,D_3289)
      | ~ m1_subset_1(C_3288,k1_zfmisc_1(k2_zfmisc_1(A_3286,B_3287)))
      | ~ v1_funct_1(C_3288) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_132595,plain,(
    ! [D_3289] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_3289) = k7_relat_1('#skF_7',D_3289)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_114,c_132593])).

tff(c_132598,plain,(
    ! [D_3289] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_3289) = k7_relat_1('#skF_7',D_3289) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_132595])).

tff(c_133456,plain,(
    ! [A_3407,B_3408,C_3409,D_3410] :
      ( k2_partfun1(u1_struct_0(A_3407),u1_struct_0(B_3408),C_3409,u1_struct_0(D_3410)) = k2_tmap_1(A_3407,B_3408,C_3409,D_3410)
      | ~ m1_pre_topc(D_3410,A_3407)
      | ~ m1_subset_1(C_3409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3407),u1_struct_0(B_3408))))
      | ~ v1_funct_2(C_3409,u1_struct_0(A_3407),u1_struct_0(B_3408))
      | ~ v1_funct_1(C_3409)
      | ~ l1_pre_topc(B_3408)
      | ~ v2_pre_topc(B_3408)
      | v2_struct_0(B_3408)
      | ~ l1_pre_topc(A_3407)
      | ~ v2_pre_topc(A_3407)
      | v2_struct_0(A_3407) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_133473,plain,(
    ! [D_3410] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0(D_3410)) = k2_tmap_1('#skF_5','#skF_6','#skF_7',D_3410)
      | ~ m1_pre_topc(D_3410,'#skF_5')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_114,c_133456])).

tff(c_133495,plain,(
    ! [D_3410] :
      ( k7_relat_1('#skF_7',u1_struct_0(D_3410)) = k2_tmap_1('#skF_5','#skF_6','#skF_7',D_3410)
      | ~ m1_pre_topc(D_3410,'#skF_5')
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_122,c_120,c_118,c_116,c_132598,c_133473])).

tff(c_133497,plain,(
    ! [D_3411] :
      ( k7_relat_1('#skF_7',u1_struct_0(D_3411)) = k2_tmap_1('#skF_5','#skF_6','#skF_7',D_3411)
      | ~ m1_pre_topc(D_3411,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_124,c_133495])).

tff(c_132584,plain,(
    ! [A_3277,B_3278,C_3279,D_3280] :
      ( v1_funct_1(k2_partfun1(A_3277,B_3278,C_3279,D_3280))
      | ~ m1_subset_1(C_3279,k1_zfmisc_1(k2_zfmisc_1(A_3277,B_3278)))
      | ~ v1_funct_1(C_3279) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_132586,plain,(
    ! [D_3280] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_3280))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_114,c_132584])).

tff(c_132589,plain,(
    ! [D_3280] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_3280)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_132586])).

tff(c_132600,plain,(
    ! [D_3280] : v1_funct_1(k7_relat_1('#skF_7',D_3280)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132598,c_132589])).

tff(c_133533,plain,(
    ! [D_3412] :
      ( v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_3412))
      | ~ m1_pre_topc(D_3412,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133497,c_132600])).

tff(c_110,plain,(
    v1_borsuk_1('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_104,plain,(
    v1_borsuk_1('#skF_9','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_98,plain,(
    ! [A_94,B_98,C_100] :
      ( r4_tsep_1(A_94,B_98,C_100)
      | ~ m1_pre_topc(C_100,A_94)
      | ~ v1_borsuk_1(C_100,A_94)
      | ~ m1_pre_topc(B_98,A_94)
      | ~ v1_borsuk_1(B_98,A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_112,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_100,plain,(
    k1_tsep_1('#skF_5','#skF_8','#skF_9') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_216,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_321,plain,(
    v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_206,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_369,plain,(
    v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_196,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_347,plain,(
    v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_186,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_380,plain,(
    m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_106,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_176,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_301,plain,(
    v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_166,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_379,plain,(
    v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_156,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_350,plain,(
    v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_146,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_391,plain,(
    m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_132,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'))
    | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_379])).

tff(c_230,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'))
    | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_132])).

tff(c_240,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'))
    | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_230])).

tff(c_250,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'))
    | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_240])).

tff(c_590,plain,(
    ~ v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_369,c_347,c_380,c_301,c_379,c_350,c_391,c_250])).

tff(c_2802,plain,(
    ! [E_385,C_382,D_383,B_381,A_384] :
      ( v5_pre_topc(C_382,A_384,B_381)
      | ~ m1_subset_1(k2_tmap_1(A_384,B_381,C_382,E_385),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_385),u1_struct_0(B_381))))
      | ~ v5_pre_topc(k2_tmap_1(A_384,B_381,C_382,E_385),E_385,B_381)
      | ~ v1_funct_2(k2_tmap_1(A_384,B_381,C_382,E_385),u1_struct_0(E_385),u1_struct_0(B_381))
      | ~ v1_funct_1(k2_tmap_1(A_384,B_381,C_382,E_385))
      | ~ m1_subset_1(k2_tmap_1(A_384,B_381,C_382,D_383),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_383),u1_struct_0(B_381))))
      | ~ v5_pre_topc(k2_tmap_1(A_384,B_381,C_382,D_383),D_383,B_381)
      | ~ v1_funct_2(k2_tmap_1(A_384,B_381,C_382,D_383),u1_struct_0(D_383),u1_struct_0(B_381))
      | ~ v1_funct_1(k2_tmap_1(A_384,B_381,C_382,D_383))
      | ~ r4_tsep_1(A_384,D_383,E_385)
      | k1_tsep_1(A_384,D_383,E_385) != A_384
      | ~ m1_pre_topc(E_385,A_384)
      | v2_struct_0(E_385)
      | ~ m1_pre_topc(D_383,A_384)
      | v2_struct_0(D_383)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_384),u1_struct_0(B_381))))
      | ~ v1_funct_2(C_382,u1_struct_0(A_384),u1_struct_0(B_381))
      | ~ v1_funct_1(C_382)
      | ~ l1_pre_topc(B_381)
      | ~ v2_pre_topc(B_381)
      | v2_struct_0(B_381)
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384)
      | v2_struct_0(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_2809,plain,(
    ! [D_383] :
      ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
      | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6')
      | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'))
      | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_383),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_383),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_383),D_383,'#skF_6')
      | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_383),u1_struct_0(D_383),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_383))
      | ~ r4_tsep_1('#skF_5',D_383,'#skF_9')
      | k1_tsep_1('#skF_5',D_383,'#skF_9') != '#skF_5'
      | ~ m1_pre_topc('#skF_9','#skF_5')
      | v2_struct_0('#skF_9')
      | ~ m1_pre_topc(D_383,'#skF_5')
      | v2_struct_0(D_383)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_391,c_2802])).

tff(c_2819,plain,(
    ! [D_383] :
      ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
      | ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_383),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_383),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_383),D_383,'#skF_6')
      | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_383),u1_struct_0(D_383),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_383))
      | ~ r4_tsep_1('#skF_5',D_383,'#skF_9')
      | k1_tsep_1('#skF_5',D_383,'#skF_9') != '#skF_5'
      | v2_struct_0('#skF_9')
      | ~ m1_pre_topc(D_383,'#skF_5')
      | v2_struct_0(D_383)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_122,c_120,c_118,c_116,c_114,c_102,c_301,c_379,c_350,c_2809])).

tff(c_9585,plain,(
    ! [D_497] :
      ( ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_497),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_497),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_497),D_497,'#skF_6')
      | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_497),u1_struct_0(D_497),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7',D_497))
      | ~ r4_tsep_1('#skF_5',D_497,'#skF_9')
      | k1_tsep_1('#skF_5',D_497,'#skF_9') != '#skF_5'
      | ~ m1_pre_topc(D_497,'#skF_5')
      | v2_struct_0(D_497) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_124,c_106,c_590,c_2819])).

tff(c_9599,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6')
    | ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ r4_tsep_1('#skF_5','#skF_8','#skF_9')
    | k1_tsep_1('#skF_5','#skF_8','#skF_9') != '#skF_5'
    | ~ m1_pre_topc('#skF_8','#skF_5')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_380,c_9585])).

tff(c_9613,plain,
    ( ~ r4_tsep_1('#skF_5','#skF_8','#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_100,c_321,c_369,c_347,c_9599])).

tff(c_9614,plain,(
    ~ r4_tsep_1('#skF_5','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_9613])).

tff(c_9617,plain,
    ( ~ m1_pre_topc('#skF_9','#skF_5')
    | ~ v1_borsuk_1('#skF_9','#skF_5')
    | ~ m1_pre_topc('#skF_8','#skF_5')
    | ~ v1_borsuk_1('#skF_8','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_9614])).

tff(c_9620,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_110,c_108,c_104,c_102,c_9617])).

tff(c_9622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_9620])).

tff(c_9623,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_11610,plain,(
    ! [B_686,A_689,D_688,E_690,C_687] :
      ( m1_subset_1(k2_tmap_1(A_689,B_686,C_687,E_690),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_690),u1_struct_0(B_686))))
      | ~ v5_pre_topc(C_687,A_689,B_686)
      | ~ r4_tsep_1(A_689,D_688,E_690)
      | k1_tsep_1(A_689,D_688,E_690) != A_689
      | ~ m1_pre_topc(E_690,A_689)
      | v2_struct_0(E_690)
      | ~ m1_pre_topc(D_688,A_689)
      | v2_struct_0(D_688)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_689),u1_struct_0(B_686))))
      | ~ v1_funct_2(C_687,u1_struct_0(A_689),u1_struct_0(B_686))
      | ~ v1_funct_1(C_687)
      | ~ l1_pre_topc(B_686)
      | ~ v2_pre_topc(B_686)
      | v2_struct_0(B_686)
      | ~ l1_pre_topc(A_689)
      | ~ v2_pre_topc(A_689)
      | v2_struct_0(A_689) ) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_20486,plain,(
    ! [C_870,A_868,B_871,B_872,C_869] :
      ( m1_subset_1(k2_tmap_1(A_868,B_872,C_869,C_870),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_870),u1_struct_0(B_872))))
      | ~ v5_pre_topc(C_869,A_868,B_872)
      | k1_tsep_1(A_868,B_871,C_870) != A_868
      | v2_struct_0(C_870)
      | v2_struct_0(B_871)
      | ~ m1_subset_1(C_869,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_868),u1_struct_0(B_872))))
      | ~ v1_funct_2(C_869,u1_struct_0(A_868),u1_struct_0(B_872))
      | ~ v1_funct_1(C_869)
      | ~ l1_pre_topc(B_872)
      | ~ v2_pre_topc(B_872)
      | v2_struct_0(B_872)
      | ~ m1_pre_topc(C_870,A_868)
      | ~ v1_borsuk_1(C_870,A_868)
      | ~ m1_pre_topc(B_871,A_868)
      | ~ v1_borsuk_1(B_871,A_868)
      | ~ l1_pre_topc(A_868)
      | ~ v2_pre_topc(A_868)
      | v2_struct_0(A_868) ) ),
    inference(resolution,[status(thm)],[c_98,c_11610])).

tff(c_20584,plain,(
    ! [B_872,C_869] :
      ( m1_subset_1(k2_tmap_1('#skF_5',B_872,C_869,'#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0(B_872))))
      | ~ v5_pre_topc(C_869,'#skF_5',B_872)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_869,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_872))))
      | ~ v1_funct_2(C_869,u1_struct_0('#skF_5'),u1_struct_0(B_872))
      | ~ v1_funct_1(C_869)
      | ~ l1_pre_topc(B_872)
      | ~ v2_pre_topc(B_872)
      | v2_struct_0(B_872)
      | ~ m1_pre_topc('#skF_9','#skF_5')
      | ~ v1_borsuk_1('#skF_9','#skF_5')
      | ~ m1_pre_topc('#skF_8','#skF_5')
      | ~ v1_borsuk_1('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_20486])).

tff(c_20714,plain,(
    ! [B_872,C_869] :
      ( m1_subset_1(k2_tmap_1('#skF_5',B_872,C_869,'#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0(B_872))))
      | ~ v5_pre_topc(C_869,'#skF_5',B_872)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_869,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_872))))
      | ~ v1_funct_2(C_869,u1_struct_0('#skF_5'),u1_struct_0(B_872))
      | ~ v1_funct_1(C_869)
      | ~ l1_pre_topc(B_872)
      | ~ v2_pre_topc(B_872)
      | v2_struct_0(B_872)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_110,c_108,c_104,c_102,c_20584])).

tff(c_32623,plain,(
    ! [B_983,C_984] :
      ( m1_subset_1(k2_tmap_1('#skF_5',B_983,C_984,'#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0(B_983))))
      | ~ v5_pre_topc(C_984,'#skF_5',B_983)
      | ~ m1_subset_1(C_984,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_983))))
      | ~ v1_funct_2(C_984,u1_struct_0('#skF_5'),u1_struct_0(B_983))
      | ~ v1_funct_1(C_984)
      | ~ l1_pre_topc(B_983)
      | ~ v2_pre_topc(B_983)
      | v2_struct_0(B_983) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_112,c_106,c_20714])).

tff(c_9624,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_9'),u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_32644,plain,
    ( ~ v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_32623,c_9624])).

tff(c_32669,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_116,c_114,c_9623,c_32644])).

tff(c_32671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_32669])).

tff(c_32672,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_34513,plain,(
    ! [C_1189,D_1190,B_1188,E_1192,A_1191] :
      ( m1_subset_1(k2_tmap_1(A_1191,B_1188,C_1189,D_1190),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1190),u1_struct_0(B_1188))))
      | ~ v5_pre_topc(C_1189,A_1191,B_1188)
      | ~ r4_tsep_1(A_1191,D_1190,E_1192)
      | k1_tsep_1(A_1191,D_1190,E_1192) != A_1191
      | ~ m1_pre_topc(E_1192,A_1191)
      | v2_struct_0(E_1192)
      | ~ m1_pre_topc(D_1190,A_1191)
      | v2_struct_0(D_1190)
      | ~ m1_subset_1(C_1189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1191),u1_struct_0(B_1188))))
      | ~ v1_funct_2(C_1189,u1_struct_0(A_1191),u1_struct_0(B_1188))
      | ~ v1_funct_1(C_1189)
      | ~ l1_pre_topc(B_1188)
      | ~ v2_pre_topc(B_1188)
      | v2_struct_0(B_1188)
      | ~ l1_pre_topc(A_1191)
      | ~ v2_pre_topc(A_1191)
      | v2_struct_0(A_1191) ) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_43217,plain,(
    ! [C_1370,B_1369,B_1371,C_1372,A_1368] :
      ( m1_subset_1(k2_tmap_1(A_1368,B_1369,C_1372,B_1371),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1371),u1_struct_0(B_1369))))
      | ~ v5_pre_topc(C_1372,A_1368,B_1369)
      | k1_tsep_1(A_1368,B_1371,C_1370) != A_1368
      | v2_struct_0(C_1370)
      | v2_struct_0(B_1371)
      | ~ m1_subset_1(C_1372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1368),u1_struct_0(B_1369))))
      | ~ v1_funct_2(C_1372,u1_struct_0(A_1368),u1_struct_0(B_1369))
      | ~ v1_funct_1(C_1372)
      | ~ l1_pre_topc(B_1369)
      | ~ v2_pre_topc(B_1369)
      | v2_struct_0(B_1369)
      | ~ m1_pre_topc(C_1370,A_1368)
      | ~ v1_borsuk_1(C_1370,A_1368)
      | ~ m1_pre_topc(B_1371,A_1368)
      | ~ v1_borsuk_1(B_1371,A_1368)
      | ~ l1_pre_topc(A_1368)
      | ~ v2_pre_topc(A_1368)
      | v2_struct_0(A_1368) ) ),
    inference(resolution,[status(thm)],[c_98,c_34513])).

tff(c_43297,plain,(
    ! [B_1369,C_1372] :
      ( m1_subset_1(k2_tmap_1('#skF_5',B_1369,C_1372,'#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(B_1369))))
      | ~ v5_pre_topc(C_1372,'#skF_5',B_1369)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_1372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_1369))))
      | ~ v1_funct_2(C_1372,u1_struct_0('#skF_5'),u1_struct_0(B_1369))
      | ~ v1_funct_1(C_1372)
      | ~ l1_pre_topc(B_1369)
      | ~ v2_pre_topc(B_1369)
      | v2_struct_0(B_1369)
      | ~ m1_pre_topc('#skF_9','#skF_5')
      | ~ v1_borsuk_1('#skF_9','#skF_5')
      | ~ m1_pre_topc('#skF_8','#skF_5')
      | ~ v1_borsuk_1('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_43217])).

tff(c_43400,plain,(
    ! [B_1369,C_1372] :
      ( m1_subset_1(k2_tmap_1('#skF_5',B_1369,C_1372,'#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(B_1369))))
      | ~ v5_pre_topc(C_1372,'#skF_5',B_1369)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_1372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_1369))))
      | ~ v1_funct_2(C_1372,u1_struct_0('#skF_5'),u1_struct_0(B_1369))
      | ~ v1_funct_1(C_1372)
      | ~ l1_pre_topc(B_1369)
      | ~ v2_pre_topc(B_1369)
      | v2_struct_0(B_1369)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_110,c_108,c_104,c_102,c_43297])).

tff(c_53926,plain,(
    ! [B_1462,C_1463] :
      ( m1_subset_1(k2_tmap_1('#skF_5',B_1462,C_1463,'#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0(B_1462))))
      | ~ v5_pre_topc(C_1463,'#skF_5',B_1462)
      | ~ m1_subset_1(C_1463,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_1462))))
      | ~ v1_funct_2(C_1463,u1_struct_0('#skF_5'),u1_struct_0(B_1462))
      | ~ v1_funct_1(C_1463)
      | ~ l1_pre_topc(B_1462)
      | ~ v2_pre_topc(B_1462)
      | v2_struct_0(B_1462) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_112,c_106,c_43400])).

tff(c_32673,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_53947,plain,
    ( ~ v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_53926,c_32673])).

tff(c_53972,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_116,c_114,c_32672,c_53947])).

tff(c_53974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_53972])).

tff(c_53976,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_53975,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_55421,plain,(
    ! [D_1643,E_1645,A_1644,C_1642,B_1641] :
      ( v1_funct_2(k2_tmap_1(A_1644,B_1641,C_1642,E_1645),u1_struct_0(E_1645),u1_struct_0(B_1641))
      | ~ v5_pre_topc(C_1642,A_1644,B_1641)
      | ~ r4_tsep_1(A_1644,D_1643,E_1645)
      | k1_tsep_1(A_1644,D_1643,E_1645) != A_1644
      | ~ m1_pre_topc(E_1645,A_1644)
      | v2_struct_0(E_1645)
      | ~ m1_pre_topc(D_1643,A_1644)
      | v2_struct_0(D_1643)
      | ~ m1_subset_1(C_1642,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1644),u1_struct_0(B_1641))))
      | ~ v1_funct_2(C_1642,u1_struct_0(A_1644),u1_struct_0(B_1641))
      | ~ v1_funct_1(C_1642)
      | ~ l1_pre_topc(B_1641)
      | ~ v2_pre_topc(B_1641)
      | v2_struct_0(B_1641)
      | ~ l1_pre_topc(A_1644)
      | ~ v2_pre_topc(A_1644)
      | v2_struct_0(A_1644) ) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_64129,plain,(
    ! [B_1840,C_1838,B_1841,A_1837,C_1839] :
      ( v1_funct_2(k2_tmap_1(A_1837,B_1840,C_1839,C_1838),u1_struct_0(C_1838),u1_struct_0(B_1840))
      | ~ v5_pre_topc(C_1839,A_1837,B_1840)
      | k1_tsep_1(A_1837,B_1841,C_1838) != A_1837
      | v2_struct_0(C_1838)
      | v2_struct_0(B_1841)
      | ~ m1_subset_1(C_1839,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1837),u1_struct_0(B_1840))))
      | ~ v1_funct_2(C_1839,u1_struct_0(A_1837),u1_struct_0(B_1840))
      | ~ v1_funct_1(C_1839)
      | ~ l1_pre_topc(B_1840)
      | ~ v2_pre_topc(B_1840)
      | v2_struct_0(B_1840)
      | ~ m1_pre_topc(C_1838,A_1837)
      | ~ v1_borsuk_1(C_1838,A_1837)
      | ~ m1_pre_topc(B_1841,A_1837)
      | ~ v1_borsuk_1(B_1841,A_1837)
      | ~ l1_pre_topc(A_1837)
      | ~ v2_pre_topc(A_1837)
      | v2_struct_0(A_1837) ) ),
    inference(resolution,[status(thm)],[c_98,c_55421])).

tff(c_64209,plain,(
    ! [B_1840,C_1839] :
      ( v1_funct_2(k2_tmap_1('#skF_5',B_1840,C_1839,'#skF_9'),u1_struct_0('#skF_9'),u1_struct_0(B_1840))
      | ~ v5_pre_topc(C_1839,'#skF_5',B_1840)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_1839,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_1840))))
      | ~ v1_funct_2(C_1839,u1_struct_0('#skF_5'),u1_struct_0(B_1840))
      | ~ v1_funct_1(C_1839)
      | ~ l1_pre_topc(B_1840)
      | ~ v2_pre_topc(B_1840)
      | v2_struct_0(B_1840)
      | ~ m1_pre_topc('#skF_9','#skF_5')
      | ~ v1_borsuk_1('#skF_9','#skF_5')
      | ~ m1_pre_topc('#skF_8','#skF_5')
      | ~ v1_borsuk_1('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_64129])).

tff(c_64312,plain,(
    ! [B_1840,C_1839] :
      ( v1_funct_2(k2_tmap_1('#skF_5',B_1840,C_1839,'#skF_9'),u1_struct_0('#skF_9'),u1_struct_0(B_1840))
      | ~ v5_pre_topc(C_1839,'#skF_5',B_1840)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_1839,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_1840))))
      | ~ v1_funct_2(C_1839,u1_struct_0('#skF_5'),u1_struct_0(B_1840))
      | ~ v1_funct_1(C_1839)
      | ~ l1_pre_topc(B_1840)
      | ~ v2_pre_topc(B_1840)
      | v2_struct_0(B_1840)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_110,c_108,c_104,c_102,c_64209])).

tff(c_73302,plain,(
    ! [B_1925,C_1926] :
      ( v1_funct_2(k2_tmap_1('#skF_5',B_1925,C_1926,'#skF_9'),u1_struct_0('#skF_9'),u1_struct_0(B_1925))
      | ~ v5_pre_topc(C_1926,'#skF_5',B_1925)
      | ~ m1_subset_1(C_1926,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_1925))))
      | ~ v1_funct_2(C_1926,u1_struct_0('#skF_5'),u1_struct_0(B_1925))
      | ~ v1_funct_1(C_1926)
      | ~ l1_pre_topc(B_1925)
      | ~ v2_pre_topc(B_1925)
      | v2_struct_0(B_1925) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_112,c_106,c_64312])).

tff(c_73331,plain,
    ( v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_73302])).

tff(c_73371,plain,
    ( v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),u1_struct_0('#skF_9'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_116,c_53975,c_73331])).

tff(c_73373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_53976,c_73371])).

tff(c_73375,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_73374,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_74844,plain,(
    ! [C_2098,A_2100,B_2097,E_2101,D_2099] :
      ( v1_funct_2(k2_tmap_1(A_2100,B_2097,C_2098,D_2099),u1_struct_0(D_2099),u1_struct_0(B_2097))
      | ~ v5_pre_topc(C_2098,A_2100,B_2097)
      | ~ r4_tsep_1(A_2100,D_2099,E_2101)
      | k1_tsep_1(A_2100,D_2099,E_2101) != A_2100
      | ~ m1_pre_topc(E_2101,A_2100)
      | v2_struct_0(E_2101)
      | ~ m1_pre_topc(D_2099,A_2100)
      | v2_struct_0(D_2099)
      | ~ m1_subset_1(C_2098,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2100),u1_struct_0(B_2097))))
      | ~ v1_funct_2(C_2098,u1_struct_0(A_2100),u1_struct_0(B_2097))
      | ~ v1_funct_1(C_2098)
      | ~ l1_pre_topc(B_2097)
      | ~ v2_pre_topc(B_2097)
      | v2_struct_0(B_2097)
      | ~ l1_pre_topc(A_2100)
      | ~ v2_pre_topc(A_2100)
      | v2_struct_0(A_2100) ) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_82278,plain,(
    ! [B_2276,C_2274,B_2275,C_2273,A_2272] :
      ( v1_funct_2(k2_tmap_1(A_2272,B_2275,C_2273,B_2276),u1_struct_0(B_2276),u1_struct_0(B_2275))
      | ~ v5_pre_topc(C_2273,A_2272,B_2275)
      | k1_tsep_1(A_2272,B_2276,C_2274) != A_2272
      | v2_struct_0(C_2274)
      | v2_struct_0(B_2276)
      | ~ m1_subset_1(C_2273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2272),u1_struct_0(B_2275))))
      | ~ v1_funct_2(C_2273,u1_struct_0(A_2272),u1_struct_0(B_2275))
      | ~ v1_funct_1(C_2273)
      | ~ l1_pre_topc(B_2275)
      | ~ v2_pre_topc(B_2275)
      | v2_struct_0(B_2275)
      | ~ m1_pre_topc(C_2274,A_2272)
      | ~ v1_borsuk_1(C_2274,A_2272)
      | ~ m1_pre_topc(B_2276,A_2272)
      | ~ v1_borsuk_1(B_2276,A_2272)
      | ~ l1_pre_topc(A_2272)
      | ~ v2_pre_topc(A_2272)
      | v2_struct_0(A_2272) ) ),
    inference(resolution,[status(thm)],[c_98,c_74844])).

tff(c_82360,plain,(
    ! [B_2275,C_2273] :
      ( v1_funct_2(k2_tmap_1('#skF_5',B_2275,C_2273,'#skF_8'),u1_struct_0('#skF_8'),u1_struct_0(B_2275))
      | ~ v5_pre_topc(C_2273,'#skF_5',B_2275)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_2273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_2275))))
      | ~ v1_funct_2(C_2273,u1_struct_0('#skF_5'),u1_struct_0(B_2275))
      | ~ v1_funct_1(C_2273)
      | ~ l1_pre_topc(B_2275)
      | ~ v2_pre_topc(B_2275)
      | v2_struct_0(B_2275)
      | ~ m1_pre_topc('#skF_9','#skF_5')
      | ~ v1_borsuk_1('#skF_9','#skF_5')
      | ~ m1_pre_topc('#skF_8','#skF_5')
      | ~ v1_borsuk_1('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_82278])).

tff(c_82466,plain,(
    ! [B_2275,C_2273] :
      ( v1_funct_2(k2_tmap_1('#skF_5',B_2275,C_2273,'#skF_8'),u1_struct_0('#skF_8'),u1_struct_0(B_2275))
      | ~ v5_pre_topc(C_2273,'#skF_5',B_2275)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_2273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_2275))))
      | ~ v1_funct_2(C_2273,u1_struct_0('#skF_5'),u1_struct_0(B_2275))
      | ~ v1_funct_1(C_2273)
      | ~ l1_pre_topc(B_2275)
      | ~ v2_pre_topc(B_2275)
      | v2_struct_0(B_2275)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_110,c_108,c_104,c_102,c_82360])).

tff(c_93210,plain,(
    ! [B_2373,C_2374] :
      ( v1_funct_2(k2_tmap_1('#skF_5',B_2373,C_2374,'#skF_8'),u1_struct_0('#skF_8'),u1_struct_0(B_2373))
      | ~ v5_pre_topc(C_2374,'#skF_5',B_2373)
      | ~ m1_subset_1(C_2374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_2373))))
      | ~ v1_funct_2(C_2374,u1_struct_0('#skF_5'),u1_struct_0(B_2373))
      | ~ v1_funct_1(C_2374)
      | ~ l1_pre_topc(B_2373)
      | ~ v2_pre_topc(B_2373)
      | v2_struct_0(B_2373) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_112,c_106,c_82466])).

tff(c_93237,plain,
    ( v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_93210])).

tff(c_93273,plain,
    ( v1_funct_2(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),u1_struct_0('#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_116,c_73374,c_93237])).

tff(c_93275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_73375,c_93273])).

tff(c_93277,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_93276,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_94771,plain,(
    ! [D_2552,A_2553,C_2551,E_2554,B_2550] :
      ( v5_pre_topc(k2_tmap_1(A_2553,B_2550,C_2551,E_2554),E_2554,B_2550)
      | ~ v5_pre_topc(C_2551,A_2553,B_2550)
      | ~ r4_tsep_1(A_2553,D_2552,E_2554)
      | k1_tsep_1(A_2553,D_2552,E_2554) != A_2553
      | ~ m1_pre_topc(E_2554,A_2553)
      | v2_struct_0(E_2554)
      | ~ m1_pre_topc(D_2552,A_2553)
      | v2_struct_0(D_2552)
      | ~ m1_subset_1(C_2551,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2553),u1_struct_0(B_2550))))
      | ~ v1_funct_2(C_2551,u1_struct_0(A_2553),u1_struct_0(B_2550))
      | ~ v1_funct_1(C_2551)
      | ~ l1_pre_topc(B_2550)
      | ~ v2_pre_topc(B_2550)
      | v2_struct_0(B_2550)
      | ~ l1_pre_topc(A_2553)
      | ~ v2_pre_topc(A_2553)
      | v2_struct_0(A_2553) ) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_103070,plain,(
    ! [B_2737,A_2734,C_2735,B_2738,C_2736] :
      ( v5_pre_topc(k2_tmap_1(A_2734,B_2737,C_2735,C_2736),C_2736,B_2737)
      | ~ v5_pre_topc(C_2735,A_2734,B_2737)
      | k1_tsep_1(A_2734,B_2738,C_2736) != A_2734
      | v2_struct_0(C_2736)
      | v2_struct_0(B_2738)
      | ~ m1_subset_1(C_2735,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2734),u1_struct_0(B_2737))))
      | ~ v1_funct_2(C_2735,u1_struct_0(A_2734),u1_struct_0(B_2737))
      | ~ v1_funct_1(C_2735)
      | ~ l1_pre_topc(B_2737)
      | ~ v2_pre_topc(B_2737)
      | v2_struct_0(B_2737)
      | ~ m1_pre_topc(C_2736,A_2734)
      | ~ v1_borsuk_1(C_2736,A_2734)
      | ~ m1_pre_topc(B_2738,A_2734)
      | ~ v1_borsuk_1(B_2738,A_2734)
      | ~ l1_pre_topc(A_2734)
      | ~ v2_pre_topc(A_2734)
      | v2_struct_0(A_2734) ) ),
    inference(resolution,[status(thm)],[c_98,c_94771])).

tff(c_103152,plain,(
    ! [B_2737,C_2735] :
      ( v5_pre_topc(k2_tmap_1('#skF_5',B_2737,C_2735,'#skF_9'),'#skF_9',B_2737)
      | ~ v5_pre_topc(C_2735,'#skF_5',B_2737)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_2735,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_2737))))
      | ~ v1_funct_2(C_2735,u1_struct_0('#skF_5'),u1_struct_0(B_2737))
      | ~ v1_funct_1(C_2735)
      | ~ l1_pre_topc(B_2737)
      | ~ v2_pre_topc(B_2737)
      | v2_struct_0(B_2737)
      | ~ m1_pre_topc('#skF_9','#skF_5')
      | ~ v1_borsuk_1('#skF_9','#skF_5')
      | ~ m1_pre_topc('#skF_8','#skF_5')
      | ~ v1_borsuk_1('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_103070])).

tff(c_103258,plain,(
    ! [B_2737,C_2735] :
      ( v5_pre_topc(k2_tmap_1('#skF_5',B_2737,C_2735,'#skF_9'),'#skF_9',B_2737)
      | ~ v5_pre_topc(C_2735,'#skF_5',B_2737)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_2735,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_2737))))
      | ~ v1_funct_2(C_2735,u1_struct_0('#skF_5'),u1_struct_0(B_2737))
      | ~ v1_funct_1(C_2735)
      | ~ l1_pre_topc(B_2737)
      | ~ v2_pre_topc(B_2737)
      | v2_struct_0(B_2737)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_110,c_108,c_104,c_102,c_103152])).

tff(c_114296,plain,(
    ! [B_2827,C_2828] :
      ( v5_pre_topc(k2_tmap_1('#skF_5',B_2827,C_2828,'#skF_9'),'#skF_9',B_2827)
      | ~ v5_pre_topc(C_2828,'#skF_5',B_2827)
      | ~ m1_subset_1(C_2828,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_2827))))
      | ~ v1_funct_2(C_2828,u1_struct_0('#skF_5'),u1_struct_0(B_2827))
      | ~ v1_funct_1(C_2828)
      | ~ l1_pre_topc(B_2827)
      | ~ v2_pre_topc(B_2827)
      | v2_struct_0(B_2827) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_112,c_106,c_103258])).

tff(c_114323,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6')
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_114296])).

tff(c_114359,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9'),'#skF_9','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_116,c_93276,c_114323])).

tff(c_114361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_93277,c_114359])).

tff(c_114363,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_114362,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_115752,plain,(
    ! [A_2997,E_2998,C_2995,D_2996,B_2994] :
      ( v5_pre_topc(k2_tmap_1(A_2997,B_2994,C_2995,D_2996),D_2996,B_2994)
      | ~ v5_pre_topc(C_2995,A_2997,B_2994)
      | ~ r4_tsep_1(A_2997,D_2996,E_2998)
      | k1_tsep_1(A_2997,D_2996,E_2998) != A_2997
      | ~ m1_pre_topc(E_2998,A_2997)
      | v2_struct_0(E_2998)
      | ~ m1_pre_topc(D_2996,A_2997)
      | v2_struct_0(D_2996)
      | ~ m1_subset_1(C_2995,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2997),u1_struct_0(B_2994))))
      | ~ v1_funct_2(C_2995,u1_struct_0(A_2997),u1_struct_0(B_2994))
      | ~ v1_funct_1(C_2995)
      | ~ l1_pre_topc(B_2994)
      | ~ v2_pre_topc(B_2994)
      | v2_struct_0(B_2994)
      | ~ l1_pre_topc(A_2997)
      | ~ v2_pre_topc(A_2997)
      | v2_struct_0(A_2997) ) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_122047,plain,(
    ! [B_3151,B_3148,C_3150,C_3149,A_3147] :
      ( v5_pre_topc(k2_tmap_1(A_3147,B_3148,C_3149,B_3151),B_3151,B_3148)
      | ~ v5_pre_topc(C_3149,A_3147,B_3148)
      | k1_tsep_1(A_3147,B_3151,C_3150) != A_3147
      | v2_struct_0(C_3150)
      | v2_struct_0(B_3151)
      | ~ m1_subset_1(C_3149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3147),u1_struct_0(B_3148))))
      | ~ v1_funct_2(C_3149,u1_struct_0(A_3147),u1_struct_0(B_3148))
      | ~ v1_funct_1(C_3149)
      | ~ l1_pre_topc(B_3148)
      | ~ v2_pre_topc(B_3148)
      | v2_struct_0(B_3148)
      | ~ m1_pre_topc(C_3150,A_3147)
      | ~ v1_borsuk_1(C_3150,A_3147)
      | ~ m1_pre_topc(B_3151,A_3147)
      | ~ v1_borsuk_1(B_3151,A_3147)
      | ~ l1_pre_topc(A_3147)
      | ~ v2_pre_topc(A_3147)
      | v2_struct_0(A_3147) ) ),
    inference(resolution,[status(thm)],[c_98,c_115752])).

tff(c_122133,plain,(
    ! [B_3148,C_3149] :
      ( v5_pre_topc(k2_tmap_1('#skF_5',B_3148,C_3149,'#skF_8'),'#skF_8',B_3148)
      | ~ v5_pre_topc(C_3149,'#skF_5',B_3148)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_3149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_3148))))
      | ~ v1_funct_2(C_3149,u1_struct_0('#skF_5'),u1_struct_0(B_3148))
      | ~ v1_funct_1(C_3149)
      | ~ l1_pre_topc(B_3148)
      | ~ v2_pre_topc(B_3148)
      | v2_struct_0(B_3148)
      | ~ m1_pre_topc('#skF_9','#skF_5')
      | ~ v1_borsuk_1('#skF_9','#skF_5')
      | ~ m1_pre_topc('#skF_8','#skF_5')
      | ~ v1_borsuk_1('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_122047])).

tff(c_122245,plain,(
    ! [B_3148,C_3149] :
      ( v5_pre_topc(k2_tmap_1('#skF_5',B_3148,C_3149,'#skF_8'),'#skF_8',B_3148)
      | ~ v5_pre_topc(C_3149,'#skF_5',B_3148)
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1(C_3149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_3148))))
      | ~ v1_funct_2(C_3149,u1_struct_0('#skF_5'),u1_struct_0(B_3148))
      | ~ v1_funct_1(C_3149)
      | ~ l1_pre_topc(B_3148)
      | ~ v2_pre_topc(B_3148)
      | v2_struct_0(B_3148)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_110,c_108,c_104,c_102,c_122133])).

tff(c_132473,plain,(
    ! [B_3261,C_3262] :
      ( v5_pre_topc(k2_tmap_1('#skF_5',B_3261,C_3262,'#skF_8'),'#skF_8',B_3261)
      | ~ v5_pre_topc(C_3262,'#skF_5',B_3261)
      | ~ m1_subset_1(C_3262,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_3261))))
      | ~ v1_funct_2(C_3262,u1_struct_0('#skF_5'),u1_struct_0(B_3261))
      | ~ v1_funct_1(C_3262)
      | ~ l1_pre_topc(B_3261)
      | ~ v2_pre_topc(B_3261)
      | v2_struct_0(B_3261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_112,c_106,c_122245])).

tff(c_132498,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6')
    | ~ v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_132473])).

tff(c_132530,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_120,c_118,c_116,c_114362,c_132498])).

tff(c_132532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_114363,c_132530])).

tff(c_132534,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_133536,plain,(
    ~ m1_pre_topc('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_133533,c_132534])).

tff(c_133540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_133536])).

tff(c_133542,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_5','#skF_6','#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_134662,plain,(
    ~ m1_pre_topc('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_134659,c_133542])).

tff(c_134666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_134662])).

%------------------------------------------------------------------------------
