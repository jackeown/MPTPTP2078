%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:13 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 279 expanded)
%              Number of leaves         :   30 ( 128 expanded)
%              Depth                    :   10
%              Number of atoms          :  477 (3274 expanded)
%              Number of equality atoms :    5 ( 112 expanded)
%              Maximal formula depth    :   30 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k10_tmap_1,type,(
    k10_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_211,negated_conjecture,(
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
                  & v1_borsuk_1(C,A)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_borsuk_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( ( A = k1_tsep_1(A,C,D)
                                & r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,k10_tmap_1(A,B,C,D,E,F)),E)
                                & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,k10_tmap_1(A,B,C,D,E,F)),F) )
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(A),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),A,B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_tmap_1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_147,axiom,(
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

tff(f_128,axiom,(
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
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( A = k1_tsep_1(A,C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,k10_tmap_1(A,B,C,D,E,F)),E)
                                & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,k10_tmap_1(A,B,C,D,E,F)),F)
                                & r4_tsep_1(A,C,D) )
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(A),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),A,B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_32,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_30,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_24,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_176,plain,(
    ! [B_177,F_174,D_176,E_175,C_178,A_179] :
      ( m1_subset_1(k10_tmap_1(A_179,B_177,C_178,D_176,E_175,F_174),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_179,C_178,D_176)),u1_struct_0(B_177))))
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_176),u1_struct_0(B_177))))
      | ~ v1_funct_2(F_174,u1_struct_0(D_176),u1_struct_0(B_177))
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_178),u1_struct_0(B_177))))
      | ~ v1_funct_2(E_175,u1_struct_0(C_178),u1_struct_0(B_177))
      | ~ v1_funct_1(E_175)
      | ~ m1_pre_topc(D_176,A_179)
      | v2_struct_0(D_176)
      | ~ m1_pre_topc(C_178,A_179)
      | v2_struct_0(C_178)
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | v2_struct_0(B_177)
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_187,plain,(
    ! [B_177,E_175,F_174] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_175,F_174),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_177))))
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_177))))
      | ~ v1_funct_2(F_174,u1_struct_0('#skF_4'),u1_struct_0(B_177))
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_177))))
      | ~ v1_funct_2(E_175,u1_struct_0('#skF_3'),u1_struct_0(B_177))
      | ~ v1_funct_1(E_175)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | v2_struct_0(B_177)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_176])).

tff(c_198,plain,(
    ! [B_177,E_175,F_174] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_175,F_174),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_177))))
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_177))))
      | ~ v1_funct_2(F_174,u1_struct_0('#skF_4'),u1_struct_0(B_177))
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_177))))
      | ~ v1_funct_2(E_175,u1_struct_0('#skF_3'),u1_struct_0(B_177))
      | ~ v1_funct_1(E_175)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | v2_struct_0(B_177)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_48,c_42,c_187])).

tff(c_206,plain,(
    ! [B_186,E_187,F_188] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_186,'#skF_3','#skF_4',E_187,F_188),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_186))))
      | ~ m1_subset_1(F_188,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_186))))
      | ~ v1_funct_2(F_188,u1_struct_0('#skF_4'),u1_struct_0(B_186))
      | ~ v1_funct_1(F_188)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_186))))
      | ~ v1_funct_2(E_187,u1_struct_0('#skF_3'),u1_struct_0(B_186))
      | ~ v1_funct_1(E_187)
      | ~ l1_pre_topc(B_186)
      | ~ v2_pre_topc(B_186)
      | v2_struct_0(B_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_46,c_198])).

tff(c_73,plain,(
    ! [B_140,E_138,C_141,A_142,F_137,D_139] :
      ( v1_funct_1(k10_tmap_1(A_142,B_140,C_141,D_139,E_138,F_137))
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_139),u1_struct_0(B_140))))
      | ~ v1_funct_2(F_137,u1_struct_0(D_139),u1_struct_0(B_140))
      | ~ v1_funct_1(F_137)
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0(B_140))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0(B_140))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc(D_139,A_142)
      | v2_struct_0(D_139)
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | ~ l1_pre_topc(B_140)
      | ~ v2_pre_topc(B_140)
      | v2_struct_0(B_140)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_75,plain,(
    ! [A_142,C_141,E_138] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2',C_141,'#skF_4',E_138,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc('#skF_4',A_142)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_80,plain,(
    ! [A_142,C_141,E_138] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2',C_141,'#skF_4',E_138,'#skF_6'))
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc('#skF_4',A_142)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_32,c_30,c_75])).

tff(c_86,plain,(
    ! [A_143,C_144,E_145] :
      ( v1_funct_1(k10_tmap_1(A_143,'#skF_2',C_144,'#skF_4',E_145,'#skF_6'))
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_144),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_145,u1_struct_0(C_144),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_145)
      | ~ m1_pre_topc('#skF_4',A_143)
      | ~ m1_pre_topc(C_144,A_143)
      | v2_struct_0(C_144)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_80])).

tff(c_90,plain,(
    ! [A_143] :
      ( v1_funct_1(k10_tmap_1(A_143,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_143)
      | ~ m1_pre_topc('#skF_3',A_143)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_97,plain,(
    ! [A_143] :
      ( v1_funct_1(k10_tmap_1(A_143,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_143)
      | ~ m1_pre_topc('#skF_3',A_143)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_90])).

tff(c_100,plain,(
    ! [A_147] :
      ( v1_funct_1(k10_tmap_1(A_147,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_147)
      | ~ m1_pre_topc('#skF_3',A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_97])).

tff(c_18,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_72,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_103,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_72])).

tff(c_106,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_48,c_42,c_103])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_106])).

tff(c_109,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_111,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_217,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_206,c_111])).

tff(c_231,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_38,c_34,c_32,c_30,c_26,c_217])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_231])).

tff(c_234,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_236,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_296,plain,(
    ! [D_205,F_203,B_206,C_207,A_208,E_204] :
      ( v1_funct_2(k10_tmap_1(A_208,B_206,C_207,D_205,E_204,F_203),u1_struct_0(k1_tsep_1(A_208,C_207,D_205)),u1_struct_0(B_206))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_205),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_203,u1_struct_0(D_205),u1_struct_0(B_206))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_207),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_204,u1_struct_0(C_207),u1_struct_0(B_206))
      | ~ v1_funct_1(E_204)
      | ~ m1_pre_topc(D_205,A_208)
      | v2_struct_0(D_205)
      | ~ m1_pre_topc(C_207,A_208)
      | v2_struct_0(C_207)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_299,plain,(
    ! [B_206,E_204,F_203] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_206,'#skF_3','#skF_4',E_204,F_203),u1_struct_0('#skF_1'),u1_struct_0(B_206))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_203,u1_struct_0('#skF_4'),u1_struct_0(B_206))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_204,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(E_204)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_296])).

tff(c_301,plain,(
    ! [B_206,E_204,F_203] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_206,'#skF_3','#skF_4',E_204,F_203),u1_struct_0('#skF_1'),u1_struct_0(B_206))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_203,u1_struct_0('#skF_4'),u1_struct_0(B_206))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_204,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(E_204)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_48,c_42,c_299])).

tff(c_305,plain,(
    ! [B_211,E_212,F_213] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_211,'#skF_3','#skF_4',E_212,F_213),u1_struct_0('#skF_1'),u1_struct_0(B_211))
      | ~ m1_subset_1(F_213,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_211))))
      | ~ v1_funct_2(F_213,u1_struct_0('#skF_4'),u1_struct_0(B_211))
      | ~ v1_funct_1(F_213)
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_211))))
      | ~ v1_funct_2(E_212,u1_struct_0('#skF_3'),u1_struct_0(B_211))
      | ~ v1_funct_1(E_212)
      | ~ l1_pre_topc(B_211)
      | ~ v2_pre_topc(B_211)
      | v2_struct_0(B_211) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_46,c_301])).

tff(c_307,plain,(
    ! [E_212] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_212,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_212,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_212)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_305])).

tff(c_310,plain,(
    ! [E_212] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_212,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_212,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_212)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_32,c_30,c_307])).

tff(c_312,plain,(
    ! [E_214] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_214,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_214,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_214) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_310])).

tff(c_315,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_312])).

tff(c_318,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_315])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_318])).

tff(c_321,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_36,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_28,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_22,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_65,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_20,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_66,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20])).

tff(c_50,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_44,plain,(
    v1_borsuk_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_16,plain,(
    ! [A_70,B_74,C_76] :
      ( r4_tsep_1(A_70,B_74,C_76)
      | ~ m1_pre_topc(C_76,A_70)
      | ~ v1_borsuk_1(C_76,A_70)
      | ~ m1_pre_topc(B_74,A_70)
      | ~ v1_borsuk_1(B_74,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_525,plain,(
    ! [B_281,A_282,F_284,D_283,C_280,E_279] :
      ( v5_pre_topc(k10_tmap_1(A_282,B_281,C_280,D_283,E_279,F_284),A_282,B_281)
      | ~ r4_tsep_1(A_282,C_280,D_283)
      | ~ r2_funct_2(u1_struct_0(D_283),u1_struct_0(B_281),k3_tmap_1(A_282,B_281,k1_tsep_1(A_282,C_280,D_283),D_283,k10_tmap_1(A_282,B_281,C_280,D_283,E_279,F_284)),F_284)
      | ~ r2_funct_2(u1_struct_0(C_280),u1_struct_0(B_281),k3_tmap_1(A_282,B_281,k1_tsep_1(A_282,C_280,D_283),C_280,k10_tmap_1(A_282,B_281,C_280,D_283,E_279,F_284)),E_279)
      | ~ m1_subset_1(F_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_283),u1_struct_0(B_281))))
      | ~ v5_pre_topc(F_284,D_283,B_281)
      | ~ v1_funct_2(F_284,u1_struct_0(D_283),u1_struct_0(B_281))
      | ~ v1_funct_1(F_284)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_280),u1_struct_0(B_281))))
      | ~ v5_pre_topc(E_279,C_280,B_281)
      | ~ v1_funct_2(E_279,u1_struct_0(C_280),u1_struct_0(B_281))
      | ~ v1_funct_1(E_279)
      | k1_tsep_1(A_282,C_280,D_283) != A_282
      | ~ m1_pre_topc(D_283,A_282)
      | v2_struct_0(D_283)
      | ~ m1_pre_topc(C_280,A_282)
      | v2_struct_0(C_280)
      | ~ l1_pre_topc(B_281)
      | ~ v2_pre_topc(B_281)
      | v2_struct_0(B_281)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_527,plain,(
    ! [B_281,E_279,F_284] :
      ( v5_pre_topc(k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284),'#skF_1',B_281)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_281),k3_tmap_1('#skF_1',B_281,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284)),F_284)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_281),k3_tmap_1('#skF_1',B_281,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284)),E_279)
      | ~ m1_subset_1(F_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_281))))
      | ~ v5_pre_topc(F_284,'#skF_4',B_281)
      | ~ v1_funct_2(F_284,u1_struct_0('#skF_4'),u1_struct_0(B_281))
      | ~ v1_funct_1(F_284)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_281))))
      | ~ v5_pre_topc(E_279,'#skF_3',B_281)
      | ~ v1_funct_2(E_279,u1_struct_0('#skF_3'),u1_struct_0(B_281))
      | ~ v1_funct_1(E_279)
      | k1_tsep_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_281)
      | ~ v2_pre_topc(B_281)
      | v2_struct_0(B_281)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_525])).

tff(c_529,plain,(
    ! [B_281,E_279,F_284] :
      ( v5_pre_topc(k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284),'#skF_1',B_281)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_281),k3_tmap_1('#skF_1',B_281,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284)),F_284)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_281),k3_tmap_1('#skF_1',B_281,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284)),E_279)
      | ~ m1_subset_1(F_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_281))))
      | ~ v5_pre_topc(F_284,'#skF_4',B_281)
      | ~ v1_funct_2(F_284,u1_struct_0('#skF_4'),u1_struct_0(B_281))
      | ~ v1_funct_1(F_284)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_281))))
      | ~ v5_pre_topc(E_279,'#skF_3',B_281)
      | ~ v1_funct_2(E_279,u1_struct_0('#skF_3'),u1_struct_0(B_281))
      | ~ v1_funct_1(E_279)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_281)
      | ~ v2_pre_topc(B_281)
      | v2_struct_0(B_281)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_48,c_42,c_24,c_24,c_527])).

tff(c_530,plain,(
    ! [B_281,E_279,F_284] :
      ( v5_pre_topc(k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284),'#skF_1',B_281)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_281),k3_tmap_1('#skF_1',B_281,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284)),F_284)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_281),k3_tmap_1('#skF_1',B_281,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_281,'#skF_3','#skF_4',E_279,F_284)),E_279)
      | ~ m1_subset_1(F_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_281))))
      | ~ v5_pre_topc(F_284,'#skF_4',B_281)
      | ~ v1_funct_2(F_284,u1_struct_0('#skF_4'),u1_struct_0(B_281))
      | ~ v1_funct_1(F_284)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_281))))
      | ~ v5_pre_topc(E_279,'#skF_3',B_281)
      | ~ v1_funct_2(E_279,u1_struct_0('#skF_3'),u1_struct_0(B_281))
      | ~ v1_funct_1(E_279)
      | ~ l1_pre_topc(B_281)
      | ~ v2_pre_topc(B_281)
      | v2_struct_0(B_281) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_46,c_529])).

tff(c_684,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_687,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_684])).

tff(c_690,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_48,c_44,c_42,c_687])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_690])).

tff(c_695,plain,(
    ! [B_327,E_328,F_329] :
      ( v5_pre_topc(k10_tmap_1('#skF_1',B_327,'#skF_3','#skF_4',E_328,F_329),'#skF_1',B_327)
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_327),k3_tmap_1('#skF_1',B_327,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_327,'#skF_3','#skF_4',E_328,F_329)),F_329)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_327),k3_tmap_1('#skF_1',B_327,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_327,'#skF_3','#skF_4',E_328,F_329)),E_328)
      | ~ m1_subset_1(F_329,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_327))))
      | ~ v5_pre_topc(F_329,'#skF_4',B_327)
      | ~ v1_funct_2(F_329,u1_struct_0('#skF_4'),u1_struct_0(B_327))
      | ~ v1_funct_1(F_329)
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_327))))
      | ~ v5_pre_topc(E_328,'#skF_3',B_327)
      | ~ v1_funct_2(E_328,u1_struct_0('#skF_3'),u1_struct_0(B_327))
      | ~ v1_funct_1(E_328)
      | ~ l1_pre_topc(B_327)
      | ~ v2_pre_topc(B_327)
      | v2_struct_0(B_327) ) ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_697,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_695])).

tff(c_700,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_65,c_697])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_321,c_700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.80  
% 4.55/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.80  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.55/1.80  
% 4.55/1.80  %Foreground sorts:
% 4.55/1.80  
% 4.55/1.80  
% 4.55/1.80  %Background operators:
% 4.55/1.80  
% 4.55/1.80  
% 4.55/1.80  %Foreground operators:
% 4.55/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.55/1.80  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.80  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.55/1.80  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.55/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.55/1.80  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 4.55/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.80  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.55/1.80  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.55/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.55/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.55/1.80  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.55/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.80  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 4.55/1.80  
% 4.72/1.83  tff(f_211, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_borsuk_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_borsuk_1(D, A)) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((A = k1_tsep_1(A, C, D)) & r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E)) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_tmap_1)).
% 4.72/1.83  tff(f_67, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 4.72/1.83  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((v1_borsuk_1(C, A) & m1_pre_topc(C, A)) => r4_tsep_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tsep_1)).
% 4.72/1.83  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_tmap_1)).
% 4.72/1.83  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_32, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_30, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_24, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_176, plain, (![B_177, F_174, D_176, E_175, C_178, A_179]: (m1_subset_1(k10_tmap_1(A_179, B_177, C_178, D_176, E_175, F_174), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_179, C_178, D_176)), u1_struct_0(B_177)))) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_176), u1_struct_0(B_177)))) | ~v1_funct_2(F_174, u1_struct_0(D_176), u1_struct_0(B_177)) | ~v1_funct_1(F_174) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_178), u1_struct_0(B_177)))) | ~v1_funct_2(E_175, u1_struct_0(C_178), u1_struct_0(B_177)) | ~v1_funct_1(E_175) | ~m1_pre_topc(D_176, A_179) | v2_struct_0(D_176) | ~m1_pre_topc(C_178, A_179) | v2_struct_0(C_178) | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.72/1.83  tff(c_187, plain, (![B_177, E_175, F_174]: (m1_subset_1(k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_175, F_174), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_177)))) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_177)))) | ~v1_funct_2(F_174, u1_struct_0('#skF_4'), u1_struct_0(B_177)) | ~v1_funct_1(F_174) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_177)))) | ~v1_funct_2(E_175, u1_struct_0('#skF_3'), u1_struct_0(B_177)) | ~v1_funct_1(E_175) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_176])).
% 4.72/1.83  tff(c_198, plain, (![B_177, E_175, F_174]: (m1_subset_1(k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_175, F_174), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_177)))) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_177)))) | ~v1_funct_2(F_174, u1_struct_0('#skF_4'), u1_struct_0(B_177)) | ~v1_funct_1(F_174) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_177)))) | ~v1_funct_2(E_175, u1_struct_0('#skF_3'), u1_struct_0(B_177)) | ~v1_funct_1(E_175) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_48, c_42, c_187])).
% 4.72/1.83  tff(c_206, plain, (![B_186, E_187, F_188]: (m1_subset_1(k10_tmap_1('#skF_1', B_186, '#skF_3', '#skF_4', E_187, F_188), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_186)))) | ~m1_subset_1(F_188, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_186)))) | ~v1_funct_2(F_188, u1_struct_0('#skF_4'), u1_struct_0(B_186)) | ~v1_funct_1(F_188) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_186)))) | ~v1_funct_2(E_187, u1_struct_0('#skF_3'), u1_struct_0(B_186)) | ~v1_funct_1(E_187) | ~l1_pre_topc(B_186) | ~v2_pre_topc(B_186) | v2_struct_0(B_186))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_46, c_198])).
% 4.72/1.83  tff(c_73, plain, (![B_140, E_138, C_141, A_142, F_137, D_139]: (v1_funct_1(k10_tmap_1(A_142, B_140, C_141, D_139, E_138, F_137)) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_139), u1_struct_0(B_140)))) | ~v1_funct_2(F_137, u1_struct_0(D_139), u1_struct_0(B_140)) | ~v1_funct_1(F_137) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0(B_140)))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0(B_140)) | ~v1_funct_1(E_138) | ~m1_pre_topc(D_139, A_142) | v2_struct_0(D_139) | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | ~l1_pre_topc(B_140) | ~v2_pre_topc(B_140) | v2_struct_0(B_140) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.72/1.83  tff(c_75, plain, (![A_142, C_141, E_138]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', C_141, '#skF_4', E_138, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0('#skF_2')) | ~v1_funct_1(E_138) | ~m1_pre_topc('#skF_4', A_142) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_26, c_73])).
% 4.72/1.83  tff(c_80, plain, (![A_142, C_141, E_138]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', C_141, '#skF_4', E_138, '#skF_6')) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0('#skF_2')) | ~v1_funct_1(E_138) | ~m1_pre_topc('#skF_4', A_142) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_32, c_30, c_75])).
% 4.72/1.83  tff(c_86, plain, (![A_143, C_144, E_145]: (v1_funct_1(k10_tmap_1(A_143, '#skF_2', C_144, '#skF_4', E_145, '#skF_6')) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_144), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_145, u1_struct_0(C_144), u1_struct_0('#skF_2')) | ~v1_funct_1(E_145) | ~m1_pre_topc('#skF_4', A_143) | ~m1_pre_topc(C_144, A_143) | v2_struct_0(C_144) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_80])).
% 4.72/1.83  tff(c_90, plain, (![A_143]: (v1_funct_1(k10_tmap_1(A_143, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_143) | ~m1_pre_topc('#skF_3', A_143) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(resolution, [status(thm)], [c_34, c_86])).
% 4.72/1.83  tff(c_97, plain, (![A_143]: (v1_funct_1(k10_tmap_1(A_143, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_143) | ~m1_pre_topc('#skF_3', A_143) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_90])).
% 4.72/1.83  tff(c_100, plain, (![A_147]: (v1_funct_1(k10_tmap_1(A_147, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_147) | ~m1_pre_topc('#skF_3', A_147) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(negUnitSimplification, [status(thm)], [c_52, c_97])).
% 4.72/1.83  tff(c_18, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_72, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_18])).
% 4.72/1.83  tff(c_103, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_100, c_72])).
% 4.72/1.83  tff(c_106, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_48, c_42, c_103])).
% 4.72/1.83  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_106])).
% 4.72/1.83  tff(c_109, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_18])).
% 4.72/1.83  tff(c_111, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_109])).
% 4.72/1.83  tff(c_217, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_206, c_111])).
% 4.72/1.83  tff(c_231, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_38, c_34, c_32, c_30, c_26, c_217])).
% 4.72/1.83  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_231])).
% 4.72/1.83  tff(c_234, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_109])).
% 4.72/1.83  tff(c_236, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_234])).
% 4.72/1.83  tff(c_296, plain, (![D_205, F_203, B_206, C_207, A_208, E_204]: (v1_funct_2(k10_tmap_1(A_208, B_206, C_207, D_205, E_204, F_203), u1_struct_0(k1_tsep_1(A_208, C_207, D_205)), u1_struct_0(B_206)) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_205), u1_struct_0(B_206)))) | ~v1_funct_2(F_203, u1_struct_0(D_205), u1_struct_0(B_206)) | ~v1_funct_1(F_203) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_207), u1_struct_0(B_206)))) | ~v1_funct_2(E_204, u1_struct_0(C_207), u1_struct_0(B_206)) | ~v1_funct_1(E_204) | ~m1_pre_topc(D_205, A_208) | v2_struct_0(D_205) | ~m1_pre_topc(C_207, A_208) | v2_struct_0(C_207) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.72/1.83  tff(c_299, plain, (![B_206, E_204, F_203]: (v1_funct_2(k10_tmap_1('#skF_1', B_206, '#skF_3', '#skF_4', E_204, F_203), u1_struct_0('#skF_1'), u1_struct_0(B_206)) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_206)))) | ~v1_funct_2(F_203, u1_struct_0('#skF_4'), u1_struct_0(B_206)) | ~v1_funct_1(F_203) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(E_204, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(E_204) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_296])).
% 4.72/1.83  tff(c_301, plain, (![B_206, E_204, F_203]: (v1_funct_2(k10_tmap_1('#skF_1', B_206, '#skF_3', '#skF_4', E_204, F_203), u1_struct_0('#skF_1'), u1_struct_0(B_206)) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_206)))) | ~v1_funct_2(F_203, u1_struct_0('#skF_4'), u1_struct_0(B_206)) | ~v1_funct_1(F_203) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(E_204, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(E_204) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_48, c_42, c_299])).
% 4.72/1.83  tff(c_305, plain, (![B_211, E_212, F_213]: (v1_funct_2(k10_tmap_1('#skF_1', B_211, '#skF_3', '#skF_4', E_212, F_213), u1_struct_0('#skF_1'), u1_struct_0(B_211)) | ~m1_subset_1(F_213, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_211)))) | ~v1_funct_2(F_213, u1_struct_0('#skF_4'), u1_struct_0(B_211)) | ~v1_funct_1(F_213) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_211)))) | ~v1_funct_2(E_212, u1_struct_0('#skF_3'), u1_struct_0(B_211)) | ~v1_funct_1(E_212) | ~l1_pre_topc(B_211) | ~v2_pre_topc(B_211) | v2_struct_0(B_211))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_46, c_301])).
% 4.72/1.83  tff(c_307, plain, (![E_212]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_212, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_212, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_212) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_305])).
% 4.72/1.83  tff(c_310, plain, (![E_212]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_212, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_212, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_212) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_32, c_30, c_307])).
% 4.72/1.83  tff(c_312, plain, (![E_214]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_214, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_214, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_214))), inference(negUnitSimplification, [status(thm)], [c_58, c_310])).
% 4.72/1.83  tff(c_315, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_312])).
% 4.72/1.83  tff(c_318, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_315])).
% 4.72/1.83  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_318])).
% 4.72/1.83  tff(c_321, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_234])).
% 4.72/1.83  tff(c_36, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_28, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_22, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_65, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 4.72/1.83  tff(c_20, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_66, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20])).
% 4.72/1.83  tff(c_50, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_44, plain, (v1_borsuk_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 4.72/1.83  tff(c_16, plain, (![A_70, B_74, C_76]: (r4_tsep_1(A_70, B_74, C_76) | ~m1_pre_topc(C_76, A_70) | ~v1_borsuk_1(C_76, A_70) | ~m1_pre_topc(B_74, A_70) | ~v1_borsuk_1(B_74, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.72/1.83  tff(c_525, plain, (![B_281, A_282, F_284, D_283, C_280, E_279]: (v5_pre_topc(k10_tmap_1(A_282, B_281, C_280, D_283, E_279, F_284), A_282, B_281) | ~r4_tsep_1(A_282, C_280, D_283) | ~r2_funct_2(u1_struct_0(D_283), u1_struct_0(B_281), k3_tmap_1(A_282, B_281, k1_tsep_1(A_282, C_280, D_283), D_283, k10_tmap_1(A_282, B_281, C_280, D_283, E_279, F_284)), F_284) | ~r2_funct_2(u1_struct_0(C_280), u1_struct_0(B_281), k3_tmap_1(A_282, B_281, k1_tsep_1(A_282, C_280, D_283), C_280, k10_tmap_1(A_282, B_281, C_280, D_283, E_279, F_284)), E_279) | ~m1_subset_1(F_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_283), u1_struct_0(B_281)))) | ~v5_pre_topc(F_284, D_283, B_281) | ~v1_funct_2(F_284, u1_struct_0(D_283), u1_struct_0(B_281)) | ~v1_funct_1(F_284) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_280), u1_struct_0(B_281)))) | ~v5_pre_topc(E_279, C_280, B_281) | ~v1_funct_2(E_279, u1_struct_0(C_280), u1_struct_0(B_281)) | ~v1_funct_1(E_279) | k1_tsep_1(A_282, C_280, D_283)!=A_282 | ~m1_pre_topc(D_283, A_282) | v2_struct_0(D_283) | ~m1_pre_topc(C_280, A_282) | v2_struct_0(C_280) | ~l1_pre_topc(B_281) | ~v2_pre_topc(B_281) | v2_struct_0(B_281) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.72/1.83  tff(c_527, plain, (![B_281, E_279, F_284]: (v5_pre_topc(k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284), '#skF_1', B_281) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_281), k3_tmap_1('#skF_1', B_281, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284)), F_284) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_281), k3_tmap_1('#skF_1', B_281, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284)), E_279) | ~m1_subset_1(F_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_281)))) | ~v5_pre_topc(F_284, '#skF_4', B_281) | ~v1_funct_2(F_284, u1_struct_0('#skF_4'), u1_struct_0(B_281)) | ~v1_funct_1(F_284) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_281)))) | ~v5_pre_topc(E_279, '#skF_3', B_281) | ~v1_funct_2(E_279, u1_struct_0('#skF_3'), u1_struct_0(B_281)) | ~v1_funct_1(E_279) | k1_tsep_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_281) | ~v2_pre_topc(B_281) | v2_struct_0(B_281) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_525])).
% 4.72/1.83  tff(c_529, plain, (![B_281, E_279, F_284]: (v5_pre_topc(k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284), '#skF_1', B_281) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_281), k3_tmap_1('#skF_1', B_281, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284)), F_284) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_281), k3_tmap_1('#skF_1', B_281, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284)), E_279) | ~m1_subset_1(F_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_281)))) | ~v5_pre_topc(F_284, '#skF_4', B_281) | ~v1_funct_2(F_284, u1_struct_0('#skF_4'), u1_struct_0(B_281)) | ~v1_funct_1(F_284) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_281)))) | ~v5_pre_topc(E_279, '#skF_3', B_281) | ~v1_funct_2(E_279, u1_struct_0('#skF_3'), u1_struct_0(B_281)) | ~v1_funct_1(E_279) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_281) | ~v2_pre_topc(B_281) | v2_struct_0(B_281) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_48, c_42, c_24, c_24, c_527])).
% 4.72/1.83  tff(c_530, plain, (![B_281, E_279, F_284]: (v5_pre_topc(k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284), '#skF_1', B_281) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_281), k3_tmap_1('#skF_1', B_281, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284)), F_284) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_281), k3_tmap_1('#skF_1', B_281, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_281, '#skF_3', '#skF_4', E_279, F_284)), E_279) | ~m1_subset_1(F_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_281)))) | ~v5_pre_topc(F_284, '#skF_4', B_281) | ~v1_funct_2(F_284, u1_struct_0('#skF_4'), u1_struct_0(B_281)) | ~v1_funct_1(F_284) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_281)))) | ~v5_pre_topc(E_279, '#skF_3', B_281) | ~v1_funct_2(E_279, u1_struct_0('#skF_3'), u1_struct_0(B_281)) | ~v1_funct_1(E_279) | ~l1_pre_topc(B_281) | ~v2_pre_topc(B_281) | v2_struct_0(B_281))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_46, c_529])).
% 4.72/1.83  tff(c_684, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_530])).
% 4.72/1.83  tff(c_687, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_borsuk_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_684])).
% 4.72/1.83  tff(c_690, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_48, c_44, c_42, c_687])).
% 4.72/1.83  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_690])).
% 4.72/1.83  tff(c_695, plain, (![B_327, E_328, F_329]: (v5_pre_topc(k10_tmap_1('#skF_1', B_327, '#skF_3', '#skF_4', E_328, F_329), '#skF_1', B_327) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_327), k3_tmap_1('#skF_1', B_327, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_327, '#skF_3', '#skF_4', E_328, F_329)), F_329) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_327), k3_tmap_1('#skF_1', B_327, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_327, '#skF_3', '#skF_4', E_328, F_329)), E_328) | ~m1_subset_1(F_329, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_327)))) | ~v5_pre_topc(F_329, '#skF_4', B_327) | ~v1_funct_2(F_329, u1_struct_0('#skF_4'), u1_struct_0(B_327)) | ~v1_funct_1(F_329) | ~m1_subset_1(E_328, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_327)))) | ~v5_pre_topc(E_328, '#skF_3', B_327) | ~v1_funct_2(E_328, u1_struct_0('#skF_3'), u1_struct_0(B_327)) | ~v1_funct_1(E_328) | ~l1_pre_topc(B_327) | ~v2_pre_topc(B_327) | v2_struct_0(B_327))), inference(splitRight, [status(thm)], [c_530])).
% 4.72/1.83  tff(c_697, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_695])).
% 4.72/1.83  tff(c_700, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_65, c_697])).
% 4.72/1.83  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_321, c_700])).
% 4.72/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.83  
% 4.72/1.83  Inference rules
% 4.72/1.83  ----------------------
% 4.72/1.83  #Ref     : 0
% 4.72/1.83  #Sup     : 92
% 4.72/1.83  #Fact    : 0
% 4.72/1.83  #Define  : 0
% 4.72/1.83  #Split   : 4
% 4.72/1.83  #Chain   : 0
% 4.72/1.83  #Close   : 0
% 4.72/1.83  
% 4.72/1.83  Ordering : KBO
% 4.72/1.83  
% 4.72/1.83  Simplification rules
% 4.72/1.83  ----------------------
% 4.72/1.83  #Subsume      : 12
% 4.72/1.83  #Demod        : 273
% 4.72/1.83  #Tautology    : 3
% 4.72/1.83  #SimpNegUnit  : 83
% 4.72/1.83  #BackRed      : 0
% 4.72/1.83  
% 4.72/1.83  #Partial instantiations: 0
% 4.72/1.83  #Strategies tried      : 1
% 4.72/1.83  
% 4.72/1.83  Timing (in seconds)
% 4.72/1.83  ----------------------
% 4.72/1.83  Preprocessing        : 0.38
% 4.72/1.83  Parsing              : 0.19
% 4.72/1.83  CNF conversion       : 0.06
% 4.72/1.83  Main loop            : 0.59
% 4.72/1.83  Inferencing          : 0.20
% 4.72/1.83  Reduction            : 0.19
% 4.72/1.83  Demodulation         : 0.14
% 4.72/1.83  BG Simplification    : 0.03
% 4.72/1.83  Subsumption          : 0.15
% 4.72/1.83  Abstraction          : 0.02
% 4.72/1.83  MUC search           : 0.00
% 4.72/1.83  Cooper               : 0.00
% 4.72/1.83  Total                : 1.01
% 4.72/1.83  Index Insertion      : 0.00
% 4.72/1.83  Index Deletion       : 0.00
% 4.72/1.83  Index Matching       : 0.00
% 4.72/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
