%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:14 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 543 expanded)
%              Number of leaves         :   29 ( 243 expanded)
%              Depth                    :   10
%              Number of atoms          :  791 (7043 expanded)
%              Number of equality atoms :   17 ( 276 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(f_169,negated_conjecture,(
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
                  & v1_tsep_1(C,A)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,A)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_tmap_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_tsep_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).

tff(f_86,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_12,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_66,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_30,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_26,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_24,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_22,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_20,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_18,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_16,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_59,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_14,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_60,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_44,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_38,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_10,plain,(
    ! [A_64,B_68,C_70] :
      ( r4_tsep_1(A_64,B_68,C_70)
      | ~ m1_pre_topc(C_70,A_64)
      | ~ v1_tsep_1(C_70,A_64)
      | ~ m1_pre_topc(B_68,A_64)
      | ~ v1_tsep_1(B_68,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_67,plain,(
    ! [C_136,B_132,D_134,E_131,F_133,A_135] :
      ( v1_funct_1(k10_tmap_1(A_135,B_132,C_136,D_134,E_131,F_133))
      | ~ r4_tsep_1(A_135,C_136,D_134)
      | ~ r2_funct_2(u1_struct_0(D_134),u1_struct_0(B_132),k3_tmap_1(A_135,B_132,k1_tsep_1(A_135,C_136,D_134),D_134,k10_tmap_1(A_135,B_132,C_136,D_134,E_131,F_133)),F_133)
      | ~ r2_funct_2(u1_struct_0(C_136),u1_struct_0(B_132),k3_tmap_1(A_135,B_132,k1_tsep_1(A_135,C_136,D_134),C_136,k10_tmap_1(A_135,B_132,C_136,D_134,E_131,F_133)),E_131)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_134),u1_struct_0(B_132))))
      | ~ v5_pre_topc(F_133,D_134,B_132)
      | ~ v1_funct_2(F_133,u1_struct_0(D_134),u1_struct_0(B_132))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_136),u1_struct_0(B_132))))
      | ~ v5_pre_topc(E_131,C_136,B_132)
      | ~ v1_funct_2(E_131,u1_struct_0(C_136),u1_struct_0(B_132))
      | ~ v1_funct_1(E_131)
      | k1_tsep_1(A_135,C_136,D_134) != A_135
      | ~ m1_pre_topc(D_134,A_135)
      | v2_struct_0(D_134)
      | ~ m1_pre_topc(C_136,A_135)
      | v2_struct_0(C_136)
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    ! [B_132,E_131,F_133] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_132),k3_tmap_1('#skF_1',B_132,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133)),F_133)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_132),k3_tmap_1('#skF_1',B_132,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133)),E_131)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_132))))
      | ~ v5_pre_topc(F_133,'#skF_4',B_132)
      | ~ v1_funct_2(F_133,u1_struct_0('#skF_4'),u1_struct_0(B_132))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_132))))
      | ~ v5_pre_topc(E_131,'#skF_3',B_132)
      | ~ v1_funct_2(E_131,u1_struct_0('#skF_3'),u1_struct_0(B_132))
      | ~ v1_funct_1(E_131)
      | k1_tsep_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_67])).

tff(c_71,plain,(
    ! [B_132,E_131,F_133] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_132),k3_tmap_1('#skF_1',B_132,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133)),F_133)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_132),k3_tmap_1('#skF_1',B_132,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133)),E_131)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_132))))
      | ~ v5_pre_topc(F_133,'#skF_4',B_132)
      | ~ v1_funct_2(F_133,u1_struct_0('#skF_4'),u1_struct_0(B_132))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_132))))
      | ~ v5_pre_topc(E_131,'#skF_3',B_132)
      | ~ v1_funct_2(E_131,u1_struct_0('#skF_3'),u1_struct_0(B_132))
      | ~ v1_funct_1(E_131)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | v2_struct_0(B_132)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_36,c_18,c_18,c_69])).

tff(c_72,plain,(
    ! [B_132,E_131,F_133] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_132),k3_tmap_1('#skF_1',B_132,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133)),F_133)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_132),k3_tmap_1('#skF_1',B_132,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_132,'#skF_3','#skF_4',E_131,F_133)),E_131)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_132))))
      | ~ v5_pre_topc(F_133,'#skF_4',B_132)
      | ~ v1_funct_2(F_133,u1_struct_0('#skF_4'),u1_struct_0(B_132))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_132))))
      | ~ v5_pre_topc(E_131,'#skF_3',B_132)
      | ~ v1_funct_2(E_131,u1_struct_0('#skF_3'),u1_struct_0(B_132))
      | ~ v1_funct_1(E_131)
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | v2_struct_0(B_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_40,c_71])).

tff(c_73,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_76,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_79,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_38,c_36,c_76])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_79])).

tff(c_84,plain,(
    ! [B_137,E_138,F_139] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_137,'#skF_3','#skF_4',E_138,F_139))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_137),k3_tmap_1('#skF_1',B_137,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_137,'#skF_3','#skF_4',E_138,F_139)),F_139)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_137),k3_tmap_1('#skF_1',B_137,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_137,'#skF_3','#skF_4',E_138,F_139)),E_138)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_137))))
      | ~ v5_pre_topc(F_139,'#skF_4',B_137)
      | ~ v1_funct_2(F_139,u1_struct_0('#skF_4'),u1_struct_0(B_137))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_137))))
      | ~ v5_pre_topc(E_138,'#skF_3',B_137)
      | ~ v1_funct_2(E_138,u1_struct_0('#skF_3'),u1_struct_0(B_137))
      | ~ v1_funct_1(E_138)
      | ~ l1_pre_topc(B_137)
      | ~ v2_pre_topc(B_137)
      | v2_struct_0(B_137) ) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_86,plain,
    ( v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
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
    inference(resolution,[status(thm)],[c_60,c_84])).

tff(c_89,plain,
    ( v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_20,c_59,c_86])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_66,c_89])).

tff(c_92,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_94,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_95,plain,(
    ! [E_140,F_142,A_144,D_143,C_145,B_141] :
      ( v1_funct_1(k10_tmap_1(A_144,B_141,C_145,D_143,E_140,F_142))
      | ~ r4_tsep_1(A_144,C_145,D_143)
      | ~ r2_funct_2(u1_struct_0(D_143),u1_struct_0(B_141),k3_tmap_1(A_144,B_141,k1_tsep_1(A_144,C_145,D_143),D_143,k10_tmap_1(A_144,B_141,C_145,D_143,E_140,F_142)),F_142)
      | ~ r2_funct_2(u1_struct_0(C_145),u1_struct_0(B_141),k3_tmap_1(A_144,B_141,k1_tsep_1(A_144,C_145,D_143),C_145,k10_tmap_1(A_144,B_141,C_145,D_143,E_140,F_142)),E_140)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_143),u1_struct_0(B_141))))
      | ~ v5_pre_topc(F_142,D_143,B_141)
      | ~ v1_funct_2(F_142,u1_struct_0(D_143),u1_struct_0(B_141))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_145),u1_struct_0(B_141))))
      | ~ v5_pre_topc(E_140,C_145,B_141)
      | ~ v1_funct_2(E_140,u1_struct_0(C_145),u1_struct_0(B_141))
      | ~ v1_funct_1(E_140)
      | k1_tsep_1(A_144,C_145,D_143) != A_144
      | ~ m1_pre_topc(D_143,A_144)
      | v2_struct_0(D_143)
      | ~ m1_pre_topc(C_145,A_144)
      | v2_struct_0(C_145)
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_97,plain,(
    ! [B_141,E_140,F_142] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_141),k3_tmap_1('#skF_1',B_141,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142)),F_142)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_141),k3_tmap_1('#skF_1',B_141,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142)),E_140)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(F_142,'#skF_4',B_141)
      | ~ v1_funct_2(F_142,u1_struct_0('#skF_4'),u1_struct_0(B_141))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(E_140,'#skF_3',B_141)
      | ~ v1_funct_2(E_140,u1_struct_0('#skF_3'),u1_struct_0(B_141))
      | ~ v1_funct_1(E_140)
      | k1_tsep_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_99,plain,(
    ! [B_141,E_140,F_142] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_141),k3_tmap_1('#skF_1',B_141,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142)),F_142)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_141),k3_tmap_1('#skF_1',B_141,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142)),E_140)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(F_142,'#skF_4',B_141)
      | ~ v1_funct_2(F_142,u1_struct_0('#skF_4'),u1_struct_0(B_141))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(E_140,'#skF_3',B_141)
      | ~ v1_funct_2(E_140,u1_struct_0('#skF_3'),u1_struct_0(B_141))
      | ~ v1_funct_1(E_140)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_36,c_18,c_18,c_97])).

tff(c_100,plain,(
    ! [B_141,E_140,F_142] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_141),k3_tmap_1('#skF_1',B_141,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142)),F_142)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_141),k3_tmap_1('#skF_1',B_141,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_141,'#skF_3','#skF_4',E_140,F_142)),E_140)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(F_142,'#skF_4',B_141)
      | ~ v1_funct_2(F_142,u1_struct_0('#skF_4'),u1_struct_0(B_141))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(E_140,'#skF_3',B_141)
      | ~ v1_funct_2(E_140,u1_struct_0('#skF_3'),u1_struct_0(B_141))
      | ~ v1_funct_1(E_140)
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_40,c_99])).

tff(c_107,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_110,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_107])).

tff(c_113,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_38,c_36,c_110])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_113])).

tff(c_117,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_147,plain,(
    ! [D_170,A_171,E_167,B_168,C_172,F_169] :
      ( m1_subset_1(k10_tmap_1(A_171,B_168,C_172,D_170,E_167,F_169),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0(B_168))))
      | ~ r4_tsep_1(A_171,C_172,D_170)
      | ~ r2_funct_2(u1_struct_0(D_170),u1_struct_0(B_168),k3_tmap_1(A_171,B_168,k1_tsep_1(A_171,C_172,D_170),D_170,k10_tmap_1(A_171,B_168,C_172,D_170,E_167,F_169)),F_169)
      | ~ r2_funct_2(u1_struct_0(C_172),u1_struct_0(B_168),k3_tmap_1(A_171,B_168,k1_tsep_1(A_171,C_172,D_170),C_172,k10_tmap_1(A_171,B_168,C_172,D_170,E_167,F_169)),E_167)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_170),u1_struct_0(B_168))))
      | ~ v5_pre_topc(F_169,D_170,B_168)
      | ~ v1_funct_2(F_169,u1_struct_0(D_170),u1_struct_0(B_168))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_172),u1_struct_0(B_168))))
      | ~ v5_pre_topc(E_167,C_172,B_168)
      | ~ v1_funct_2(E_167,u1_struct_0(C_172),u1_struct_0(B_168))
      | ~ v1_funct_1(E_167)
      | k1_tsep_1(A_171,C_172,D_170) != A_171
      | ~ m1_pre_topc(D_170,A_171)
      | v2_struct_0(D_170)
      | ~ m1_pre_topc(C_172,A_171)
      | v2_struct_0(C_172)
      | ~ l1_pre_topc(B_168)
      | ~ v2_pre_topc(B_168)
      | v2_struct_0(B_168)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_149,plain,(
    ! [B_168,E_167,F_169] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_168,'#skF_3','#skF_4',E_167,F_169),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_168))))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_168),k3_tmap_1('#skF_1',B_168,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_168,'#skF_3','#skF_4',E_167,F_169)),F_169)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_168),k3_tmap_1('#skF_1',B_168,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_168,'#skF_3','#skF_4',E_167,F_169)),E_167)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_168))))
      | ~ v5_pre_topc(F_169,'#skF_4',B_168)
      | ~ v1_funct_2(F_169,u1_struct_0('#skF_4'),u1_struct_0(B_168))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_168))))
      | ~ v5_pre_topc(E_167,'#skF_3',B_168)
      | ~ v1_funct_2(E_167,u1_struct_0('#skF_3'),u1_struct_0(B_168))
      | ~ v1_funct_1(E_167)
      | k1_tsep_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_168)
      | ~ v2_pre_topc(B_168)
      | v2_struct_0(B_168)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_147])).

tff(c_151,plain,(
    ! [B_168,E_167,F_169] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_168,'#skF_3','#skF_4',E_167,F_169),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_168))))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_168),k3_tmap_1('#skF_1',B_168,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_168,'#skF_3','#skF_4',E_167,F_169)),F_169)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_168),k3_tmap_1('#skF_1',B_168,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_168,'#skF_3','#skF_4',E_167,F_169)),E_167)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_168))))
      | ~ v5_pre_topc(F_169,'#skF_4',B_168)
      | ~ v1_funct_2(F_169,u1_struct_0('#skF_4'),u1_struct_0(B_168))
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_168))))
      | ~ v5_pre_topc(E_167,'#skF_3',B_168)
      | ~ v1_funct_2(E_167,u1_struct_0('#skF_3'),u1_struct_0(B_168))
      | ~ v1_funct_1(E_167)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_168)
      | ~ v2_pre_topc(B_168)
      | v2_struct_0(B_168)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_36,c_18,c_18,c_117,c_149])).

tff(c_153,plain,(
    ! [B_173,E_174,F_175] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_173,'#skF_3','#skF_4',E_174,F_175),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_173))))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_173),k3_tmap_1('#skF_1',B_173,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_173,'#skF_3','#skF_4',E_174,F_175)),F_175)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_173),k3_tmap_1('#skF_1',B_173,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_173,'#skF_3','#skF_4',E_174,F_175)),E_174)
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_173))))
      | ~ v5_pre_topc(F_175,'#skF_4',B_173)
      | ~ v1_funct_2(F_175,u1_struct_0('#skF_4'),u1_struct_0(B_173))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_173))))
      | ~ v5_pre_topc(E_174,'#skF_3',B_173)
      | ~ v1_funct_2(E_174,u1_struct_0('#skF_3'),u1_struct_0(B_173))
      | ~ v1_funct_1(E_174)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_40,c_151])).

tff(c_155,plain,
    ( m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
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
    inference(resolution,[status(thm)],[c_60,c_153])).

tff(c_158,plain,
    ( m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_20,c_59,c_155])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_94,c_158])).

tff(c_161,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_163,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_164,plain,(
    ! [B_177,F_178,D_179,C_181,E_176,A_180] :
      ( v1_funct_1(k10_tmap_1(A_180,B_177,C_181,D_179,E_176,F_178))
      | ~ r4_tsep_1(A_180,C_181,D_179)
      | ~ r2_funct_2(u1_struct_0(D_179),u1_struct_0(B_177),k3_tmap_1(A_180,B_177,k1_tsep_1(A_180,C_181,D_179),D_179,k10_tmap_1(A_180,B_177,C_181,D_179,E_176,F_178)),F_178)
      | ~ r2_funct_2(u1_struct_0(C_181),u1_struct_0(B_177),k3_tmap_1(A_180,B_177,k1_tsep_1(A_180,C_181,D_179),C_181,k10_tmap_1(A_180,B_177,C_181,D_179,E_176,F_178)),E_176)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179),u1_struct_0(B_177))))
      | ~ v5_pre_topc(F_178,D_179,B_177)
      | ~ v1_funct_2(F_178,u1_struct_0(D_179),u1_struct_0(B_177))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_181),u1_struct_0(B_177))))
      | ~ v5_pre_topc(E_176,C_181,B_177)
      | ~ v1_funct_2(E_176,u1_struct_0(C_181),u1_struct_0(B_177))
      | ~ v1_funct_1(E_176)
      | k1_tsep_1(A_180,C_181,D_179) != A_180
      | ~ m1_pre_topc(D_179,A_180)
      | v2_struct_0(D_179)
      | ~ m1_pre_topc(C_181,A_180)
      | v2_struct_0(C_181)
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | v2_struct_0(B_177)
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_166,plain,(
    ! [B_177,E_176,F_178] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_177),k3_tmap_1('#skF_1',B_177,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178)),F_178)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_177),k3_tmap_1('#skF_1',B_177,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178)),E_176)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_177))))
      | ~ v5_pre_topc(F_178,'#skF_4',B_177)
      | ~ v1_funct_2(F_178,u1_struct_0('#skF_4'),u1_struct_0(B_177))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_177))))
      | ~ v5_pre_topc(E_176,'#skF_3',B_177)
      | ~ v1_funct_2(E_176,u1_struct_0('#skF_3'),u1_struct_0(B_177))
      | ~ v1_funct_1(E_176)
      | k1_tsep_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
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
    inference(superposition,[status(thm),theory(equality)],[c_18,c_164])).

tff(c_168,plain,(
    ! [B_177,E_176,F_178] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_177),k3_tmap_1('#skF_1',B_177,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178)),F_178)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_177),k3_tmap_1('#skF_1',B_177,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178)),E_176)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_177))))
      | ~ v5_pre_topc(F_178,'#skF_4',B_177)
      | ~ v1_funct_2(F_178,u1_struct_0('#skF_4'),u1_struct_0(B_177))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_177))))
      | ~ v5_pre_topc(E_176,'#skF_3',B_177)
      | ~ v1_funct_2(E_176,u1_struct_0('#skF_3'),u1_struct_0(B_177))
      | ~ v1_funct_1(E_176)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | v2_struct_0(B_177)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_36,c_18,c_18,c_166])).

tff(c_169,plain,(
    ! [B_177,E_176,F_178] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_177),k3_tmap_1('#skF_1',B_177,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178)),F_178)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_177),k3_tmap_1('#skF_1',B_177,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_177,'#skF_3','#skF_4',E_176,F_178)),E_176)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_177))))
      | ~ v5_pre_topc(F_178,'#skF_4',B_177)
      | ~ v1_funct_2(F_178,u1_struct_0('#skF_4'),u1_struct_0(B_177))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_177))))
      | ~ v5_pre_topc(E_176,'#skF_3',B_177)
      | ~ v1_funct_2(E_176,u1_struct_0('#skF_3'),u1_struct_0(B_177))
      | ~ v1_funct_1(E_176)
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | v2_struct_0(B_177) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_40,c_168])).

tff(c_170,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_173,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_170])).

tff(c_176,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_38,c_36,c_173])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_176])).

tff(c_180,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_201,plain,(
    ! [F_196,C_199,E_194,A_198,D_197,B_195] :
      ( v1_funct_2(k10_tmap_1(A_198,B_195,C_199,D_197,E_194,F_196),u1_struct_0(A_198),u1_struct_0(B_195))
      | ~ r4_tsep_1(A_198,C_199,D_197)
      | ~ r2_funct_2(u1_struct_0(D_197),u1_struct_0(B_195),k3_tmap_1(A_198,B_195,k1_tsep_1(A_198,C_199,D_197),D_197,k10_tmap_1(A_198,B_195,C_199,D_197,E_194,F_196)),F_196)
      | ~ r2_funct_2(u1_struct_0(C_199),u1_struct_0(B_195),k3_tmap_1(A_198,B_195,k1_tsep_1(A_198,C_199,D_197),C_199,k10_tmap_1(A_198,B_195,C_199,D_197,E_194,F_196)),E_194)
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_197),u1_struct_0(B_195))))
      | ~ v5_pre_topc(F_196,D_197,B_195)
      | ~ v1_funct_2(F_196,u1_struct_0(D_197),u1_struct_0(B_195))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_199),u1_struct_0(B_195))))
      | ~ v5_pre_topc(E_194,C_199,B_195)
      | ~ v1_funct_2(E_194,u1_struct_0(C_199),u1_struct_0(B_195))
      | ~ v1_funct_1(E_194)
      | k1_tsep_1(A_198,C_199,D_197) != A_198
      | ~ m1_pre_topc(D_197,A_198)
      | v2_struct_0(D_197)
      | ~ m1_pre_topc(C_199,A_198)
      | v2_struct_0(C_199)
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_203,plain,(
    ! [B_195,E_194,F_196] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_195,'#skF_3','#skF_4',E_194,F_196),u1_struct_0('#skF_1'),u1_struct_0(B_195))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_195),k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_195,'#skF_3','#skF_4',E_194,F_196)),F_196)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_195),k3_tmap_1('#skF_1',B_195,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_195,'#skF_3','#skF_4',E_194,F_196)),E_194)
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_195))))
      | ~ v5_pre_topc(F_196,'#skF_4',B_195)
      | ~ v1_funct_2(F_196,u1_struct_0('#skF_4'),u1_struct_0(B_195))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_195))))
      | ~ v5_pre_topc(E_194,'#skF_3',B_195)
      | ~ v1_funct_2(E_194,u1_struct_0('#skF_3'),u1_struct_0(B_195))
      | ~ v1_funct_1(E_194)
      | k1_tsep_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_201])).

tff(c_205,plain,(
    ! [B_195,E_194,F_196] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_195,'#skF_3','#skF_4',E_194,F_196),u1_struct_0('#skF_1'),u1_struct_0(B_195))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_195),k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_195,'#skF_3','#skF_4',E_194,F_196)),F_196)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_195),k3_tmap_1('#skF_1',B_195,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_195,'#skF_3','#skF_4',E_194,F_196)),E_194)
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_195))))
      | ~ v5_pre_topc(F_196,'#skF_4',B_195)
      | ~ v1_funct_2(F_196,u1_struct_0('#skF_4'),u1_struct_0(B_195))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_195))))
      | ~ v5_pre_topc(E_194,'#skF_3',B_195)
      | ~ v1_funct_2(E_194,u1_struct_0('#skF_3'),u1_struct_0(B_195))
      | ~ v1_funct_1(E_194)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_36,c_18,c_18,c_180,c_203])).

tff(c_207,plain,(
    ! [B_200,E_201,F_202] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_200,'#skF_3','#skF_4',E_201,F_202),u1_struct_0('#skF_1'),u1_struct_0(B_200))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_200),k3_tmap_1('#skF_1',B_200,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_200,'#skF_3','#skF_4',E_201,F_202)),F_202)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_200),k3_tmap_1('#skF_1',B_200,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_200,'#skF_3','#skF_4',E_201,F_202)),E_201)
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_200))))
      | ~ v5_pre_topc(F_202,'#skF_4',B_200)
      | ~ v1_funct_2(F_202,u1_struct_0('#skF_4'),u1_struct_0(B_200))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_200))))
      | ~ v5_pre_topc(E_201,'#skF_3',B_200)
      | ~ v1_funct_2(E_201,u1_struct_0('#skF_3'),u1_struct_0(B_200))
      | ~ v1_funct_1(E_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_40,c_205])).

tff(c_209,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
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
    inference(resolution,[status(thm)],[c_60,c_207])).

tff(c_212,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_20,c_59,c_209])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_163,c_212])).

tff(c_215,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_217,plain,(
    ! [A_207,B_204,F_205,E_203,D_206,C_208] :
      ( v1_funct_1(k10_tmap_1(A_207,B_204,C_208,D_206,E_203,F_205))
      | ~ r4_tsep_1(A_207,C_208,D_206)
      | ~ r2_funct_2(u1_struct_0(D_206),u1_struct_0(B_204),k3_tmap_1(A_207,B_204,k1_tsep_1(A_207,C_208,D_206),D_206,k10_tmap_1(A_207,B_204,C_208,D_206,E_203,F_205)),F_205)
      | ~ r2_funct_2(u1_struct_0(C_208),u1_struct_0(B_204),k3_tmap_1(A_207,B_204,k1_tsep_1(A_207,C_208,D_206),C_208,k10_tmap_1(A_207,B_204,C_208,D_206,E_203,F_205)),E_203)
      | ~ m1_subset_1(F_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206),u1_struct_0(B_204))))
      | ~ v5_pre_topc(F_205,D_206,B_204)
      | ~ v1_funct_2(F_205,u1_struct_0(D_206),u1_struct_0(B_204))
      | ~ v1_funct_1(F_205)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_208),u1_struct_0(B_204))))
      | ~ v5_pre_topc(E_203,C_208,B_204)
      | ~ v1_funct_2(E_203,u1_struct_0(C_208),u1_struct_0(B_204))
      | ~ v1_funct_1(E_203)
      | k1_tsep_1(A_207,C_208,D_206) != A_207
      | ~ m1_pre_topc(D_206,A_207)
      | v2_struct_0(D_206)
      | ~ m1_pre_topc(C_208,A_207)
      | v2_struct_0(C_208)
      | ~ l1_pre_topc(B_204)
      | ~ v2_pre_topc(B_204)
      | v2_struct_0(B_204)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_219,plain,(
    ! [B_204,E_203,F_205] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_204),k3_tmap_1('#skF_1',B_204,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205)),F_205)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_204),k3_tmap_1('#skF_1',B_204,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205)),E_203)
      | ~ m1_subset_1(F_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_204))))
      | ~ v5_pre_topc(F_205,'#skF_4',B_204)
      | ~ v1_funct_2(F_205,u1_struct_0('#skF_4'),u1_struct_0(B_204))
      | ~ v1_funct_1(F_205)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_204))))
      | ~ v5_pre_topc(E_203,'#skF_3',B_204)
      | ~ v1_funct_2(E_203,u1_struct_0('#skF_3'),u1_struct_0(B_204))
      | ~ v1_funct_1(E_203)
      | k1_tsep_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_204)
      | ~ v2_pre_topc(B_204)
      | v2_struct_0(B_204)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_217])).

tff(c_221,plain,(
    ! [B_204,E_203,F_205] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_204),k3_tmap_1('#skF_1',B_204,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205)),F_205)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_204),k3_tmap_1('#skF_1',B_204,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205)),E_203)
      | ~ m1_subset_1(F_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_204))))
      | ~ v5_pre_topc(F_205,'#skF_4',B_204)
      | ~ v1_funct_2(F_205,u1_struct_0('#skF_4'),u1_struct_0(B_204))
      | ~ v1_funct_1(F_205)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_204))))
      | ~ v5_pre_topc(E_203,'#skF_3',B_204)
      | ~ v1_funct_2(E_203,u1_struct_0('#skF_3'),u1_struct_0(B_204))
      | ~ v1_funct_1(E_203)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_204)
      | ~ v2_pre_topc(B_204)
      | v2_struct_0(B_204)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_36,c_18,c_18,c_219])).

tff(c_222,plain,(
    ! [B_204,E_203,F_205] :
      ( v1_funct_1(k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205))
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_204),k3_tmap_1('#skF_1',B_204,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205)),F_205)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_204),k3_tmap_1('#skF_1',B_204,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_204,'#skF_3','#skF_4',E_203,F_205)),E_203)
      | ~ m1_subset_1(F_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_204))))
      | ~ v5_pre_topc(F_205,'#skF_4',B_204)
      | ~ v1_funct_2(F_205,u1_struct_0('#skF_4'),u1_struct_0(B_204))
      | ~ v1_funct_1(F_205)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_204))))
      | ~ v5_pre_topc(E_203,'#skF_3',B_204)
      | ~ v1_funct_2(E_203,u1_struct_0('#skF_3'),u1_struct_0(B_204))
      | ~ v1_funct_1(E_203)
      | ~ l1_pre_topc(B_204)
      | ~ v2_pre_topc(B_204)
      | v2_struct_0(B_204) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_40,c_221])).

tff(c_223,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_226,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_223])).

tff(c_229,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_38,c_36,c_226])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_229])).

tff(c_233,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_234,plain,(
    ! [A_213,B_210,D_212,E_209,C_214,F_211] :
      ( v5_pre_topc(k10_tmap_1(A_213,B_210,C_214,D_212,E_209,F_211),A_213,B_210)
      | ~ r4_tsep_1(A_213,C_214,D_212)
      | ~ r2_funct_2(u1_struct_0(D_212),u1_struct_0(B_210),k3_tmap_1(A_213,B_210,k1_tsep_1(A_213,C_214,D_212),D_212,k10_tmap_1(A_213,B_210,C_214,D_212,E_209,F_211)),F_211)
      | ~ r2_funct_2(u1_struct_0(C_214),u1_struct_0(B_210),k3_tmap_1(A_213,B_210,k1_tsep_1(A_213,C_214,D_212),C_214,k10_tmap_1(A_213,B_210,C_214,D_212,E_209,F_211)),E_209)
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_212),u1_struct_0(B_210))))
      | ~ v5_pre_topc(F_211,D_212,B_210)
      | ~ v1_funct_2(F_211,u1_struct_0(D_212),u1_struct_0(B_210))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_214),u1_struct_0(B_210))))
      | ~ v5_pre_topc(E_209,C_214,B_210)
      | ~ v1_funct_2(E_209,u1_struct_0(C_214),u1_struct_0(B_210))
      | ~ v1_funct_1(E_209)
      | k1_tsep_1(A_213,C_214,D_212) != A_213
      | ~ m1_pre_topc(D_212,A_213)
      | v2_struct_0(D_212)
      | ~ m1_pre_topc(C_214,A_213)
      | v2_struct_0(C_214)
      | ~ l1_pre_topc(B_210)
      | ~ v2_pre_topc(B_210)
      | v2_struct_0(B_210)
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_236,plain,(
    ! [B_210,E_209,F_211] :
      ( v5_pre_topc(k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211),'#skF_1',B_210)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_210),k3_tmap_1('#skF_1',B_210,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211)),F_211)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_210),k3_tmap_1('#skF_1',B_210,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211)),E_209)
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_210))))
      | ~ v5_pre_topc(F_211,'#skF_4',B_210)
      | ~ v1_funct_2(F_211,u1_struct_0('#skF_4'),u1_struct_0(B_210))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_210))))
      | ~ v5_pre_topc(E_209,'#skF_3',B_210)
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_210))
      | ~ v1_funct_1(E_209)
      | k1_tsep_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_210)
      | ~ v2_pre_topc(B_210)
      | v2_struct_0(B_210)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_234])).

tff(c_238,plain,(
    ! [B_210,E_209,F_211] :
      ( v5_pre_topc(k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211),'#skF_1',B_210)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_210),k3_tmap_1('#skF_1',B_210,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211)),F_211)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_210),k3_tmap_1('#skF_1',B_210,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211)),E_209)
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_210))))
      | ~ v5_pre_topc(F_211,'#skF_4',B_210)
      | ~ v1_funct_2(F_211,u1_struct_0('#skF_4'),u1_struct_0(B_210))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_210))))
      | ~ v5_pre_topc(E_209,'#skF_3',B_210)
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_210))
      | ~ v1_funct_1(E_209)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_210)
      | ~ v2_pre_topc(B_210)
      | v2_struct_0(B_210)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_36,c_18,c_18,c_236])).

tff(c_239,plain,(
    ! [B_210,E_209,F_211] :
      ( v5_pre_topc(k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211),'#skF_1',B_210)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_210),k3_tmap_1('#skF_1',B_210,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211)),F_211)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_210),k3_tmap_1('#skF_1',B_210,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_210,'#skF_3','#skF_4',E_209,F_211)),E_209)
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_210))))
      | ~ v5_pre_topc(F_211,'#skF_4',B_210)
      | ~ v1_funct_2(F_211,u1_struct_0('#skF_4'),u1_struct_0(B_210))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_210))))
      | ~ v5_pre_topc(E_209,'#skF_3',B_210)
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_210))
      | ~ v1_funct_1(E_209)
      | ~ l1_pre_topc(B_210)
      | ~ v2_pre_topc(B_210)
      | v2_struct_0(B_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_40,c_238])).

tff(c_249,plain,(
    ! [B_218,E_219,F_220] :
      ( v5_pre_topc(k10_tmap_1('#skF_1',B_218,'#skF_3','#skF_4',E_219,F_220),'#skF_1',B_218)
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_218),k3_tmap_1('#skF_1',B_218,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_218,'#skF_3','#skF_4',E_219,F_220)),F_220)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_218),k3_tmap_1('#skF_1',B_218,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_218,'#skF_3','#skF_4',E_219,F_220)),E_219)
      | ~ m1_subset_1(F_220,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_218))))
      | ~ v5_pre_topc(F_220,'#skF_4',B_218)
      | ~ v1_funct_2(F_220,u1_struct_0('#skF_4'),u1_struct_0(B_218))
      | ~ v1_funct_1(F_220)
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_218))))
      | ~ v5_pre_topc(E_219,'#skF_3',B_218)
      | ~ v1_funct_2(E_219,u1_struct_0('#skF_3'),u1_struct_0(B_218))
      | ~ v1_funct_1(E_219)
      | ~ l1_pre_topc(B_218)
      | ~ v2_pre_topc(B_218)
      | v2_struct_0(B_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_239])).

tff(c_251,plain,
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
    inference(resolution,[status(thm)],[c_60,c_249])).

tff(c_254,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_32,c_30,c_28,c_26,c_24,c_22,c_20,c_59,c_251])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_215,c_254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.51  
% 3.33/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.51  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.51  
% 3.33/1.51  %Foreground sorts:
% 3.33/1.51  
% 3.33/1.51  
% 3.33/1.51  %Background operators:
% 3.33/1.51  
% 3.33/1.51  
% 3.33/1.51  %Foreground operators:
% 3.33/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.51  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.33/1.51  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.51  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 3.33/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.51  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.33/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.51  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.33/1.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.33/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.51  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.33/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.51  
% 3.59/1.54  tff(f_169, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_tsep_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, A)) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((A = k1_tsep_1(A, C, D)) & r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E)) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_tmap_1)).
% 3.59/1.54  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((v1_tsep_1(C, A) & m1_pre_topc(C, A)) => r4_tsep_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tsep_1)).
% 3.59/1.54  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_tmap_1)).
% 3.59/1.54  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_12, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_66, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_12])).
% 3.59/1.54  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_30, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_26, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_24, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_22, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_20, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_18, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_16, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_59, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 3.59/1.54  tff(c_14, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_60, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 3.59/1.54  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_44, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_38, plain, (v1_tsep_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_10, plain, (![A_64, B_68, C_70]: (r4_tsep_1(A_64, B_68, C_70) | ~m1_pre_topc(C_70, A_64) | ~v1_tsep_1(C_70, A_64) | ~m1_pre_topc(B_68, A_64) | ~v1_tsep_1(B_68, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.59/1.54  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.59/1.54  tff(c_67, plain, (![C_136, B_132, D_134, E_131, F_133, A_135]: (v1_funct_1(k10_tmap_1(A_135, B_132, C_136, D_134, E_131, F_133)) | ~r4_tsep_1(A_135, C_136, D_134) | ~r2_funct_2(u1_struct_0(D_134), u1_struct_0(B_132), k3_tmap_1(A_135, B_132, k1_tsep_1(A_135, C_136, D_134), D_134, k10_tmap_1(A_135, B_132, C_136, D_134, E_131, F_133)), F_133) | ~r2_funct_2(u1_struct_0(C_136), u1_struct_0(B_132), k3_tmap_1(A_135, B_132, k1_tsep_1(A_135, C_136, D_134), C_136, k10_tmap_1(A_135, B_132, C_136, D_134, E_131, F_133)), E_131) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_134), u1_struct_0(B_132)))) | ~v5_pre_topc(F_133, D_134, B_132) | ~v1_funct_2(F_133, u1_struct_0(D_134), u1_struct_0(B_132)) | ~v1_funct_1(F_133) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_136), u1_struct_0(B_132)))) | ~v5_pre_topc(E_131, C_136, B_132) | ~v1_funct_2(E_131, u1_struct_0(C_136), u1_struct_0(B_132)) | ~v1_funct_1(E_131) | k1_tsep_1(A_135, C_136, D_134)!=A_135 | ~m1_pre_topc(D_134, A_135) | v2_struct_0(D_134) | ~m1_pre_topc(C_136, A_135) | v2_struct_0(C_136) | ~l1_pre_topc(B_132) | ~v2_pre_topc(B_132) | v2_struct_0(B_132) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.54  tff(c_69, plain, (![B_132, E_131, F_133]: (v1_funct_1(k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_132), k3_tmap_1('#skF_1', B_132, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)), F_133) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_132), k3_tmap_1('#skF_1', B_132, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)), E_131) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_132)))) | ~v5_pre_topc(F_133, '#skF_4', B_132) | ~v1_funct_2(F_133, u1_struct_0('#skF_4'), u1_struct_0(B_132)) | ~v1_funct_1(F_133) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_132)))) | ~v5_pre_topc(E_131, '#skF_3', B_132) | ~v1_funct_2(E_131, u1_struct_0('#skF_3'), u1_struct_0(B_132)) | ~v1_funct_1(E_131) | k1_tsep_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_132) | ~v2_pre_topc(B_132) | v2_struct_0(B_132) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_67])).
% 3.59/1.54  tff(c_71, plain, (![B_132, E_131, F_133]: (v1_funct_1(k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_132), k3_tmap_1('#skF_1', B_132, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)), F_133) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_132), k3_tmap_1('#skF_1', B_132, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)), E_131) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_132)))) | ~v5_pre_topc(F_133, '#skF_4', B_132) | ~v1_funct_2(F_133, u1_struct_0('#skF_4'), u1_struct_0(B_132)) | ~v1_funct_1(F_133) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_132)))) | ~v5_pre_topc(E_131, '#skF_3', B_132) | ~v1_funct_2(E_131, u1_struct_0('#skF_3'), u1_struct_0(B_132)) | ~v1_funct_1(E_131) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_132) | ~v2_pre_topc(B_132) | v2_struct_0(B_132) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_36, c_18, c_18, c_69])).
% 3.59/1.54  tff(c_72, plain, (![B_132, E_131, F_133]: (v1_funct_1(k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_132), k3_tmap_1('#skF_1', B_132, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)), F_133) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_132), k3_tmap_1('#skF_1', B_132, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_132, '#skF_3', '#skF_4', E_131, F_133)), E_131) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_132)))) | ~v5_pre_topc(F_133, '#skF_4', B_132) | ~v1_funct_2(F_133, u1_struct_0('#skF_4'), u1_struct_0(B_132)) | ~v1_funct_1(F_133) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_132)))) | ~v5_pre_topc(E_131, '#skF_3', B_132) | ~v1_funct_2(E_131, u1_struct_0('#skF_3'), u1_struct_0(B_132)) | ~v1_funct_1(E_131) | ~l1_pre_topc(B_132) | ~v2_pre_topc(B_132) | v2_struct_0(B_132))), inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_40, c_71])).
% 3.59/1.54  tff(c_73, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_72])).
% 3.59/1.54  tff(c_76, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_73])).
% 3.59/1.54  tff(c_79, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_38, c_36, c_76])).
% 3.59/1.54  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_79])).
% 3.59/1.54  tff(c_84, plain, (![B_137, E_138, F_139]: (v1_funct_1(k10_tmap_1('#skF_1', B_137, '#skF_3', '#skF_4', E_138, F_139)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_137), k3_tmap_1('#skF_1', B_137, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_137, '#skF_3', '#skF_4', E_138, F_139)), F_139) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_137), k3_tmap_1('#skF_1', B_137, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_137, '#skF_3', '#skF_4', E_138, F_139)), E_138) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_137)))) | ~v5_pre_topc(F_139, '#skF_4', B_137) | ~v1_funct_2(F_139, u1_struct_0('#skF_4'), u1_struct_0(B_137)) | ~v1_funct_1(F_139) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_137)))) | ~v5_pre_topc(E_138, '#skF_3', B_137) | ~v1_funct_2(E_138, u1_struct_0('#skF_3'), u1_struct_0(B_137)) | ~v1_funct_1(E_138) | ~l1_pre_topc(B_137) | ~v2_pre_topc(B_137) | v2_struct_0(B_137))), inference(splitRight, [status(thm)], [c_72])).
% 3.59/1.54  tff(c_86, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_84])).
% 3.59/1.54  tff(c_89, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_32, c_30, c_28, c_26, c_24, c_22, c_20, c_59, c_86])).
% 3.59/1.54  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_66, c_89])).
% 3.59/1.54  tff(c_92, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_12])).
% 3.59/1.54  tff(c_94, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_92])).
% 3.59/1.54  tff(c_95, plain, (![E_140, F_142, A_144, D_143, C_145, B_141]: (v1_funct_1(k10_tmap_1(A_144, B_141, C_145, D_143, E_140, F_142)) | ~r4_tsep_1(A_144, C_145, D_143) | ~r2_funct_2(u1_struct_0(D_143), u1_struct_0(B_141), k3_tmap_1(A_144, B_141, k1_tsep_1(A_144, C_145, D_143), D_143, k10_tmap_1(A_144, B_141, C_145, D_143, E_140, F_142)), F_142) | ~r2_funct_2(u1_struct_0(C_145), u1_struct_0(B_141), k3_tmap_1(A_144, B_141, k1_tsep_1(A_144, C_145, D_143), C_145, k10_tmap_1(A_144, B_141, C_145, D_143, E_140, F_142)), E_140) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_143), u1_struct_0(B_141)))) | ~v5_pre_topc(F_142, D_143, B_141) | ~v1_funct_2(F_142, u1_struct_0(D_143), u1_struct_0(B_141)) | ~v1_funct_1(F_142) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_145), u1_struct_0(B_141)))) | ~v5_pre_topc(E_140, C_145, B_141) | ~v1_funct_2(E_140, u1_struct_0(C_145), u1_struct_0(B_141)) | ~v1_funct_1(E_140) | k1_tsep_1(A_144, C_145, D_143)!=A_144 | ~m1_pre_topc(D_143, A_144) | v2_struct_0(D_143) | ~m1_pre_topc(C_145, A_144) | v2_struct_0(C_145) | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.54  tff(c_97, plain, (![B_141, E_140, F_142]: (v1_funct_1(k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_141), k3_tmap_1('#skF_1', B_141, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)), F_142) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_141), k3_tmap_1('#skF_1', B_141, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)), E_140) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_141)))) | ~v5_pre_topc(F_142, '#skF_4', B_141) | ~v1_funct_2(F_142, u1_struct_0('#skF_4'), u1_struct_0(B_141)) | ~v1_funct_1(F_142) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_141)))) | ~v5_pre_topc(E_140, '#skF_3', B_141) | ~v1_funct_2(E_140, u1_struct_0('#skF_3'), u1_struct_0(B_141)) | ~v1_funct_1(E_140) | k1_tsep_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_95])).
% 3.59/1.54  tff(c_99, plain, (![B_141, E_140, F_142]: (v1_funct_1(k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_141), k3_tmap_1('#skF_1', B_141, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)), F_142) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_141), k3_tmap_1('#skF_1', B_141, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)), E_140) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_141)))) | ~v5_pre_topc(F_142, '#skF_4', B_141) | ~v1_funct_2(F_142, u1_struct_0('#skF_4'), u1_struct_0(B_141)) | ~v1_funct_1(F_142) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_141)))) | ~v5_pre_topc(E_140, '#skF_3', B_141) | ~v1_funct_2(E_140, u1_struct_0('#skF_3'), u1_struct_0(B_141)) | ~v1_funct_1(E_140) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_36, c_18, c_18, c_97])).
% 3.59/1.54  tff(c_100, plain, (![B_141, E_140, F_142]: (v1_funct_1(k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_141), k3_tmap_1('#skF_1', B_141, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)), F_142) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_141), k3_tmap_1('#skF_1', B_141, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_141, '#skF_3', '#skF_4', E_140, F_142)), E_140) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_141)))) | ~v5_pre_topc(F_142, '#skF_4', B_141) | ~v1_funct_2(F_142, u1_struct_0('#skF_4'), u1_struct_0(B_141)) | ~v1_funct_1(F_142) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_141)))) | ~v5_pre_topc(E_140, '#skF_3', B_141) | ~v1_funct_2(E_140, u1_struct_0('#skF_3'), u1_struct_0(B_141)) | ~v1_funct_1(E_140) | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141))), inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_40, c_99])).
% 3.59/1.54  tff(c_107, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_100])).
% 3.59/1.54  tff(c_110, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_107])).
% 3.59/1.54  tff(c_113, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_38, c_36, c_110])).
% 3.59/1.54  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_113])).
% 3.59/1.54  tff(c_117, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_100])).
% 3.59/1.54  tff(c_147, plain, (![D_170, A_171, E_167, B_168, C_172, F_169]: (m1_subset_1(k10_tmap_1(A_171, B_168, C_172, D_170, E_167, F_169), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), u1_struct_0(B_168)))) | ~r4_tsep_1(A_171, C_172, D_170) | ~r2_funct_2(u1_struct_0(D_170), u1_struct_0(B_168), k3_tmap_1(A_171, B_168, k1_tsep_1(A_171, C_172, D_170), D_170, k10_tmap_1(A_171, B_168, C_172, D_170, E_167, F_169)), F_169) | ~r2_funct_2(u1_struct_0(C_172), u1_struct_0(B_168), k3_tmap_1(A_171, B_168, k1_tsep_1(A_171, C_172, D_170), C_172, k10_tmap_1(A_171, B_168, C_172, D_170, E_167, F_169)), E_167) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_170), u1_struct_0(B_168)))) | ~v5_pre_topc(F_169, D_170, B_168) | ~v1_funct_2(F_169, u1_struct_0(D_170), u1_struct_0(B_168)) | ~v1_funct_1(F_169) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_172), u1_struct_0(B_168)))) | ~v5_pre_topc(E_167, C_172, B_168) | ~v1_funct_2(E_167, u1_struct_0(C_172), u1_struct_0(B_168)) | ~v1_funct_1(E_167) | k1_tsep_1(A_171, C_172, D_170)!=A_171 | ~m1_pre_topc(D_170, A_171) | v2_struct_0(D_170) | ~m1_pre_topc(C_172, A_171) | v2_struct_0(C_172) | ~l1_pre_topc(B_168) | ~v2_pre_topc(B_168) | v2_struct_0(B_168) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.54  tff(c_149, plain, (![B_168, E_167, F_169]: (m1_subset_1(k10_tmap_1('#skF_1', B_168, '#skF_3', '#skF_4', E_167, F_169), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_168)))) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_168), k3_tmap_1('#skF_1', B_168, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_168, '#skF_3', '#skF_4', E_167, F_169)), F_169) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_168), k3_tmap_1('#skF_1', B_168, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_168, '#skF_3', '#skF_4', E_167, F_169)), E_167) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_168)))) | ~v5_pre_topc(F_169, '#skF_4', B_168) | ~v1_funct_2(F_169, u1_struct_0('#skF_4'), u1_struct_0(B_168)) | ~v1_funct_1(F_169) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_168)))) | ~v5_pre_topc(E_167, '#skF_3', B_168) | ~v1_funct_2(E_167, u1_struct_0('#skF_3'), u1_struct_0(B_168)) | ~v1_funct_1(E_167) | k1_tsep_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_168) | ~v2_pre_topc(B_168) | v2_struct_0(B_168) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_147])).
% 3.59/1.54  tff(c_151, plain, (![B_168, E_167, F_169]: (m1_subset_1(k10_tmap_1('#skF_1', B_168, '#skF_3', '#skF_4', E_167, F_169), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_168)))) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_168), k3_tmap_1('#skF_1', B_168, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_168, '#skF_3', '#skF_4', E_167, F_169)), F_169) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_168), k3_tmap_1('#skF_1', B_168, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_168, '#skF_3', '#skF_4', E_167, F_169)), E_167) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_168)))) | ~v5_pre_topc(F_169, '#skF_4', B_168) | ~v1_funct_2(F_169, u1_struct_0('#skF_4'), u1_struct_0(B_168)) | ~v1_funct_1(F_169) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_168)))) | ~v5_pre_topc(E_167, '#skF_3', B_168) | ~v1_funct_2(E_167, u1_struct_0('#skF_3'), u1_struct_0(B_168)) | ~v1_funct_1(E_167) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_168) | ~v2_pre_topc(B_168) | v2_struct_0(B_168) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_36, c_18, c_18, c_117, c_149])).
% 3.59/1.54  tff(c_153, plain, (![B_173, E_174, F_175]: (m1_subset_1(k10_tmap_1('#skF_1', B_173, '#skF_3', '#skF_4', E_174, F_175), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_173)))) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_173), k3_tmap_1('#skF_1', B_173, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_173, '#skF_3', '#skF_4', E_174, F_175)), F_175) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_173), k3_tmap_1('#skF_1', B_173, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_173, '#skF_3', '#skF_4', E_174, F_175)), E_174) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_173)))) | ~v5_pre_topc(F_175, '#skF_4', B_173) | ~v1_funct_2(F_175, u1_struct_0('#skF_4'), u1_struct_0(B_173)) | ~v1_funct_1(F_175) | ~m1_subset_1(E_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_173)))) | ~v5_pre_topc(E_174, '#skF_3', B_173) | ~v1_funct_2(E_174, u1_struct_0('#skF_3'), u1_struct_0(B_173)) | ~v1_funct_1(E_174) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173))), inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_40, c_151])).
% 3.59/1.54  tff(c_155, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_153])).
% 3.59/1.54  tff(c_158, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_32, c_30, c_28, c_26, c_24, c_22, c_20, c_59, c_155])).
% 3.59/1.54  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_94, c_158])).
% 3.59/1.54  tff(c_161, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_92])).
% 3.59/1.54  tff(c_163, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_161])).
% 3.59/1.54  tff(c_164, plain, (![B_177, F_178, D_179, C_181, E_176, A_180]: (v1_funct_1(k10_tmap_1(A_180, B_177, C_181, D_179, E_176, F_178)) | ~r4_tsep_1(A_180, C_181, D_179) | ~r2_funct_2(u1_struct_0(D_179), u1_struct_0(B_177), k3_tmap_1(A_180, B_177, k1_tsep_1(A_180, C_181, D_179), D_179, k10_tmap_1(A_180, B_177, C_181, D_179, E_176, F_178)), F_178) | ~r2_funct_2(u1_struct_0(C_181), u1_struct_0(B_177), k3_tmap_1(A_180, B_177, k1_tsep_1(A_180, C_181, D_179), C_181, k10_tmap_1(A_180, B_177, C_181, D_179, E_176, F_178)), E_176) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179), u1_struct_0(B_177)))) | ~v5_pre_topc(F_178, D_179, B_177) | ~v1_funct_2(F_178, u1_struct_0(D_179), u1_struct_0(B_177)) | ~v1_funct_1(F_178) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_181), u1_struct_0(B_177)))) | ~v5_pre_topc(E_176, C_181, B_177) | ~v1_funct_2(E_176, u1_struct_0(C_181), u1_struct_0(B_177)) | ~v1_funct_1(E_176) | k1_tsep_1(A_180, C_181, D_179)!=A_180 | ~m1_pre_topc(D_179, A_180) | v2_struct_0(D_179) | ~m1_pre_topc(C_181, A_180) | v2_struct_0(C_181) | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.54  tff(c_166, plain, (![B_177, E_176, F_178]: (v1_funct_1(k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_177), k3_tmap_1('#skF_1', B_177, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)), F_178) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_177), k3_tmap_1('#skF_1', B_177, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)), E_176) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_177)))) | ~v5_pre_topc(F_178, '#skF_4', B_177) | ~v1_funct_2(F_178, u1_struct_0('#skF_4'), u1_struct_0(B_177)) | ~v1_funct_1(F_178) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_177)))) | ~v5_pre_topc(E_176, '#skF_3', B_177) | ~v1_funct_2(E_176, u1_struct_0('#skF_3'), u1_struct_0(B_177)) | ~v1_funct_1(E_176) | k1_tsep_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_164])).
% 3.59/1.54  tff(c_168, plain, (![B_177, E_176, F_178]: (v1_funct_1(k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_177), k3_tmap_1('#skF_1', B_177, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)), F_178) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_177), k3_tmap_1('#skF_1', B_177, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)), E_176) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_177)))) | ~v5_pre_topc(F_178, '#skF_4', B_177) | ~v1_funct_2(F_178, u1_struct_0('#skF_4'), u1_struct_0(B_177)) | ~v1_funct_1(F_178) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_177)))) | ~v5_pre_topc(E_176, '#skF_3', B_177) | ~v1_funct_2(E_176, u1_struct_0('#skF_3'), u1_struct_0(B_177)) | ~v1_funct_1(E_176) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_36, c_18, c_18, c_166])).
% 3.59/1.54  tff(c_169, plain, (![B_177, E_176, F_178]: (v1_funct_1(k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_177), k3_tmap_1('#skF_1', B_177, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)), F_178) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_177), k3_tmap_1('#skF_1', B_177, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_177, '#skF_3', '#skF_4', E_176, F_178)), E_176) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_177)))) | ~v5_pre_topc(F_178, '#skF_4', B_177) | ~v1_funct_2(F_178, u1_struct_0('#skF_4'), u1_struct_0(B_177)) | ~v1_funct_1(F_178) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_177)))) | ~v5_pre_topc(E_176, '#skF_3', B_177) | ~v1_funct_2(E_176, u1_struct_0('#skF_3'), u1_struct_0(B_177)) | ~v1_funct_1(E_176) | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177))), inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_40, c_168])).
% 3.59/1.54  tff(c_170, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_169])).
% 3.59/1.54  tff(c_173, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_170])).
% 3.59/1.54  tff(c_176, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_38, c_36, c_173])).
% 3.59/1.54  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_176])).
% 3.59/1.54  tff(c_180, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_169])).
% 3.59/1.54  tff(c_201, plain, (![F_196, C_199, E_194, A_198, D_197, B_195]: (v1_funct_2(k10_tmap_1(A_198, B_195, C_199, D_197, E_194, F_196), u1_struct_0(A_198), u1_struct_0(B_195)) | ~r4_tsep_1(A_198, C_199, D_197) | ~r2_funct_2(u1_struct_0(D_197), u1_struct_0(B_195), k3_tmap_1(A_198, B_195, k1_tsep_1(A_198, C_199, D_197), D_197, k10_tmap_1(A_198, B_195, C_199, D_197, E_194, F_196)), F_196) | ~r2_funct_2(u1_struct_0(C_199), u1_struct_0(B_195), k3_tmap_1(A_198, B_195, k1_tsep_1(A_198, C_199, D_197), C_199, k10_tmap_1(A_198, B_195, C_199, D_197, E_194, F_196)), E_194) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_197), u1_struct_0(B_195)))) | ~v5_pre_topc(F_196, D_197, B_195) | ~v1_funct_2(F_196, u1_struct_0(D_197), u1_struct_0(B_195)) | ~v1_funct_1(F_196) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_199), u1_struct_0(B_195)))) | ~v5_pre_topc(E_194, C_199, B_195) | ~v1_funct_2(E_194, u1_struct_0(C_199), u1_struct_0(B_195)) | ~v1_funct_1(E_194) | k1_tsep_1(A_198, C_199, D_197)!=A_198 | ~m1_pre_topc(D_197, A_198) | v2_struct_0(D_197) | ~m1_pre_topc(C_199, A_198) | v2_struct_0(C_199) | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.54  tff(c_203, plain, (![B_195, E_194, F_196]: (v1_funct_2(k10_tmap_1('#skF_1', B_195, '#skF_3', '#skF_4', E_194, F_196), u1_struct_0('#skF_1'), u1_struct_0(B_195)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_195), k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_195, '#skF_3', '#skF_4', E_194, F_196)), F_196) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_195), k3_tmap_1('#skF_1', B_195, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_195, '#skF_3', '#skF_4', E_194, F_196)), E_194) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_195)))) | ~v5_pre_topc(F_196, '#skF_4', B_195) | ~v1_funct_2(F_196, u1_struct_0('#skF_4'), u1_struct_0(B_195)) | ~v1_funct_1(F_196) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_195)))) | ~v5_pre_topc(E_194, '#skF_3', B_195) | ~v1_funct_2(E_194, u1_struct_0('#skF_3'), u1_struct_0(B_195)) | ~v1_funct_1(E_194) | k1_tsep_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_201])).
% 3.59/1.54  tff(c_205, plain, (![B_195, E_194, F_196]: (v1_funct_2(k10_tmap_1('#skF_1', B_195, '#skF_3', '#skF_4', E_194, F_196), u1_struct_0('#skF_1'), u1_struct_0(B_195)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_195), k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_195, '#skF_3', '#skF_4', E_194, F_196)), F_196) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_195), k3_tmap_1('#skF_1', B_195, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_195, '#skF_3', '#skF_4', E_194, F_196)), E_194) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_195)))) | ~v5_pre_topc(F_196, '#skF_4', B_195) | ~v1_funct_2(F_196, u1_struct_0('#skF_4'), u1_struct_0(B_195)) | ~v1_funct_1(F_196) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_195)))) | ~v5_pre_topc(E_194, '#skF_3', B_195) | ~v1_funct_2(E_194, u1_struct_0('#skF_3'), u1_struct_0(B_195)) | ~v1_funct_1(E_194) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_36, c_18, c_18, c_180, c_203])).
% 3.59/1.54  tff(c_207, plain, (![B_200, E_201, F_202]: (v1_funct_2(k10_tmap_1('#skF_1', B_200, '#skF_3', '#skF_4', E_201, F_202), u1_struct_0('#skF_1'), u1_struct_0(B_200)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_200), k3_tmap_1('#skF_1', B_200, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_200, '#skF_3', '#skF_4', E_201, F_202)), F_202) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_200), k3_tmap_1('#skF_1', B_200, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_200, '#skF_3', '#skF_4', E_201, F_202)), E_201) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_200)))) | ~v5_pre_topc(F_202, '#skF_4', B_200) | ~v1_funct_2(F_202, u1_struct_0('#skF_4'), u1_struct_0(B_200)) | ~v1_funct_1(F_202) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_200)))) | ~v5_pre_topc(E_201, '#skF_3', B_200) | ~v1_funct_2(E_201, u1_struct_0('#skF_3'), u1_struct_0(B_200)) | ~v1_funct_1(E_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200))), inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_40, c_205])).
% 3.59/1.54  tff(c_209, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_207])).
% 3.59/1.54  tff(c_212, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_32, c_30, c_28, c_26, c_24, c_22, c_20, c_59, c_209])).
% 3.59/1.54  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_163, c_212])).
% 3.59/1.54  tff(c_215, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_161])).
% 3.59/1.54  tff(c_217, plain, (![A_207, B_204, F_205, E_203, D_206, C_208]: (v1_funct_1(k10_tmap_1(A_207, B_204, C_208, D_206, E_203, F_205)) | ~r4_tsep_1(A_207, C_208, D_206) | ~r2_funct_2(u1_struct_0(D_206), u1_struct_0(B_204), k3_tmap_1(A_207, B_204, k1_tsep_1(A_207, C_208, D_206), D_206, k10_tmap_1(A_207, B_204, C_208, D_206, E_203, F_205)), F_205) | ~r2_funct_2(u1_struct_0(C_208), u1_struct_0(B_204), k3_tmap_1(A_207, B_204, k1_tsep_1(A_207, C_208, D_206), C_208, k10_tmap_1(A_207, B_204, C_208, D_206, E_203, F_205)), E_203) | ~m1_subset_1(F_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_206), u1_struct_0(B_204)))) | ~v5_pre_topc(F_205, D_206, B_204) | ~v1_funct_2(F_205, u1_struct_0(D_206), u1_struct_0(B_204)) | ~v1_funct_1(F_205) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_208), u1_struct_0(B_204)))) | ~v5_pre_topc(E_203, C_208, B_204) | ~v1_funct_2(E_203, u1_struct_0(C_208), u1_struct_0(B_204)) | ~v1_funct_1(E_203) | k1_tsep_1(A_207, C_208, D_206)!=A_207 | ~m1_pre_topc(D_206, A_207) | v2_struct_0(D_206) | ~m1_pre_topc(C_208, A_207) | v2_struct_0(C_208) | ~l1_pre_topc(B_204) | ~v2_pre_topc(B_204) | v2_struct_0(B_204) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.55  tff(c_219, plain, (![B_204, E_203, F_205]: (v1_funct_1(k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_204), k3_tmap_1('#skF_1', B_204, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)), F_205) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_204), k3_tmap_1('#skF_1', B_204, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)), E_203) | ~m1_subset_1(F_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_204)))) | ~v5_pre_topc(F_205, '#skF_4', B_204) | ~v1_funct_2(F_205, u1_struct_0('#skF_4'), u1_struct_0(B_204)) | ~v1_funct_1(F_205) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_204)))) | ~v5_pre_topc(E_203, '#skF_3', B_204) | ~v1_funct_2(E_203, u1_struct_0('#skF_3'), u1_struct_0(B_204)) | ~v1_funct_1(E_203) | k1_tsep_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_204) | ~v2_pre_topc(B_204) | v2_struct_0(B_204) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_217])).
% 3.59/1.55  tff(c_221, plain, (![B_204, E_203, F_205]: (v1_funct_1(k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_204), k3_tmap_1('#skF_1', B_204, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)), F_205) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_204), k3_tmap_1('#skF_1', B_204, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)), E_203) | ~m1_subset_1(F_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_204)))) | ~v5_pre_topc(F_205, '#skF_4', B_204) | ~v1_funct_2(F_205, u1_struct_0('#skF_4'), u1_struct_0(B_204)) | ~v1_funct_1(F_205) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_204)))) | ~v5_pre_topc(E_203, '#skF_3', B_204) | ~v1_funct_2(E_203, u1_struct_0('#skF_3'), u1_struct_0(B_204)) | ~v1_funct_1(E_203) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_204) | ~v2_pre_topc(B_204) | v2_struct_0(B_204) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_36, c_18, c_18, c_219])).
% 3.59/1.55  tff(c_222, plain, (![B_204, E_203, F_205]: (v1_funct_1(k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_204), k3_tmap_1('#skF_1', B_204, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)), F_205) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_204), k3_tmap_1('#skF_1', B_204, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_204, '#skF_3', '#skF_4', E_203, F_205)), E_203) | ~m1_subset_1(F_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_204)))) | ~v5_pre_topc(F_205, '#skF_4', B_204) | ~v1_funct_2(F_205, u1_struct_0('#skF_4'), u1_struct_0(B_204)) | ~v1_funct_1(F_205) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_204)))) | ~v5_pre_topc(E_203, '#skF_3', B_204) | ~v1_funct_2(E_203, u1_struct_0('#skF_3'), u1_struct_0(B_204)) | ~v1_funct_1(E_203) | ~l1_pre_topc(B_204) | ~v2_pre_topc(B_204) | v2_struct_0(B_204))), inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_40, c_221])).
% 3.59/1.55  tff(c_223, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_222])).
% 3.59/1.55  tff(c_226, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_223])).
% 3.59/1.55  tff(c_229, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_38, c_36, c_226])).
% 3.59/1.55  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_229])).
% 3.59/1.55  tff(c_233, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_222])).
% 3.59/1.55  tff(c_234, plain, (![A_213, B_210, D_212, E_209, C_214, F_211]: (v5_pre_topc(k10_tmap_1(A_213, B_210, C_214, D_212, E_209, F_211), A_213, B_210) | ~r4_tsep_1(A_213, C_214, D_212) | ~r2_funct_2(u1_struct_0(D_212), u1_struct_0(B_210), k3_tmap_1(A_213, B_210, k1_tsep_1(A_213, C_214, D_212), D_212, k10_tmap_1(A_213, B_210, C_214, D_212, E_209, F_211)), F_211) | ~r2_funct_2(u1_struct_0(C_214), u1_struct_0(B_210), k3_tmap_1(A_213, B_210, k1_tsep_1(A_213, C_214, D_212), C_214, k10_tmap_1(A_213, B_210, C_214, D_212, E_209, F_211)), E_209) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_212), u1_struct_0(B_210)))) | ~v5_pre_topc(F_211, D_212, B_210) | ~v1_funct_2(F_211, u1_struct_0(D_212), u1_struct_0(B_210)) | ~v1_funct_1(F_211) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_214), u1_struct_0(B_210)))) | ~v5_pre_topc(E_209, C_214, B_210) | ~v1_funct_2(E_209, u1_struct_0(C_214), u1_struct_0(B_210)) | ~v1_funct_1(E_209) | k1_tsep_1(A_213, C_214, D_212)!=A_213 | ~m1_pre_topc(D_212, A_213) | v2_struct_0(D_212) | ~m1_pre_topc(C_214, A_213) | v2_struct_0(C_214) | ~l1_pre_topc(B_210) | ~v2_pre_topc(B_210) | v2_struct_0(B_210) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.59/1.55  tff(c_236, plain, (![B_210, E_209, F_211]: (v5_pre_topc(k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211), '#skF_1', B_210) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_210), k3_tmap_1('#skF_1', B_210, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211)), F_211) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_210), k3_tmap_1('#skF_1', B_210, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211)), E_209) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_210)))) | ~v5_pre_topc(F_211, '#skF_4', B_210) | ~v1_funct_2(F_211, u1_struct_0('#skF_4'), u1_struct_0(B_210)) | ~v1_funct_1(F_211) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_210)))) | ~v5_pre_topc(E_209, '#skF_3', B_210) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_210)) | ~v1_funct_1(E_209) | k1_tsep_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_210) | ~v2_pre_topc(B_210) | v2_struct_0(B_210) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_234])).
% 3.59/1.55  tff(c_238, plain, (![B_210, E_209, F_211]: (v5_pre_topc(k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211), '#skF_1', B_210) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_210), k3_tmap_1('#skF_1', B_210, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211)), F_211) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_210), k3_tmap_1('#skF_1', B_210, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211)), E_209) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_210)))) | ~v5_pre_topc(F_211, '#skF_4', B_210) | ~v1_funct_2(F_211, u1_struct_0('#skF_4'), u1_struct_0(B_210)) | ~v1_funct_1(F_211) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_210)))) | ~v5_pre_topc(E_209, '#skF_3', B_210) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_210)) | ~v1_funct_1(E_209) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_210) | ~v2_pre_topc(B_210) | v2_struct_0(B_210) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_36, c_18, c_18, c_236])).
% 3.59/1.55  tff(c_239, plain, (![B_210, E_209, F_211]: (v5_pre_topc(k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211), '#skF_1', B_210) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_210), k3_tmap_1('#skF_1', B_210, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211)), F_211) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_210), k3_tmap_1('#skF_1', B_210, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_210, '#skF_3', '#skF_4', E_209, F_211)), E_209) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_210)))) | ~v5_pre_topc(F_211, '#skF_4', B_210) | ~v1_funct_2(F_211, u1_struct_0('#skF_4'), u1_struct_0(B_210)) | ~v1_funct_1(F_211) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_210)))) | ~v5_pre_topc(E_209, '#skF_3', B_210) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_210)) | ~v1_funct_1(E_209) | ~l1_pre_topc(B_210) | ~v2_pre_topc(B_210) | v2_struct_0(B_210))), inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_40, c_238])).
% 3.59/1.55  tff(c_249, plain, (![B_218, E_219, F_220]: (v5_pre_topc(k10_tmap_1('#skF_1', B_218, '#skF_3', '#skF_4', E_219, F_220), '#skF_1', B_218) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_218), k3_tmap_1('#skF_1', B_218, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_218, '#skF_3', '#skF_4', E_219, F_220)), F_220) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_218), k3_tmap_1('#skF_1', B_218, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_218, '#skF_3', '#skF_4', E_219, F_220)), E_219) | ~m1_subset_1(F_220, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_218)))) | ~v5_pre_topc(F_220, '#skF_4', B_218) | ~v1_funct_2(F_220, u1_struct_0('#skF_4'), u1_struct_0(B_218)) | ~v1_funct_1(F_220) | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_218)))) | ~v5_pre_topc(E_219, '#skF_3', B_218) | ~v1_funct_2(E_219, u1_struct_0('#skF_3'), u1_struct_0(B_218)) | ~v1_funct_1(E_219) | ~l1_pre_topc(B_218) | ~v2_pre_topc(B_218) | v2_struct_0(B_218))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_239])).
% 3.59/1.55  tff(c_251, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_249])).
% 3.59/1.55  tff(c_254, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_32, c_30, c_28, c_26, c_24, c_22, c_20, c_59, c_251])).
% 3.59/1.55  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_215, c_254])).
% 3.59/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.55  
% 3.59/1.55  Inference rules
% 3.59/1.55  ----------------------
% 3.59/1.55  #Ref     : 0
% 3.59/1.55  #Sup     : 26
% 3.59/1.55  #Fact    : 0
% 3.59/1.55  #Define  : 0
% 3.59/1.55  #Split   : 7
% 3.59/1.55  #Chain   : 0
% 3.59/1.55  #Close   : 0
% 3.59/1.55  
% 3.59/1.55  Ordering : KBO
% 3.59/1.55  
% 3.59/1.55  Simplification rules
% 3.59/1.55  ----------------------
% 3.59/1.55  #Subsume      : 0
% 3.59/1.55  #Demod        : 205
% 3.59/1.55  #Tautology    : 5
% 3.59/1.55  #SimpNegUnit  : 24
% 3.59/1.55  #BackRed      : 0
% 3.59/1.55  
% 3.59/1.55  #Partial instantiations: 0
% 3.59/1.55  #Strategies tried      : 1
% 3.59/1.55  
% 3.59/1.55  Timing (in seconds)
% 3.59/1.55  ----------------------
% 3.59/1.55  Preprocessing        : 0.37
% 3.59/1.55  Parsing              : 0.19
% 3.59/1.55  CNF conversion       : 0.07
% 3.59/1.55  Main loop            : 0.33
% 3.59/1.55  Inferencing          : 0.13
% 3.59/1.55  Reduction            : 0.11
% 3.59/1.55  Demodulation         : 0.08
% 3.59/1.55  BG Simplification    : 0.02
% 3.59/1.55  Subsumption          : 0.06
% 3.59/1.55  Abstraction          : 0.01
% 3.59/1.55  MUC search           : 0.00
% 3.59/1.55  Cooper               : 0.00
% 3.59/1.55  Total                : 0.77
% 3.59/1.55  Index Insertion      : 0.00
% 3.59/1.55  Index Deletion       : 0.00
% 3.59/1.55  Index Matching       : 0.00
% 3.59/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
