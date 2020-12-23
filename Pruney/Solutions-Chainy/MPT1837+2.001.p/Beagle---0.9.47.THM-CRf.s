%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:13 EST 2020

% Result     : Theorem 8.78s
% Output     : CNFRefutation 9.01s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 885 expanded)
%              Number of leaves         :   34 ( 347 expanded)
%              Depth                    :   10
%              Number of atoms          :  760 (9740 expanded)
%              Number of equality atoms :   14 ( 414 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(f_278,negated_conjecture,(
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

tff(f_83,axiom,(
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

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_135,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_214,axiom,(
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

tff(f_195,axiom,(
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
                 => ( r4_tsep_1(A,C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(E,k1_tsep_1(A,C,D),B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),C,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_88,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_86,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_70,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_62,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_94,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_92,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_80,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_74,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_56,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_885,plain,(
    ! [C_320,D_317,A_321,E_322,B_319,F_318] :
      ( m1_subset_1(k10_tmap_1(A_321,B_319,C_320,D_317,E_322,F_318),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_321,C_320,D_317)),u1_struct_0(B_319))))
      | ~ m1_subset_1(F_318,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_317),u1_struct_0(B_319))))
      | ~ v1_funct_2(F_318,u1_struct_0(D_317),u1_struct_0(B_319))
      | ~ v1_funct_1(F_318)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_320),u1_struct_0(B_319))))
      | ~ v1_funct_2(E_322,u1_struct_0(C_320),u1_struct_0(B_319))
      | ~ v1_funct_1(E_322)
      | ~ m1_pre_topc(D_317,A_321)
      | v2_struct_0(D_317)
      | ~ m1_pre_topc(C_320,A_321)
      | v2_struct_0(C_320)
      | ~ l1_pre_topc(B_319)
      | ~ v2_pre_topc(B_319)
      | v2_struct_0(B_319)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_914,plain,(
    ! [B_319,E_322,F_318] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_319,'#skF_3','#skF_4',E_322,F_318),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_319))))
      | ~ m1_subset_1(F_318,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_319))))
      | ~ v1_funct_2(F_318,u1_struct_0('#skF_4'),u1_struct_0(B_319))
      | ~ v1_funct_1(F_318)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_319))))
      | ~ v1_funct_2(E_322,u1_struct_0('#skF_3'),u1_struct_0(B_319))
      | ~ v1_funct_1(E_322)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_319)
      | ~ v2_pre_topc(B_319)
      | v2_struct_0(B_319)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_885])).

tff(c_934,plain,(
    ! [B_319,E_322,F_318] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_319,'#skF_3','#skF_4',E_322,F_318),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_319))))
      | ~ m1_subset_1(F_318,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_319))))
      | ~ v1_funct_2(F_318,u1_struct_0('#skF_4'),u1_struct_0(B_319))
      | ~ v1_funct_1(F_318)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_319))))
      | ~ v1_funct_2(E_322,u1_struct_0('#skF_3'),u1_struct_0(B_319))
      | ~ v1_funct_1(E_322)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_319)
      | ~ v2_pre_topc(B_319)
      | v2_struct_0(B_319)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_74,c_914])).

tff(c_936,plain,(
    ! [B_323,E_324,F_325] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_323,'#skF_3','#skF_4',E_324,F_325),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_323))))
      | ~ m1_subset_1(F_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_323))))
      | ~ v1_funct_2(F_325,u1_struct_0('#skF_4'),u1_struct_0(B_323))
      | ~ v1_funct_1(F_325)
      | ~ m1_subset_1(E_324,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_323))))
      | ~ v1_funct_2(E_324,u1_struct_0('#skF_3'),u1_struct_0(B_323))
      | ~ v1_funct_1(E_324)
      | ~ l1_pre_topc(B_323)
      | ~ v2_pre_topc(B_323)
      | v2_struct_0(B_323) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_78,c_934])).

tff(c_200,plain,(
    ! [C_159,A_160,F_157,D_156,B_158,E_161] :
      ( v1_funct_1(k10_tmap_1(A_160,B_158,C_159,D_156,E_161,F_157))
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_156),u1_struct_0(B_158))))
      | ~ v1_funct_2(F_157,u1_struct_0(D_156),u1_struct_0(B_158))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_159),u1_struct_0(B_158))))
      | ~ v1_funct_2(E_161,u1_struct_0(C_159),u1_struct_0(B_158))
      | ~ v1_funct_1(E_161)
      | ~ m1_pre_topc(D_156,A_160)
      | v2_struct_0(D_156)
      | ~ m1_pre_topc(C_159,A_160)
      | v2_struct_0(C_159)
      | ~ l1_pre_topc(B_158)
      | ~ v2_pre_topc(B_158)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_204,plain,(
    ! [A_160,C_159,E_161] :
      ( v1_funct_1(k10_tmap_1(A_160,'#skF_2',C_159,'#skF_4',E_161,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_159),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_161,u1_struct_0(C_159),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_161)
      | ~ m1_pre_topc('#skF_4',A_160)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_159,A_160)
      | v2_struct_0(C_159)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_58,c_200])).

tff(c_210,plain,(
    ! [A_160,C_159,E_161] :
      ( v1_funct_1(k10_tmap_1(A_160,'#skF_2',C_159,'#skF_4',E_161,'#skF_6'))
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_159),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_161,u1_struct_0(C_159),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_161)
      | ~ m1_pre_topc('#skF_4',A_160)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_159,A_160)
      | v2_struct_0(C_159)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_64,c_62,c_204])).

tff(c_216,plain,(
    ! [A_162,C_163,E_164] :
      ( v1_funct_1(k10_tmap_1(A_162,'#skF_2',C_163,'#skF_4',E_164,'#skF_6'))
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_163),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_164,u1_struct_0(C_163),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_164)
      | ~ m1_pre_topc('#skF_4',A_162)
      | ~ m1_pre_topc(C_163,A_162)
      | v2_struct_0(C_163)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_78,c_210])).

tff(c_223,plain,(
    ! [A_162] :
      ( v1_funct_1(k10_tmap_1(A_162,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_162)
      | ~ m1_pre_topc('#skF_3',A_162)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(resolution,[status(thm)],[c_66,c_216])).

tff(c_234,plain,(
    ! [A_162] :
      ( v1_funct_1(k10_tmap_1(A_162,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_162)
      | ~ m1_pre_topc('#skF_3',A_162)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_223])).

tff(c_247,plain,(
    ! [A_171] :
      ( v1_funct_1(k10_tmap_1(A_171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_171)
      | ~ m1_pre_topc('#skF_3',A_171)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_234])).

tff(c_50,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_128,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_250,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_247,c_128])).

tff(c_253,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_74,c_250])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_253])).

tff(c_256,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_289,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_971,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_936,c_289])).

tff(c_1003,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_72,c_70,c_66,c_64,c_62,c_58,c_971])).

tff(c_1005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1003])).

tff(c_1006,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_1013,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1006])).

tff(c_1260,plain,(
    ! [B_415,C_416,D_413,F_414,E_418,A_417] :
      ( v1_funct_2(k10_tmap_1(A_417,B_415,C_416,D_413,E_418,F_414),u1_struct_0(k1_tsep_1(A_417,C_416,D_413)),u1_struct_0(B_415))
      | ~ m1_subset_1(F_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_413),u1_struct_0(B_415))))
      | ~ v1_funct_2(F_414,u1_struct_0(D_413),u1_struct_0(B_415))
      | ~ v1_funct_1(F_414)
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_416),u1_struct_0(B_415))))
      | ~ v1_funct_2(E_418,u1_struct_0(C_416),u1_struct_0(B_415))
      | ~ v1_funct_1(E_418)
      | ~ m1_pre_topc(D_413,A_417)
      | v2_struct_0(D_413)
      | ~ m1_pre_topc(C_416,A_417)
      | v2_struct_0(C_416)
      | ~ l1_pre_topc(B_415)
      | ~ v2_pre_topc(B_415)
      | v2_struct_0(B_415)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1263,plain,(
    ! [B_415,E_418,F_414] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_415,'#skF_3','#skF_4',E_418,F_414),u1_struct_0('#skF_1'),u1_struct_0(B_415))
      | ~ m1_subset_1(F_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_415))))
      | ~ v1_funct_2(F_414,u1_struct_0('#skF_4'),u1_struct_0(B_415))
      | ~ v1_funct_1(F_414)
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_415))))
      | ~ v1_funct_2(E_418,u1_struct_0('#skF_3'),u1_struct_0(B_415))
      | ~ v1_funct_1(E_418)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_415)
      | ~ v2_pre_topc(B_415)
      | v2_struct_0(B_415)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1260])).

tff(c_1265,plain,(
    ! [B_415,E_418,F_414] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_415,'#skF_3','#skF_4',E_418,F_414),u1_struct_0('#skF_1'),u1_struct_0(B_415))
      | ~ m1_subset_1(F_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_415))))
      | ~ v1_funct_2(F_414,u1_struct_0('#skF_4'),u1_struct_0(B_415))
      | ~ v1_funct_1(F_414)
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_415))))
      | ~ v1_funct_2(E_418,u1_struct_0('#skF_3'),u1_struct_0(B_415))
      | ~ v1_funct_1(E_418)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_415)
      | ~ v2_pre_topc(B_415)
      | v2_struct_0(B_415)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_74,c_1263])).

tff(c_1278,plain,(
    ! [B_421,E_422,F_423] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_421,'#skF_3','#skF_4',E_422,F_423),u1_struct_0('#skF_1'),u1_struct_0(B_421))
      | ~ m1_subset_1(F_423,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_421))))
      | ~ v1_funct_2(F_423,u1_struct_0('#skF_4'),u1_struct_0(B_421))
      | ~ v1_funct_1(F_423)
      | ~ m1_subset_1(E_422,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_421))))
      | ~ v1_funct_2(E_422,u1_struct_0('#skF_3'),u1_struct_0(B_421))
      | ~ v1_funct_1(E_422)
      | ~ l1_pre_topc(B_421)
      | ~ v2_pre_topc(B_421)
      | v2_struct_0(B_421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_78,c_1265])).

tff(c_1283,plain,(
    ! [E_422] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_422,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_422,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_422,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_422)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_1278])).

tff(c_1287,plain,(
    ! [E_422] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_422,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_422,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_422,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_422)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_64,c_62,c_1283])).

tff(c_1289,plain,(
    ! [E_424] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_424,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_424,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_424) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1287])).

tff(c_1296,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1289])).

tff(c_1303,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1296])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1013,c_1303])).

tff(c_1306,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1006])).

tff(c_257,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1307,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1006])).

tff(c_1007,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_258,plain,(
    ! [A_172,B_173,C_174] :
      ( m1_pre_topc(k1_tsep_1(A_172,B_173,C_174),A_172)
      | ~ m1_pre_topc(C_174,A_172)
      | v2_struct_0(C_174)
      | ~ m1_pre_topc(B_173,A_172)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_261,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_258])).

tff(c_263,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_80,c_74,c_261])).

tff(c_264,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_78,c_263])).

tff(c_1337,plain,(
    ! [A_438,C_436,D_435,E_434,B_437] :
      ( v1_funct_2(k3_tmap_1(A_438,B_437,C_436,D_435,E_434),u1_struct_0(D_435),u1_struct_0(B_437))
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_436),u1_struct_0(B_437))))
      | ~ v1_funct_2(E_434,u1_struct_0(C_436),u1_struct_0(B_437))
      | ~ v1_funct_1(E_434)
      | ~ m1_pre_topc(D_435,A_438)
      | ~ m1_pre_topc(C_436,A_438)
      | ~ l1_pre_topc(B_437)
      | ~ v2_pre_topc(B_437)
      | v2_struct_0(B_437)
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1339,plain,(
    ! [A_438,D_435] :
      ( v1_funct_2(k3_tmap_1(A_438,'#skF_2','#skF_1',D_435,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_435),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_435,A_438)
      | ~ m1_pre_topc('#skF_1',A_438)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(resolution,[status(thm)],[c_1007,c_1337])).

tff(c_1346,plain,(
    ! [A_438,D_435] :
      ( v1_funct_2(k3_tmap_1(A_438,'#skF_2','#skF_1',D_435,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_435),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_435,A_438)
      | ~ m1_pre_topc('#skF_1',A_438)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_257,c_1307,c_1339])).

tff(c_1347,plain,(
    ! [A_438,D_435] :
      ( v1_funct_2(k3_tmap_1(A_438,'#skF_2','#skF_1',D_435,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_435),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_435,A_438)
      | ~ m1_pre_topc('#skF_1',A_438)
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1346])).

tff(c_18,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] :
      ( m1_subset_1(k3_tmap_1(A_14,B_15,C_16,D_17,E_18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_17),u1_struct_0(B_15))))
      | ~ m1_subset_1(E_18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_16),u1_struct_0(B_15))))
      | ~ v1_funct_2(E_18,u1_struct_0(C_16),u1_struct_0(B_15))
      | ~ v1_funct_1(E_18)
      | ~ m1_pre_topc(D_17,A_14)
      | ~ m1_pre_topc(C_16,A_14)
      | ~ l1_pre_topc(B_15)
      | ~ v2_pre_topc(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1316,plain,(
    ! [C_427,D_426,E_425,B_428,A_429] :
      ( v1_funct_1(k3_tmap_1(A_429,B_428,C_427,D_426,E_425))
      | ~ m1_subset_1(E_425,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_427),u1_struct_0(B_428))))
      | ~ v1_funct_2(E_425,u1_struct_0(C_427),u1_struct_0(B_428))
      | ~ v1_funct_1(E_425)
      | ~ m1_pre_topc(D_426,A_429)
      | ~ m1_pre_topc(C_427,A_429)
      | ~ l1_pre_topc(B_428)
      | ~ v2_pre_topc(B_428)
      | v2_struct_0(B_428)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1318,plain,(
    ! [A_429,D_426] :
      ( v1_funct_1(k3_tmap_1(A_429,'#skF_2','#skF_1',D_426,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_426,A_429)
      | ~ m1_pre_topc('#skF_1',A_429)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(resolution,[status(thm)],[c_1007,c_1316])).

tff(c_1325,plain,(
    ! [A_429,D_426] :
      ( v1_funct_1(k3_tmap_1(A_429,'#skF_2','#skF_1',D_426,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_426,A_429)
      | ~ m1_pre_topc('#skF_1',A_429)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_257,c_1307,c_1318])).

tff(c_1326,plain,(
    ! [A_429,D_426] :
      ( v1_funct_1(k3_tmap_1(A_429,'#skF_2','#skF_1',D_426,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_426,A_429)
      | ~ m1_pre_topc('#skF_1',A_429)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1325])).

tff(c_54,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_97,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54])).

tff(c_266,plain,(
    ! [D_178,C_179,A_180,B_181] :
      ( D_178 = C_179
      | ~ r2_funct_2(A_180,B_181,C_179,D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_2(D_178,A_180,B_181)
      | ~ v1_funct_1(D_178)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_2(C_179,A_180,B_181)
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_270,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_97,c_266])).

tff(c_280,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_270])).

tff(c_1683,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_1686,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1326,c_1683])).

tff(c_1689,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_264,c_80,c_1686])).

tff(c_1691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1689])).

tff(c_1692,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_1694,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1692])).

tff(c_1707,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1694])).

tff(c_1710,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_264,c_80,c_257,c_1307,c_1007,c_1707])).

tff(c_1712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_1710])).

tff(c_1713,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1692])).

tff(c_1756,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1713])).

tff(c_1760,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1347,c_1756])).

tff(c_1763,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_264,c_80,c_1760])).

tff(c_1765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1763])).

tff(c_1766,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1713])).

tff(c_68,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_52,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_98,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52])).

tff(c_268,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_98,c_266])).

tff(c_277,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_268])).

tff(c_1536,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_1539,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1326,c_1536])).

tff(c_1542,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_264,c_74,c_1539])).

tff(c_1544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1542])).

tff(c_1545,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_1547,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1545])).

tff(c_1560,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1547])).

tff(c_1563,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_264,c_74,c_257,c_1307,c_1007,c_1560])).

tff(c_1565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_1563])).

tff(c_1566,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1545])).

tff(c_1609,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1566])).

tff(c_1613,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1347,c_1609])).

tff(c_1616,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_264,c_74,c_1613])).

tff(c_1618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1616])).

tff(c_1619,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1566])).

tff(c_60,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_82,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_76,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_48,plain,(
    ! [A_50,B_54,C_56] :
      ( r4_tsep_1(A_50,B_54,C_56)
      | ~ m1_pre_topc(C_56,A_50)
      | ~ v1_tsep_1(C_56,A_50)
      | ~ m1_pre_topc(B_54,A_50)
      | ~ v1_tsep_1(B_54,A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_1420,plain,(
    ! [D_464,A_465,C_463,B_466,E_467] :
      ( v1_funct_1(k3_tmap_1(A_465,B_466,k1_tsep_1(A_465,C_463,D_464),C_463,E_467))
      | ~ v5_pre_topc(E_467,k1_tsep_1(A_465,C_463,D_464),B_466)
      | ~ m1_subset_1(E_467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_465,C_463,D_464)),u1_struct_0(B_466))))
      | ~ v1_funct_2(E_467,u1_struct_0(k1_tsep_1(A_465,C_463,D_464)),u1_struct_0(B_466))
      | ~ v1_funct_1(E_467)
      | ~ r4_tsep_1(A_465,C_463,D_464)
      | ~ m1_pre_topc(D_464,A_465)
      | v2_struct_0(D_464)
      | ~ m1_pre_topc(C_463,A_465)
      | v2_struct_0(C_463)
      | ~ l1_pre_topc(B_466)
      | ~ v2_pre_topc(B_466)
      | v2_struct_0(B_466)
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1425,plain,(
    ! [B_466,E_467] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_466,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_467))
      | ~ v5_pre_topc(E_467,k1_tsep_1('#skF_1','#skF_3','#skF_4'),B_466)
      | ~ m1_subset_1(E_467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_466))))
      | ~ v1_funct_2(E_467,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_466))
      | ~ v1_funct_1(E_467)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_466)
      | ~ v2_pre_topc(B_466)
      | v2_struct_0(B_466)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1420])).

tff(c_1428,plain,(
    ! [B_466,E_467] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_466,'#skF_1','#skF_3',E_467))
      | ~ v5_pre_topc(E_467,'#skF_1',B_466)
      | ~ m1_subset_1(E_467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_466))))
      | ~ v1_funct_2(E_467,u1_struct_0('#skF_1'),u1_struct_0(B_466))
      | ~ v1_funct_1(E_467)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_466)
      | ~ v2_pre_topc(B_466)
      | v2_struct_0(B_466)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_74,c_56,c_56,c_56,c_1425])).

tff(c_1429,plain,(
    ! [B_466,E_467] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_466,'#skF_1','#skF_3',E_467))
      | ~ v5_pre_topc(E_467,'#skF_1',B_466)
      | ~ m1_subset_1(E_467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_466))))
      | ~ v1_funct_2(E_467,u1_struct_0('#skF_1'),u1_struct_0(B_466))
      | ~ v1_funct_1(E_467)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ l1_pre_topc(B_466)
      | ~ v2_pre_topc(B_466)
      | v2_struct_0(B_466) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_78,c_1428])).

tff(c_1431,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1429])).

tff(c_1434,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1431])).

tff(c_1437,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_80,c_76,c_74,c_1434])).

tff(c_1439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1437])).

tff(c_1441,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1429])).

tff(c_2725,plain,(
    ! [B_619,D_617,A_618,E_620,C_616] :
      ( v5_pre_topc(E_620,k1_tsep_1(A_618,C_616,D_617),B_619)
      | ~ m1_subset_1(k3_tmap_1(A_618,B_619,k1_tsep_1(A_618,C_616,D_617),D_617,E_620),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_617),u1_struct_0(B_619))))
      | ~ v5_pre_topc(k3_tmap_1(A_618,B_619,k1_tsep_1(A_618,C_616,D_617),D_617,E_620),D_617,B_619)
      | ~ v1_funct_2(k3_tmap_1(A_618,B_619,k1_tsep_1(A_618,C_616,D_617),D_617,E_620),u1_struct_0(D_617),u1_struct_0(B_619))
      | ~ v1_funct_1(k3_tmap_1(A_618,B_619,k1_tsep_1(A_618,C_616,D_617),D_617,E_620))
      | ~ m1_subset_1(k3_tmap_1(A_618,B_619,k1_tsep_1(A_618,C_616,D_617),C_616,E_620),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_616),u1_struct_0(B_619))))
      | ~ v5_pre_topc(k3_tmap_1(A_618,B_619,k1_tsep_1(A_618,C_616,D_617),C_616,E_620),C_616,B_619)
      | ~ v1_funct_2(k3_tmap_1(A_618,B_619,k1_tsep_1(A_618,C_616,D_617),C_616,E_620),u1_struct_0(C_616),u1_struct_0(B_619))
      | ~ v1_funct_1(k3_tmap_1(A_618,B_619,k1_tsep_1(A_618,C_616,D_617),C_616,E_620))
      | ~ m1_subset_1(E_620,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_618,C_616,D_617)),u1_struct_0(B_619))))
      | ~ v1_funct_2(E_620,u1_struct_0(k1_tsep_1(A_618,C_616,D_617)),u1_struct_0(B_619))
      | ~ v1_funct_1(E_620)
      | ~ r4_tsep_1(A_618,C_616,D_617)
      | ~ m1_pre_topc(D_617,A_618)
      | v2_struct_0(D_617)
      | ~ m1_pre_topc(C_616,A_618)
      | v2_struct_0(C_616)
      | ~ l1_pre_topc(B_619)
      | ~ v2_pre_topc(B_619)
      | v2_struct_0(B_619)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2735,plain,(
    ! [E_620,B_619] :
      ( v5_pre_topc(E_620,k1_tsep_1('#skF_1','#skF_3','#skF_4'),B_619)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_4',E_620),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_619))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_619,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_620),'#skF_4',B_619)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_619,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_620),u1_struct_0('#skF_4'),u1_struct_0(B_619))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_619,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_620))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_619,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_620),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_619))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_619,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_620),'#skF_3',B_619)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_619,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_620),u1_struct_0('#skF_3'),u1_struct_0(B_619))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_619,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_620))
      | ~ m1_subset_1(E_620,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_619))))
      | ~ v1_funct_2(E_620,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_619))
      | ~ v1_funct_1(E_620)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_619)
      | ~ v2_pre_topc(B_619)
      | v2_struct_0(B_619)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2725])).

tff(c_2740,plain,(
    ! [E_620,B_619] :
      ( v5_pre_topc(E_620,'#skF_1',B_619)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_4',E_620),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_619))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_4',E_620),'#skF_4',B_619)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_4',E_620),u1_struct_0('#skF_4'),u1_struct_0(B_619))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_4',E_620))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_3',E_620),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_619))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_3',E_620),'#skF_3',B_619)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_3',E_620),u1_struct_0('#skF_3'),u1_struct_0(B_619))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_619,'#skF_1','#skF_3',E_620))
      | ~ m1_subset_1(E_620,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_619))))
      | ~ v1_funct_2(E_620,u1_struct_0('#skF_1'),u1_struct_0(B_619))
      | ~ v1_funct_1(E_620)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_619)
      | ~ v2_pre_topc(B_619)
      | v2_struct_0(B_619)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80,c_74,c_1441,c_56,c_56,c_56,c_56,c_56,c_56,c_56,c_56,c_56,c_56,c_2735])).

tff(c_4197,plain,(
    ! [E_857,B_858] :
      ( v5_pre_topc(E_857,'#skF_1',B_858)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_858,'#skF_1','#skF_4',E_857),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_858))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_858,'#skF_1','#skF_4',E_857),'#skF_4',B_858)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_858,'#skF_1','#skF_4',E_857),u1_struct_0('#skF_4'),u1_struct_0(B_858))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_858,'#skF_1','#skF_4',E_857))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_858,'#skF_1','#skF_3',E_857),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_858))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_858,'#skF_1','#skF_3',E_857),'#skF_3',B_858)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_858,'#skF_1','#skF_3',E_857),u1_struct_0('#skF_3'),u1_struct_0(B_858))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_858,'#skF_1','#skF_3',E_857))
      | ~ m1_subset_1(E_857,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_858))))
      | ~ v1_funct_2(E_857,u1_struct_0('#skF_1'),u1_struct_0(B_858))
      | ~ v1_funct_1(E_857)
      | ~ l1_pre_topc(B_858)
      | ~ v2_pre_topc(B_858)
      | v2_struct_0(B_858) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_78,c_2740])).

tff(c_4203,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_4197])).

tff(c_4210,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_257,c_1307,c_1007,c_72,c_1766,c_70,c_1766,c_68,c_1766,c_66,c_64,c_1619,c_62,c_1619,c_60,c_1619,c_58,c_1619,c_4203])).

tff(c_4212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1306,c_4210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:32:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.78/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/3.07  
% 8.78/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.78/3.08  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.78/3.08  
% 8.78/3.08  %Foreground sorts:
% 8.78/3.08  
% 8.78/3.08  
% 8.78/3.08  %Background operators:
% 8.78/3.08  
% 8.78/3.08  
% 8.78/3.08  %Foreground operators:
% 8.78/3.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.78/3.08  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.78/3.08  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.78/3.08  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.78/3.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.78/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.78/3.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.78/3.08  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 8.78/3.08  tff('#skF_5', type, '#skF_5': $i).
% 8.78/3.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.78/3.08  tff('#skF_6', type, '#skF_6': $i).
% 8.78/3.08  tff('#skF_2', type, '#skF_2': $i).
% 8.78/3.08  tff('#skF_3', type, '#skF_3': $i).
% 8.78/3.08  tff('#skF_1', type, '#skF_1': $i).
% 8.78/3.08  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.78/3.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.78/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.78/3.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.78/3.08  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 8.78/3.08  tff('#skF_4', type, '#skF_4': $i).
% 8.78/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.78/3.08  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.78/3.08  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.78/3.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.78/3.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.78/3.08  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.78/3.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.78/3.08  
% 9.01/3.11  tff(f_278, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_tsep_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, A)) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((A = k1_tsep_1(A, C, D)) & r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E)) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_tmap_1)).
% 9.01/3.11  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 9.01/3.11  tff(f_105, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 9.01/3.11  tff(f_135, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 9.01/3.11  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 9.01/3.11  tff(f_214, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((v1_tsep_1(C, A) & m1_pre_topc(C, A)) => r4_tsep_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tsep_1)).
% 9.01/3.11  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 9.01/3.11  tff(c_90, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_88, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_86, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_70, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_62, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_96, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_84, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_78, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_94, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_92, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_80, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_74, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_56, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_885, plain, (![C_320, D_317, A_321, E_322, B_319, F_318]: (m1_subset_1(k10_tmap_1(A_321, B_319, C_320, D_317, E_322, F_318), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_321, C_320, D_317)), u1_struct_0(B_319)))) | ~m1_subset_1(F_318, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_317), u1_struct_0(B_319)))) | ~v1_funct_2(F_318, u1_struct_0(D_317), u1_struct_0(B_319)) | ~v1_funct_1(F_318) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_320), u1_struct_0(B_319)))) | ~v1_funct_2(E_322, u1_struct_0(C_320), u1_struct_0(B_319)) | ~v1_funct_1(E_322) | ~m1_pre_topc(D_317, A_321) | v2_struct_0(D_317) | ~m1_pre_topc(C_320, A_321) | v2_struct_0(C_320) | ~l1_pre_topc(B_319) | ~v2_pre_topc(B_319) | v2_struct_0(B_319) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.01/3.11  tff(c_914, plain, (![B_319, E_322, F_318]: (m1_subset_1(k10_tmap_1('#skF_1', B_319, '#skF_3', '#skF_4', E_322, F_318), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_319)))) | ~m1_subset_1(F_318, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_319)))) | ~v1_funct_2(F_318, u1_struct_0('#skF_4'), u1_struct_0(B_319)) | ~v1_funct_1(F_318) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_319)))) | ~v1_funct_2(E_322, u1_struct_0('#skF_3'), u1_struct_0(B_319)) | ~v1_funct_1(E_322) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_319) | ~v2_pre_topc(B_319) | v2_struct_0(B_319) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_885])).
% 9.01/3.11  tff(c_934, plain, (![B_319, E_322, F_318]: (m1_subset_1(k10_tmap_1('#skF_1', B_319, '#skF_3', '#skF_4', E_322, F_318), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_319)))) | ~m1_subset_1(F_318, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_319)))) | ~v1_funct_2(F_318, u1_struct_0('#skF_4'), u1_struct_0(B_319)) | ~v1_funct_1(F_318) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_319)))) | ~v1_funct_2(E_322, u1_struct_0('#skF_3'), u1_struct_0(B_319)) | ~v1_funct_1(E_322) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_319) | ~v2_pre_topc(B_319) | v2_struct_0(B_319) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_74, c_914])).
% 9.01/3.11  tff(c_936, plain, (![B_323, E_324, F_325]: (m1_subset_1(k10_tmap_1('#skF_1', B_323, '#skF_3', '#skF_4', E_324, F_325), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_323)))) | ~m1_subset_1(F_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_323)))) | ~v1_funct_2(F_325, u1_struct_0('#skF_4'), u1_struct_0(B_323)) | ~v1_funct_1(F_325) | ~m1_subset_1(E_324, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_323)))) | ~v1_funct_2(E_324, u1_struct_0('#skF_3'), u1_struct_0(B_323)) | ~v1_funct_1(E_324) | ~l1_pre_topc(B_323) | ~v2_pre_topc(B_323) | v2_struct_0(B_323))), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_78, c_934])).
% 9.01/3.11  tff(c_200, plain, (![C_159, A_160, F_157, D_156, B_158, E_161]: (v1_funct_1(k10_tmap_1(A_160, B_158, C_159, D_156, E_161, F_157)) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_156), u1_struct_0(B_158)))) | ~v1_funct_2(F_157, u1_struct_0(D_156), u1_struct_0(B_158)) | ~v1_funct_1(F_157) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_159), u1_struct_0(B_158)))) | ~v1_funct_2(E_161, u1_struct_0(C_159), u1_struct_0(B_158)) | ~v1_funct_1(E_161) | ~m1_pre_topc(D_156, A_160) | v2_struct_0(D_156) | ~m1_pre_topc(C_159, A_160) | v2_struct_0(C_159) | ~l1_pre_topc(B_158) | ~v2_pre_topc(B_158) | v2_struct_0(B_158) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.01/3.11  tff(c_204, plain, (![A_160, C_159, E_161]: (v1_funct_1(k10_tmap_1(A_160, '#skF_2', C_159, '#skF_4', E_161, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_159), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_161, u1_struct_0(C_159), u1_struct_0('#skF_2')) | ~v1_funct_1(E_161) | ~m1_pre_topc('#skF_4', A_160) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_159, A_160) | v2_struct_0(C_159) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_58, c_200])).
% 9.01/3.11  tff(c_210, plain, (![A_160, C_159, E_161]: (v1_funct_1(k10_tmap_1(A_160, '#skF_2', C_159, '#skF_4', E_161, '#skF_6')) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_159), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_161, u1_struct_0(C_159), u1_struct_0('#skF_2')) | ~v1_funct_1(E_161) | ~m1_pre_topc('#skF_4', A_160) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_159, A_160) | v2_struct_0(C_159) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_64, c_62, c_204])).
% 9.01/3.11  tff(c_216, plain, (![A_162, C_163, E_164]: (v1_funct_1(k10_tmap_1(A_162, '#skF_2', C_163, '#skF_4', E_164, '#skF_6')) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_163), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_164, u1_struct_0(C_163), u1_struct_0('#skF_2')) | ~v1_funct_1(E_164) | ~m1_pre_topc('#skF_4', A_162) | ~m1_pre_topc(C_163, A_162) | v2_struct_0(C_163) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(negUnitSimplification, [status(thm)], [c_90, c_78, c_210])).
% 9.01/3.11  tff(c_223, plain, (![A_162]: (v1_funct_1(k10_tmap_1(A_162, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_162) | ~m1_pre_topc('#skF_3', A_162) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(resolution, [status(thm)], [c_66, c_216])).
% 9.01/3.11  tff(c_234, plain, (![A_162]: (v1_funct_1(k10_tmap_1(A_162, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_162) | ~m1_pre_topc('#skF_3', A_162) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_223])).
% 9.01/3.11  tff(c_247, plain, (![A_171]: (v1_funct_1(k10_tmap_1(A_171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_171) | ~m1_pre_topc('#skF_3', A_171) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(negUnitSimplification, [status(thm)], [c_84, c_234])).
% 9.01/3.11  tff(c_50, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_128, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_50])).
% 9.01/3.11  tff(c_250, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_247, c_128])).
% 9.01/3.11  tff(c_253, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_74, c_250])).
% 9.01/3.11  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_253])).
% 9.01/3.11  tff(c_256, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_50])).
% 9.01/3.11  tff(c_289, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_256])).
% 9.01/3.11  tff(c_971, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_936, c_289])).
% 9.01/3.11  tff(c_1003, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_72, c_70, c_66, c_64, c_62, c_58, c_971])).
% 9.01/3.11  tff(c_1005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1003])).
% 9.01/3.11  tff(c_1006, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_256])).
% 9.01/3.11  tff(c_1013, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1006])).
% 9.01/3.11  tff(c_1260, plain, (![B_415, C_416, D_413, F_414, E_418, A_417]: (v1_funct_2(k10_tmap_1(A_417, B_415, C_416, D_413, E_418, F_414), u1_struct_0(k1_tsep_1(A_417, C_416, D_413)), u1_struct_0(B_415)) | ~m1_subset_1(F_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_413), u1_struct_0(B_415)))) | ~v1_funct_2(F_414, u1_struct_0(D_413), u1_struct_0(B_415)) | ~v1_funct_1(F_414) | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_416), u1_struct_0(B_415)))) | ~v1_funct_2(E_418, u1_struct_0(C_416), u1_struct_0(B_415)) | ~v1_funct_1(E_418) | ~m1_pre_topc(D_413, A_417) | v2_struct_0(D_413) | ~m1_pre_topc(C_416, A_417) | v2_struct_0(C_416) | ~l1_pre_topc(B_415) | ~v2_pre_topc(B_415) | v2_struct_0(B_415) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.01/3.11  tff(c_1263, plain, (![B_415, E_418, F_414]: (v1_funct_2(k10_tmap_1('#skF_1', B_415, '#skF_3', '#skF_4', E_418, F_414), u1_struct_0('#skF_1'), u1_struct_0(B_415)) | ~m1_subset_1(F_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_415)))) | ~v1_funct_2(F_414, u1_struct_0('#skF_4'), u1_struct_0(B_415)) | ~v1_funct_1(F_414) | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_415)))) | ~v1_funct_2(E_418, u1_struct_0('#skF_3'), u1_struct_0(B_415)) | ~v1_funct_1(E_418) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_415) | ~v2_pre_topc(B_415) | v2_struct_0(B_415) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1260])).
% 9.01/3.11  tff(c_1265, plain, (![B_415, E_418, F_414]: (v1_funct_2(k10_tmap_1('#skF_1', B_415, '#skF_3', '#skF_4', E_418, F_414), u1_struct_0('#skF_1'), u1_struct_0(B_415)) | ~m1_subset_1(F_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_415)))) | ~v1_funct_2(F_414, u1_struct_0('#skF_4'), u1_struct_0(B_415)) | ~v1_funct_1(F_414) | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_415)))) | ~v1_funct_2(E_418, u1_struct_0('#skF_3'), u1_struct_0(B_415)) | ~v1_funct_1(E_418) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_415) | ~v2_pre_topc(B_415) | v2_struct_0(B_415) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_74, c_1263])).
% 9.01/3.11  tff(c_1278, plain, (![B_421, E_422, F_423]: (v1_funct_2(k10_tmap_1('#skF_1', B_421, '#skF_3', '#skF_4', E_422, F_423), u1_struct_0('#skF_1'), u1_struct_0(B_421)) | ~m1_subset_1(F_423, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_421)))) | ~v1_funct_2(F_423, u1_struct_0('#skF_4'), u1_struct_0(B_421)) | ~v1_funct_1(F_423) | ~m1_subset_1(E_422, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_421)))) | ~v1_funct_2(E_422, u1_struct_0('#skF_3'), u1_struct_0(B_421)) | ~v1_funct_1(E_422) | ~l1_pre_topc(B_421) | ~v2_pre_topc(B_421) | v2_struct_0(B_421))), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_78, c_1265])).
% 9.01/3.11  tff(c_1283, plain, (![E_422]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_422, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_422, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_422, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_422) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_1278])).
% 9.01/3.11  tff(c_1287, plain, (![E_422]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_422, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_422, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_422, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_422) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_64, c_62, c_1283])).
% 9.01/3.11  tff(c_1289, plain, (![E_424]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_424, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_424, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_424))), inference(negUnitSimplification, [status(thm)], [c_90, c_1287])).
% 9.01/3.11  tff(c_1296, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1289])).
% 9.01/3.11  tff(c_1303, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1296])).
% 9.01/3.11  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1013, c_1303])).
% 9.01/3.11  tff(c_1306, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1006])).
% 9.01/3.11  tff(c_257, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_50])).
% 9.01/3.11  tff(c_1307, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1006])).
% 9.01/3.11  tff(c_1007, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_256])).
% 9.01/3.11  tff(c_258, plain, (![A_172, B_173, C_174]: (m1_pre_topc(k1_tsep_1(A_172, B_173, C_174), A_172) | ~m1_pre_topc(C_174, A_172) | v2_struct_0(C_174) | ~m1_pre_topc(B_173, A_172) | v2_struct_0(B_173) | ~l1_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.01/3.11  tff(c_261, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_258])).
% 9.01/3.11  tff(c_263, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_80, c_74, c_261])).
% 9.01/3.11  tff(c_264, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_78, c_263])).
% 9.01/3.11  tff(c_1337, plain, (![A_438, C_436, D_435, E_434, B_437]: (v1_funct_2(k3_tmap_1(A_438, B_437, C_436, D_435, E_434), u1_struct_0(D_435), u1_struct_0(B_437)) | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_436), u1_struct_0(B_437)))) | ~v1_funct_2(E_434, u1_struct_0(C_436), u1_struct_0(B_437)) | ~v1_funct_1(E_434) | ~m1_pre_topc(D_435, A_438) | ~m1_pre_topc(C_436, A_438) | ~l1_pre_topc(B_437) | ~v2_pre_topc(B_437) | v2_struct_0(B_437) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.01/3.11  tff(c_1339, plain, (![A_438, D_435]: (v1_funct_2(k3_tmap_1(A_438, '#skF_2', '#skF_1', D_435, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_435), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_435, A_438) | ~m1_pre_topc('#skF_1', A_438) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(resolution, [status(thm)], [c_1007, c_1337])).
% 9.01/3.11  tff(c_1346, plain, (![A_438, D_435]: (v1_funct_2(k3_tmap_1(A_438, '#skF_2', '#skF_1', D_435, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_435), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_435, A_438) | ~m1_pre_topc('#skF_1', A_438) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_257, c_1307, c_1339])).
% 9.01/3.11  tff(c_1347, plain, (![A_438, D_435]: (v1_funct_2(k3_tmap_1(A_438, '#skF_2', '#skF_1', D_435, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_435), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_435, A_438) | ~m1_pre_topc('#skF_1', A_438) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(negUnitSimplification, [status(thm)], [c_90, c_1346])).
% 9.01/3.11  tff(c_18, plain, (![E_18, C_16, D_17, A_14, B_15]: (m1_subset_1(k3_tmap_1(A_14, B_15, C_16, D_17, E_18), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_17), u1_struct_0(B_15)))) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_16), u1_struct_0(B_15)))) | ~v1_funct_2(E_18, u1_struct_0(C_16), u1_struct_0(B_15)) | ~v1_funct_1(E_18) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(C_16, A_14) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.01/3.11  tff(c_1316, plain, (![C_427, D_426, E_425, B_428, A_429]: (v1_funct_1(k3_tmap_1(A_429, B_428, C_427, D_426, E_425)) | ~m1_subset_1(E_425, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_427), u1_struct_0(B_428)))) | ~v1_funct_2(E_425, u1_struct_0(C_427), u1_struct_0(B_428)) | ~v1_funct_1(E_425) | ~m1_pre_topc(D_426, A_429) | ~m1_pre_topc(C_427, A_429) | ~l1_pre_topc(B_428) | ~v2_pre_topc(B_428) | v2_struct_0(B_428) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.01/3.11  tff(c_1318, plain, (![A_429, D_426]: (v1_funct_1(k3_tmap_1(A_429, '#skF_2', '#skF_1', D_426, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_426, A_429) | ~m1_pre_topc('#skF_1', A_429) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(resolution, [status(thm)], [c_1007, c_1316])).
% 9.01/3.11  tff(c_1325, plain, (![A_429, D_426]: (v1_funct_1(k3_tmap_1(A_429, '#skF_2', '#skF_1', D_426, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_426, A_429) | ~m1_pre_topc('#skF_1', A_429) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_257, c_1307, c_1318])).
% 9.01/3.11  tff(c_1326, plain, (![A_429, D_426]: (v1_funct_1(k3_tmap_1(A_429, '#skF_2', '#skF_1', D_426, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_426, A_429) | ~m1_pre_topc('#skF_1', A_429) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(negUnitSimplification, [status(thm)], [c_90, c_1325])).
% 9.01/3.11  tff(c_54, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_97, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54])).
% 9.01/3.11  tff(c_266, plain, (![D_178, C_179, A_180, B_181]: (D_178=C_179 | ~r2_funct_2(A_180, B_181, C_179, D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_2(D_178, A_180, B_181) | ~v1_funct_1(D_178) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_2(C_179, A_180, B_181) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.01/3.11  tff(c_270, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_97, c_266])).
% 9.01/3.11  tff(c_280, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_270])).
% 9.01/3.11  tff(c_1683, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_280])).
% 9.01/3.11  tff(c_1686, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1326, c_1683])).
% 9.01/3.11  tff(c_1689, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_264, c_80, c_1686])).
% 9.01/3.11  tff(c_1691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1689])).
% 9.01/3.11  tff(c_1692, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_280])).
% 9.01/3.11  tff(c_1694, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1692])).
% 9.01/3.11  tff(c_1707, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1694])).
% 9.01/3.11  tff(c_1710, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_264, c_80, c_257, c_1307, c_1007, c_1707])).
% 9.01/3.11  tff(c_1712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_1710])).
% 9.01/3.11  tff(c_1713, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1692])).
% 9.01/3.11  tff(c_1756, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1713])).
% 9.01/3.11  tff(c_1760, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1347, c_1756])).
% 9.01/3.11  tff(c_1763, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_264, c_80, c_1760])).
% 9.01/3.11  tff(c_1765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1763])).
% 9.01/3.11  tff(c_1766, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1713])).
% 9.01/3.11  tff(c_68, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_52, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_98, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52])).
% 9.01/3.11  tff(c_268, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_98, c_266])).
% 9.01/3.11  tff(c_277, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_268])).
% 9.01/3.11  tff(c_1536, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_277])).
% 9.01/3.11  tff(c_1539, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1326, c_1536])).
% 9.01/3.11  tff(c_1542, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_264, c_74, c_1539])).
% 9.01/3.11  tff(c_1544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1542])).
% 9.01/3.11  tff(c_1545, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_277])).
% 9.01/3.11  tff(c_1547, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1545])).
% 9.01/3.11  tff(c_1560, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1547])).
% 9.01/3.11  tff(c_1563, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_264, c_74, c_257, c_1307, c_1007, c_1560])).
% 9.01/3.11  tff(c_1565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_1563])).
% 9.01/3.11  tff(c_1566, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1545])).
% 9.01/3.11  tff(c_1609, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1566])).
% 9.01/3.11  tff(c_1613, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1347, c_1609])).
% 9.01/3.11  tff(c_1616, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_264, c_74, c_1613])).
% 9.01/3.11  tff(c_1618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1616])).
% 9.01/3.11  tff(c_1619, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1566])).
% 9.01/3.11  tff(c_60, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_82, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_76, plain, (v1_tsep_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 9.01/3.11  tff(c_48, plain, (![A_50, B_54, C_56]: (r4_tsep_1(A_50, B_54, C_56) | ~m1_pre_topc(C_56, A_50) | ~v1_tsep_1(C_56, A_50) | ~m1_pre_topc(B_54, A_50) | ~v1_tsep_1(B_54, A_50) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.01/3.11  tff(c_1420, plain, (![D_464, A_465, C_463, B_466, E_467]: (v1_funct_1(k3_tmap_1(A_465, B_466, k1_tsep_1(A_465, C_463, D_464), C_463, E_467)) | ~v5_pre_topc(E_467, k1_tsep_1(A_465, C_463, D_464), B_466) | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_465, C_463, D_464)), u1_struct_0(B_466)))) | ~v1_funct_2(E_467, u1_struct_0(k1_tsep_1(A_465, C_463, D_464)), u1_struct_0(B_466)) | ~v1_funct_1(E_467) | ~r4_tsep_1(A_465, C_463, D_464) | ~m1_pre_topc(D_464, A_465) | v2_struct_0(D_464) | ~m1_pre_topc(C_463, A_465) | v2_struct_0(C_463) | ~l1_pre_topc(B_466) | ~v2_pre_topc(B_466) | v2_struct_0(B_466) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.01/3.11  tff(c_1425, plain, (![B_466, E_467]: (v1_funct_1(k3_tmap_1('#skF_1', B_466, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_467)) | ~v5_pre_topc(E_467, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), B_466) | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_466)))) | ~v1_funct_2(E_467, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_466)) | ~v1_funct_1(E_467) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_466) | ~v2_pre_topc(B_466) | v2_struct_0(B_466) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1420])).
% 9.01/3.11  tff(c_1428, plain, (![B_466, E_467]: (v1_funct_1(k3_tmap_1('#skF_1', B_466, '#skF_1', '#skF_3', E_467)) | ~v5_pre_topc(E_467, '#skF_1', B_466) | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_466)))) | ~v1_funct_2(E_467, u1_struct_0('#skF_1'), u1_struct_0(B_466)) | ~v1_funct_1(E_467) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_466) | ~v2_pre_topc(B_466) | v2_struct_0(B_466) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_74, c_56, c_56, c_56, c_1425])).
% 9.01/3.11  tff(c_1429, plain, (![B_466, E_467]: (v1_funct_1(k3_tmap_1('#skF_1', B_466, '#skF_1', '#skF_3', E_467)) | ~v5_pre_topc(E_467, '#skF_1', B_466) | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_466)))) | ~v1_funct_2(E_467, u1_struct_0('#skF_1'), u1_struct_0(B_466)) | ~v1_funct_1(E_467) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~l1_pre_topc(B_466) | ~v2_pre_topc(B_466) | v2_struct_0(B_466))), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_78, c_1428])).
% 9.01/3.11  tff(c_1431, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1429])).
% 9.01/3.11  tff(c_1434, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1431])).
% 9.01/3.11  tff(c_1437, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_80, c_76, c_74, c_1434])).
% 9.01/3.11  tff(c_1439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1437])).
% 9.01/3.11  tff(c_1441, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1429])).
% 9.01/3.11  tff(c_2725, plain, (![B_619, D_617, A_618, E_620, C_616]: (v5_pre_topc(E_620, k1_tsep_1(A_618, C_616, D_617), B_619) | ~m1_subset_1(k3_tmap_1(A_618, B_619, k1_tsep_1(A_618, C_616, D_617), D_617, E_620), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_617), u1_struct_0(B_619)))) | ~v5_pre_topc(k3_tmap_1(A_618, B_619, k1_tsep_1(A_618, C_616, D_617), D_617, E_620), D_617, B_619) | ~v1_funct_2(k3_tmap_1(A_618, B_619, k1_tsep_1(A_618, C_616, D_617), D_617, E_620), u1_struct_0(D_617), u1_struct_0(B_619)) | ~v1_funct_1(k3_tmap_1(A_618, B_619, k1_tsep_1(A_618, C_616, D_617), D_617, E_620)) | ~m1_subset_1(k3_tmap_1(A_618, B_619, k1_tsep_1(A_618, C_616, D_617), C_616, E_620), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_616), u1_struct_0(B_619)))) | ~v5_pre_topc(k3_tmap_1(A_618, B_619, k1_tsep_1(A_618, C_616, D_617), C_616, E_620), C_616, B_619) | ~v1_funct_2(k3_tmap_1(A_618, B_619, k1_tsep_1(A_618, C_616, D_617), C_616, E_620), u1_struct_0(C_616), u1_struct_0(B_619)) | ~v1_funct_1(k3_tmap_1(A_618, B_619, k1_tsep_1(A_618, C_616, D_617), C_616, E_620)) | ~m1_subset_1(E_620, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_618, C_616, D_617)), u1_struct_0(B_619)))) | ~v1_funct_2(E_620, u1_struct_0(k1_tsep_1(A_618, C_616, D_617)), u1_struct_0(B_619)) | ~v1_funct_1(E_620) | ~r4_tsep_1(A_618, C_616, D_617) | ~m1_pre_topc(D_617, A_618) | v2_struct_0(D_617) | ~m1_pre_topc(C_616, A_618) | v2_struct_0(C_616) | ~l1_pre_topc(B_619) | ~v2_pre_topc(B_619) | v2_struct_0(B_619) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(cnfTransformation, [status(thm)], [f_195])).
% 9.01/3.11  tff(c_2735, plain, (![E_620, B_619]: (v5_pre_topc(E_620, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), B_619) | ~m1_subset_1(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_4', E_620), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_619)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_619, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_620), '#skF_4', B_619) | ~v1_funct_2(k3_tmap_1('#skF_1', B_619, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_620), u1_struct_0('#skF_4'), u1_struct_0(B_619)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_619, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_620)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_619, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_620), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_619)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_619, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_620), '#skF_3', B_619) | ~v1_funct_2(k3_tmap_1('#skF_1', B_619, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_620), u1_struct_0('#skF_3'), u1_struct_0(B_619)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_619, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_620)) | ~m1_subset_1(E_620, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_619)))) | ~v1_funct_2(E_620, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_619)) | ~v1_funct_1(E_620) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_619) | ~v2_pre_topc(B_619) | v2_struct_0(B_619) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2725])).
% 9.01/3.11  tff(c_2740, plain, (![E_620, B_619]: (v5_pre_topc(E_620, '#skF_1', B_619) | ~m1_subset_1(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_4', E_620), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_619)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_4', E_620), '#skF_4', B_619) | ~v1_funct_2(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_4', E_620), u1_struct_0('#skF_4'), u1_struct_0(B_619)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_4', E_620)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_3', E_620), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_619)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_3', E_620), '#skF_3', B_619) | ~v1_funct_2(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_3', E_620), u1_struct_0('#skF_3'), u1_struct_0(B_619)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_619, '#skF_1', '#skF_3', E_620)) | ~m1_subset_1(E_620, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_619)))) | ~v1_funct_2(E_620, u1_struct_0('#skF_1'), u1_struct_0(B_619)) | ~v1_funct_1(E_620) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_619) | ~v2_pre_topc(B_619) | v2_struct_0(B_619) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80, c_74, c_1441, c_56, c_56, c_56, c_56, c_56, c_56, c_56, c_56, c_56, c_56, c_2735])).
% 9.01/3.11  tff(c_4197, plain, (![E_857, B_858]: (v5_pre_topc(E_857, '#skF_1', B_858) | ~m1_subset_1(k3_tmap_1('#skF_1', B_858, '#skF_1', '#skF_4', E_857), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_858)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_858, '#skF_1', '#skF_4', E_857), '#skF_4', B_858) | ~v1_funct_2(k3_tmap_1('#skF_1', B_858, '#skF_1', '#skF_4', E_857), u1_struct_0('#skF_4'), u1_struct_0(B_858)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_858, '#skF_1', '#skF_4', E_857)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_858, '#skF_1', '#skF_3', E_857), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_858)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_858, '#skF_1', '#skF_3', E_857), '#skF_3', B_858) | ~v1_funct_2(k3_tmap_1('#skF_1', B_858, '#skF_1', '#skF_3', E_857), u1_struct_0('#skF_3'), u1_struct_0(B_858)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_858, '#skF_1', '#skF_3', E_857)) | ~m1_subset_1(E_857, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_858)))) | ~v1_funct_2(E_857, u1_struct_0('#skF_1'), u1_struct_0(B_858)) | ~v1_funct_1(E_857) | ~l1_pre_topc(B_858) | ~v2_pre_topc(B_858) | v2_struct_0(B_858))), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_78, c_2740])).
% 9.01/3.11  tff(c_4203, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1766, c_4197])).
% 9.01/3.11  tff(c_4210, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_257, c_1307, c_1007, c_72, c_1766, c_70, c_1766, c_68, c_1766, c_66, c_64, c_1619, c_62, c_1619, c_60, c_1619, c_58, c_1619, c_4203])).
% 9.01/3.11  tff(c_4212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1306, c_4210])).
% 9.01/3.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.01/3.11  
% 9.01/3.11  Inference rules
% 9.01/3.11  ----------------------
% 9.01/3.11  #Ref     : 0
% 9.01/3.11  #Sup     : 700
% 9.01/3.11  #Fact    : 0
% 9.01/3.11  #Define  : 0
% 9.01/3.11  #Split   : 18
% 9.01/3.11  #Chain   : 0
% 9.01/3.11  #Close   : 0
% 9.01/3.11  
% 9.01/3.11  Ordering : KBO
% 9.01/3.11  
% 9.01/3.11  Simplification rules
% 9.01/3.11  ----------------------
% 9.01/3.11  #Subsume      : 100
% 9.01/3.11  #Demod        : 2130
% 9.01/3.11  #Tautology    : 50
% 9.01/3.11  #SimpNegUnit  : 435
% 9.01/3.11  #BackRed      : 6
% 9.01/3.11  
% 9.01/3.11  #Partial instantiations: 0
% 9.01/3.11  #Strategies tried      : 1
% 9.01/3.11  
% 9.01/3.11  Timing (in seconds)
% 9.01/3.11  ----------------------
% 9.01/3.12  Preprocessing        : 0.45
% 9.01/3.12  Parsing              : 0.23
% 9.01/3.12  CNF conversion       : 0.06
% 9.01/3.12  Main loop            : 1.87
% 9.01/3.12  Inferencing          : 0.57
% 9.01/3.12  Reduction            : 0.55
% 9.01/3.12  Demodulation         : 0.42
% 9.01/3.12  BG Simplification    : 0.06
% 9.01/3.12  Subsumption          : 0.61
% 9.01/3.12  Abstraction          : 0.08
% 9.01/3.12  MUC search           : 0.00
% 9.01/3.12  Cooper               : 0.00
% 9.01/3.12  Total                : 2.38
% 9.01/3.12  Index Insertion      : 0.00
% 9.01/3.12  Index Deletion       : 0.00
% 9.01/3.12  Index Matching       : 0.00
% 9.01/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
