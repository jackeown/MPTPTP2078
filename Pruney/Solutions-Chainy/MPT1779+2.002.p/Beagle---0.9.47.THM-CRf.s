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
% DateTime   : Thu Dec  3 10:27:44 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  200 (5908 expanded)
%              Number of leaves         :   34 (2320 expanded)
%              Depth                    :   26
%              Number of atoms          :  906 (62568 expanded)
%              Number of equality atoms :   39 (1147 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_303,negated_conjecture,(
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
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(C,D)
                            & m1_pre_topc(E,C) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                             => ( ( v1_funct_1(k3_tmap_1(A,B,D,C,F))
                                  & v1_funct_2(k3_tmap_1(A,B,D,C,F),u1_struct_0(C),u1_struct_0(B))
                                  & v5_pre_topc(k3_tmap_1(A,B,D,C,F),C,B)
                                  & m1_subset_1(k3_tmap_1(A,B,D,C,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                               => ( v1_funct_1(k3_tmap_1(A,B,D,E,F))
                                  & v1_funct_2(k3_tmap_1(A,B,D,E,F),u1_struct_0(E),u1_struct_0(B))
                                  & v5_pre_topc(k3_tmap_1(A,B,D,E,F),E,B)
                                  & m1_subset_1(k3_tmap_1(A,B,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_196,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_116,axiom,(
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

tff(f_146,axiom,(
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

tff(f_184,axiom,(
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
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

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

tff(f_242,axiom,(
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
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & v5_pre_topc(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
                          & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
                          & v5_pre_topc(k3_tmap_1(A,B,C,D,E),D,B)
                          & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_106,plain,(
    ! [B_190,A_191] :
      ( v2_pre_topc(B_190)
      | ~ m1_pre_topc(B_190,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_106])).

tff(c_130,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_115])).

tff(c_75,plain,(
    ! [B_188,A_189] :
      ( l1_pre_topc(B_188)
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_84,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_75])).

tff(c_97,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_84])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_141,plain,(
    ! [C_192,A_193,B_194] :
      ( m1_pre_topc(C_192,A_193)
      | ~ m1_pre_topc(C_192,B_194)
      | ~ m1_pre_topc(B_194,A_193)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_155,plain,(
    ! [A_193] :
      ( m1_pre_topc('#skF_5',A_193)
      | ~ m1_pre_topc('#skF_3',A_193)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_48,c_141])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_44,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_1143,plain,(
    ! [E_328,C_329,D_330,A_327,B_331] :
      ( k3_tmap_1(A_327,B_331,C_329,D_330,E_328) = k2_partfun1(u1_struct_0(C_329),u1_struct_0(B_331),E_328,u1_struct_0(D_330))
      | ~ m1_pre_topc(D_330,C_329)
      | ~ m1_subset_1(E_328,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_329),u1_struct_0(B_331))))
      | ~ v1_funct_2(E_328,u1_struct_0(C_329),u1_struct_0(B_331))
      | ~ v1_funct_1(E_328)
      | ~ m1_pre_topc(D_330,A_327)
      | ~ m1_pre_topc(C_329,A_327)
      | ~ l1_pre_topc(B_331)
      | ~ v2_pre_topc(B_331)
      | v2_struct_0(B_331)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1151,plain,(
    ! [A_327,D_330] :
      ( k3_tmap_1(A_327,'#skF_2','#skF_4',D_330,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_330))
      | ~ m1_pre_topc(D_330,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_330,A_327)
      | ~ m1_pre_topc('#skF_4',A_327)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_42,c_1143])).

tff(c_1163,plain,(
    ! [A_327,D_330] :
      ( k3_tmap_1(A_327,'#skF_2','#skF_4',D_330,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_330))
      | ~ m1_pre_topc(D_330,'#skF_4')
      | ~ m1_pre_topc(D_330,A_327)
      | ~ m1_pre_topc('#skF_4',A_327)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_46,c_44,c_1151])).

tff(c_1165,plain,(
    ! [A_332,D_333] :
      ( k3_tmap_1(A_332,'#skF_2','#skF_4',D_333,'#skF_6') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_333))
      | ~ m1_pre_topc(D_333,'#skF_4')
      | ~ m1_pre_topc(D_333,A_332)
      | ~ m1_pre_topc('#skF_4',A_332)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1163])).

tff(c_1177,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1165])).

tff(c_1198,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_1177])).

tff(c_1199,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1198])).

tff(c_1346,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1199])).

tff(c_1352,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_1346])).

tff(c_1359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_1352])).

tff(c_1361,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1199])).

tff(c_1360,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1199])).

tff(c_1062,plain,(
    ! [A_304,B_305,C_306,D_307] :
      ( k2_partfun1(u1_struct_0(A_304),u1_struct_0(B_305),C_306,u1_struct_0(D_307)) = k2_tmap_1(A_304,B_305,C_306,D_307)
      | ~ m1_pre_topc(D_307,A_304)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_304),u1_struct_0(B_305))))
      | ~ v1_funct_2(C_306,u1_struct_0(A_304),u1_struct_0(B_305))
      | ~ v1_funct_1(C_306)
      | ~ l1_pre_topc(B_305)
      | ~ v2_pre_topc(B_305)
      | v2_struct_0(B_305)
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304)
      | v2_struct_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1068,plain,(
    ! [D_307] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_307)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_307)
      | ~ m1_pre_topc(D_307,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_1062])).

tff(c_1079,plain,(
    ! [D_307] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_307)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_307)
      | ~ m1_pre_topc(D_307,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_66,c_64,c_46,c_44,c_1068])).

tff(c_1080,plain,(
    ! [D_307] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_307)) = k2_tmap_1('#skF_4','#skF_2','#skF_6',D_307)
      | ~ m1_pre_topc(D_307,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_1079])).

tff(c_1446,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_1080])).

tff(c_1453,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_1446])).

tff(c_944,plain,(
    ! [E_285,C_288,D_287,A_286,B_284] :
      ( v1_funct_2(k3_tmap_1(A_286,B_284,C_288,D_287,E_285),u1_struct_0(D_287),u1_struct_0(B_284))
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_288),u1_struct_0(B_284))))
      | ~ v1_funct_2(E_285,u1_struct_0(C_288),u1_struct_0(B_284))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc(D_287,A_286)
      | ~ m1_pre_topc(C_288,A_286)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_950,plain,(
    ! [A_286,D_287] :
      ( v1_funct_2(k3_tmap_1(A_286,'#skF_2','#skF_4',D_287,'#skF_6'),u1_struct_0(D_287),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_287,A_286)
      | ~ m1_pre_topc('#skF_4',A_286)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_42,c_944])).

tff(c_961,plain,(
    ! [A_286,D_287] :
      ( v1_funct_2(k3_tmap_1(A_286,'#skF_2','#skF_4',D_287,'#skF_6'),u1_struct_0(D_287),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_287,A_286)
      | ~ m1_pre_topc('#skF_4',A_286)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_46,c_44,c_950])).

tff(c_963,plain,(
    ! [A_289,D_290] :
      ( v1_funct_2(k3_tmap_1(A_289,'#skF_2','#skF_4',D_290,'#skF_6'),u1_struct_0(D_290),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_290,A_289)
      | ~ m1_pre_topc('#skF_4',A_289)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_961])).

tff(c_752,plain,(
    ! [C_264,A_262,B_260,E_261,D_263] :
      ( m1_subset_1(k3_tmap_1(A_262,B_260,C_264,D_263,E_261),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_263),u1_struct_0(B_260))))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_264),u1_struct_0(B_260))))
      | ~ v1_funct_2(E_261,u1_struct_0(C_264),u1_struct_0(B_260))
      | ~ v1_funct_1(E_261)
      | ~ m1_pre_topc(D_263,A_262)
      | ~ m1_pre_topc(C_264,A_262)
      | ~ l1_pre_topc(B_260)
      | ~ v2_pre_topc(B_260)
      | v2_struct_0(B_260)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_380,plain,(
    ! [C_217,D_216,A_215,B_213,E_214] :
      ( v1_funct_1(k3_tmap_1(A_215,B_213,C_217,D_216,E_214))
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_217),u1_struct_0(B_213))))
      | ~ v1_funct_2(E_214,u1_struct_0(C_217),u1_struct_0(B_213))
      | ~ v1_funct_1(E_214)
      | ~ m1_pre_topc(D_216,A_215)
      | ~ m1_pre_topc(C_217,A_215)
      | ~ l1_pre_topc(B_213)
      | ~ v2_pre_topc(B_213)
      | v2_struct_0(B_213)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_384,plain,(
    ! [A_215,D_216] :
      ( v1_funct_1(k3_tmap_1(A_215,'#skF_2','#skF_4',D_216,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_216,A_215)
      | ~ m1_pre_topc('#skF_4',A_215)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_42,c_380])).

tff(c_391,plain,(
    ! [A_215,D_216] :
      ( v1_funct_1(k3_tmap_1(A_215,'#skF_2','#skF_4',D_216,'#skF_6'))
      | ~ m1_pre_topc(D_216,A_215)
      | ~ m1_pre_topc('#skF_4',A_215)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_46,c_44,c_384])).

tff(c_452,plain,(
    ! [A_220,D_221] :
      ( v1_funct_1(k3_tmap_1(A_220,'#skF_2','#skF_4',D_221,'#skF_6'))
      | ~ m1_pre_topc(D_221,A_220)
      | ~ m1_pre_topc('#skF_4',A_220)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_391])).

tff(c_32,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_210,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_455,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_452,c_210])).

tff(c_458,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_52,c_455])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_458])).

tff(c_461,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_584,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_761,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_752,c_584])).

tff(c_769,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_56,c_52,c_46,c_44,c_42,c_761])).

tff(c_771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_769])).

tff(c_772,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_827,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_966,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_963,c_827])).

tff(c_969,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_52,c_966])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_969])).

tff(c_972,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_1463,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),'#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_972])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_1183,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1165])).

tff(c_1210,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_50,c_1183])).

tff(c_1211,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1210])).

tff(c_1215,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1211,c_1080])).

tff(c_1222,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6') = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1215])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_121,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_106])).

tff(c_136,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_121])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_75])).

tff(c_101,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_90])).

tff(c_40,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_38,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_34,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_1066,plain,(
    ! [D_307] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_307)) = k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_307)
      | ~ m1_pre_topc(D_307,'#skF_3')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_1062])).

tff(c_1075,plain,(
    ! [D_307] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_307)) = k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_307)
      | ~ m1_pre_topc(D_307,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_101,c_66,c_64,c_40,c_38,c_1066])).

tff(c_1076,plain,(
    ! [D_307] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_307)) = k2_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),D_307)
      | ~ m1_pre_topc(D_307,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_1075])).

tff(c_1250,plain,(
    ! [D_307] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_307)) = k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),D_307)
      | ~ m1_pre_topc(D_307,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1222,c_1076])).

tff(c_1149,plain,(
    ! [A_327,D_330] :
      ( k3_tmap_1(A_327,'#skF_2','#skF_3',D_330,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_330))
      | ~ m1_pre_topc(D_330,'#skF_3')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ m1_pre_topc(D_330,A_327)
      | ~ m1_pre_topc('#skF_3',A_327)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_34,c_1143])).

tff(c_1159,plain,(
    ! [A_327,D_330] :
      ( k3_tmap_1(A_327,'#skF_2','#skF_3',D_330,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_330))
      | ~ m1_pre_topc(D_330,'#skF_3')
      | ~ m1_pre_topc(D_330,A_327)
      | ~ m1_pre_topc('#skF_3',A_327)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_40,c_38,c_1149])).

tff(c_1160,plain,(
    ! [A_327,D_330] :
      ( k3_tmap_1(A_327,'#skF_2','#skF_3',D_330,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0(D_330))
      | ~ m1_pre_topc(D_330,'#skF_3')
      | ~ m1_pre_topc(D_330,A_327)
      | ~ m1_pre_topc('#skF_3',A_327)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1159])).

tff(c_1679,plain,(
    ! [A_327,D_330] :
      ( k3_tmap_1(A_327,'#skF_2','#skF_3',D_330,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_330))
      | ~ m1_pre_topc(D_330,'#skF_3')
      | ~ m1_pre_topc(D_330,A_327)
      | ~ m1_pre_topc('#skF_3',A_327)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1222,c_1160])).

tff(c_1090,plain,(
    ! [D_312,B_309,C_313,A_311,E_310] :
      ( v1_funct_2(k3_tmap_1(A_311,B_309,C_313,D_312,E_310),u1_struct_0(D_312),u1_struct_0(B_309))
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_313),u1_struct_0(B_309))))
      | ~ v1_funct_2(E_310,u1_struct_0(C_313),u1_struct_0(B_309))
      | ~ v1_funct_1(E_310)
      | ~ m1_pre_topc(D_312,A_311)
      | ~ m1_pre_topc(C_313,A_311)
      | ~ l1_pre_topc(B_309)
      | ~ v2_pre_topc(B_309)
      | v2_struct_0(B_309)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1094,plain,(
    ! [A_311,D_312] :
      ( v1_funct_2(k3_tmap_1(A_311,'#skF_2','#skF_3',D_312,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0(D_312),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ m1_pre_topc(D_312,A_311)
      | ~ m1_pre_topc('#skF_3',A_311)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(resolution,[status(thm)],[c_34,c_1090])).

tff(c_1103,plain,(
    ! [A_311,D_312] :
      ( v1_funct_2(k3_tmap_1(A_311,'#skF_2','#skF_3',D_312,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0(D_312),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_312,A_311)
      | ~ m1_pre_topc('#skF_3',A_311)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_40,c_38,c_1094])).

tff(c_1104,plain,(
    ! [A_311,D_312] :
      ( v1_funct_2(k3_tmap_1(A_311,'#skF_2','#skF_3',D_312,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0(D_312),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_312,A_311)
      | ~ m1_pre_topc('#skF_3',A_311)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1103])).

tff(c_1713,plain,(
    ! [A_361,D_362] :
      ( v1_funct_2(k3_tmap_1(A_361,'#skF_2','#skF_3',D_362,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),u1_struct_0(D_362),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_362,A_361)
      | ~ m1_pre_topc('#skF_3',A_361)
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361)
      | v2_struct_0(A_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1104])).

tff(c_2726,plain,(
    ! [D_426,A_427] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_426)),u1_struct_0(D_426),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_426,A_427)
      | ~ m1_pre_topc('#skF_3',A_427)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427)
      | ~ m1_pre_topc(D_426,'#skF_3')
      | ~ m1_pre_topc(D_426,A_427)
      | ~ m1_pre_topc('#skF_3',A_427)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1679,c_1713])).

tff(c_2730,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1361,c_2726])).

tff(c_2754,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_1361,c_48,c_2730])).

tff(c_2755,plain,(
    v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2754])).

tff(c_2789,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_2755])).

tff(c_2793,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2789])).

tff(c_1680,plain,(
    ! [A_359,D_360] :
      ( k3_tmap_1(A_359,'#skF_2','#skF_3',D_360,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_360))
      | ~ m1_pre_topc(D_360,'#skF_3')
      | ~ m1_pre_topc(D_360,A_359)
      | ~ m1_pre_topc('#skF_3',A_359)
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1222,c_1160])).

tff(c_1689,plain,(
    ! [A_359,D_360] :
      ( k3_tmap_1(A_359,'#skF_2','#skF_3',D_360,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),D_360)
      | ~ m1_pre_topc(D_360,'#skF_3')
      | ~ m1_pre_topc(D_360,'#skF_3')
      | ~ m1_pre_topc(D_360,A_359)
      | ~ m1_pre_topc('#skF_3',A_359)
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_1250])).

tff(c_1040,plain,(
    ! [D_296,B_293,C_297,A_295,E_294] :
      ( v1_funct_1(k3_tmap_1(A_295,B_293,C_297,D_296,E_294))
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_297),u1_struct_0(B_293))))
      | ~ v1_funct_2(E_294,u1_struct_0(C_297),u1_struct_0(B_293))
      | ~ v1_funct_1(E_294)
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc(C_297,A_295)
      | ~ l1_pre_topc(B_293)
      | ~ v2_pre_topc(B_293)
      | v2_struct_0(B_293)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1044,plain,(
    ! [A_295,D_296] :
      ( v1_funct_1(k3_tmap_1(A_295,'#skF_2','#skF_3',D_296,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_3',A_295)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_34,c_1040])).

tff(c_1053,plain,(
    ! [A_295,D_296] :
      ( v1_funct_1(k3_tmap_1(A_295,'#skF_2','#skF_3',D_296,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')))
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_3',A_295)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_40,c_38,c_1044])).

tff(c_1054,plain,(
    ! [A_295,D_296] :
      ( v1_funct_1(k3_tmap_1(A_295,'#skF_2','#skF_3',D_296,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')))
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_3',A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1053])).

tff(c_1251,plain,(
    ! [A_295,D_296] :
      ( v1_funct_1(k3_tmap_1(A_295,'#skF_2','#skF_3',D_296,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')))
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_3',A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1054])).

tff(c_2387,plain,(
    ! [D_405,A_406] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_405)))
      | ~ m1_pre_topc(D_405,A_406)
      | ~ m1_pre_topc('#skF_3',A_406)
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406)
      | ~ m1_pre_topc(D_405,'#skF_3')
      | ~ m1_pre_topc(D_405,A_406)
      | ~ m1_pre_topc('#skF_3',A_406)
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_1251])).

tff(c_2391,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1361,c_2387])).

tff(c_2415,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_1361,c_48,c_2391])).

tff(c_2416,plain,(
    v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2415])).

tff(c_2450,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_2416])).

tff(c_2454,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2450])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_1046,plain,(
    ! [A_295,D_296] :
      ( v1_funct_1(k3_tmap_1(A_295,'#skF_2','#skF_4',D_296,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_4',A_295)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_42,c_1040])).

tff(c_1057,plain,(
    ! [A_295,D_296] :
      ( v1_funct_1(k3_tmap_1(A_295,'#skF_2','#skF_4',D_296,'#skF_6'))
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_4',A_295)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_46,c_44,c_1046])).

tff(c_1058,plain,(
    ! [A_295,D_296] :
      ( v1_funct_1(k3_tmap_1(A_295,'#skF_2','#skF_4',D_296,'#skF_6'))
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_4',A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1057])).

tff(c_1475,plain,
    ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1453,c_1058])).

tff(c_1485,plain,
    ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_52,c_1475])).

tff(c_1486,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1485])).

tff(c_973,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_1462,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_973])).

tff(c_773,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_1464,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_773])).

tff(c_1256,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_40])).

tff(c_1254,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_38])).

tff(c_1253,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_34])).

tff(c_14,plain,(
    ! [A_57,E_61,B_58,D_60,C_59] :
      ( m1_subset_1(k3_tmap_1(A_57,B_58,C_59,D_60,E_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_60),u1_struct_0(B_58))))
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59),u1_struct_0(B_58))))
      | ~ v1_funct_2(E_61,u1_struct_0(C_59),u1_struct_0(B_58))
      | ~ v1_funct_1(E_61)
      | ~ m1_pre_topc(D_60,A_57)
      | ~ m1_pre_topc(C_59,A_57)
      | ~ l1_pre_topc(B_58)
      | ~ v2_pre_topc(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1698,plain,(
    ! [D_360,A_359] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_360)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_360),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'))
      | ~ m1_pre_topc(D_360,A_359)
      | ~ m1_pre_topc('#skF_3',A_359)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359)
      | ~ m1_pre_topc(D_360,'#skF_3')
      | ~ m1_pre_topc(D_360,A_359)
      | ~ m1_pre_topc('#skF_3',A_359)
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_14])).

tff(c_1710,plain,(
    ! [D_360,A_359] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_360)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_360),u1_struct_0('#skF_2'))))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_360,'#skF_3')
      | ~ m1_pre_topc(D_360,A_359)
      | ~ m1_pre_topc('#skF_3',A_359)
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1256,c_1254,c_1253,c_1698])).

tff(c_1861,plain,(
    ! [D_372,A_373] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_372)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_372),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_372,'#skF_3')
      | ~ m1_pre_topc(D_372,A_373)
      | ~ m1_pre_topc('#skF_3',A_373)
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373)
      | v2_struct_0(A_373) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1710])).

tff(c_1865,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1361,c_1861])).

tff(c_1889,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_48,c_1865])).

tff(c_1890,plain,(
    m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1889])).

tff(c_1933,plain,(
    ! [A_327] :
      ( m1_subset_1(k3_tmap_1(A_327,'#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ m1_pre_topc('#skF_5',A_327)
      | ~ m1_pre_topc('#skF_3',A_327)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1679,c_1890])).

tff(c_1959,plain,(
    ! [A_327] :
      ( m1_subset_1(k3_tmap_1(A_327,'#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc('#skF_5',A_327)
      | ~ m1_pre_topc('#skF_3',A_327)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1933])).

tff(c_1318,plain,(
    ! [B_341,E_342,D_339,A_343,C_340] :
      ( r2_funct_2(u1_struct_0(C_340),u1_struct_0(B_341),k3_tmap_1(A_343,B_341,D_339,C_340,k2_tmap_1(A_343,B_341,E_342,D_339)),k2_tmap_1(A_343,B_341,E_342,C_340))
      | ~ m1_pre_topc(C_340,D_339)
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_343),u1_struct_0(B_341))))
      | ~ v1_funct_2(E_342,u1_struct_0(A_343),u1_struct_0(B_341))
      | ~ v1_funct_1(E_342)
      | ~ m1_pre_topc(D_339,A_343)
      | v2_struct_0(D_339)
      | ~ m1_pre_topc(C_340,A_343)
      | v2_struct_0(C_340)
      | ~ l1_pre_topc(B_341)
      | ~ v2_pre_topc(B_341)
      | v2_struct_0(B_341)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3040,plain,(
    ! [E_447,B_445,D_448,C_449,A_446] :
      ( k3_tmap_1(A_446,B_445,D_448,C_449,k2_tmap_1(A_446,B_445,E_447,D_448)) = k2_tmap_1(A_446,B_445,E_447,C_449)
      | ~ m1_subset_1(k2_tmap_1(A_446,B_445,E_447,C_449),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_449),u1_struct_0(B_445))))
      | ~ v1_funct_2(k2_tmap_1(A_446,B_445,E_447,C_449),u1_struct_0(C_449),u1_struct_0(B_445))
      | ~ v1_funct_1(k2_tmap_1(A_446,B_445,E_447,C_449))
      | ~ m1_subset_1(k3_tmap_1(A_446,B_445,D_448,C_449,k2_tmap_1(A_446,B_445,E_447,D_448)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_449),u1_struct_0(B_445))))
      | ~ v1_funct_2(k3_tmap_1(A_446,B_445,D_448,C_449,k2_tmap_1(A_446,B_445,E_447,D_448)),u1_struct_0(C_449),u1_struct_0(B_445))
      | ~ v1_funct_1(k3_tmap_1(A_446,B_445,D_448,C_449,k2_tmap_1(A_446,B_445,E_447,D_448)))
      | ~ m1_pre_topc(C_449,D_448)
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_446),u1_struct_0(B_445))))
      | ~ v1_funct_2(E_447,u1_struct_0(A_446),u1_struct_0(B_445))
      | ~ v1_funct_1(E_447)
      | ~ m1_pre_topc(D_448,A_446)
      | v2_struct_0(D_448)
      | ~ m1_pre_topc(C_449,A_446)
      | v2_struct_0(C_449)
      | ~ l1_pre_topc(B_445)
      | ~ v2_pre_topc(B_445)
      | v2_struct_0(B_445)
      | ~ l1_pre_topc(A_446)
      | ~ v2_pre_topc(A_446)
      | v2_struct_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_1318,c_4])).

tff(c_3052,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1959,c_3040])).

tff(c_3065,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_1361,c_66,c_64,c_46,c_44,c_42,c_48,c_1486,c_1462,c_1464,c_3052])).

tff(c_3066,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_54,c_62,c_3065])).

tff(c_3085,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3066])).

tff(c_3088,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1689,c_3085])).

tff(c_3093,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_1361,c_48,c_48,c_2454,c_3088])).

tff(c_3095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3093])).

tff(c_3096,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3066])).

tff(c_3104,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3096])).

tff(c_3120,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1689,c_3104])).

tff(c_3125,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_1361,c_48,c_48,c_2793,c_3120])).

tff(c_3127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3125])).

tff(c_3128,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')) = k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3096])).

tff(c_36,plain,(
    v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_1226,plain,(
    ! [D_335,C_338,A_336,E_334,B_337] :
      ( v5_pre_topc(k3_tmap_1(A_336,B_337,C_338,D_335,E_334),D_335,B_337)
      | ~ m1_pre_topc(D_335,C_338)
      | ~ m1_subset_1(E_334,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_338),u1_struct_0(B_337))))
      | ~ v5_pre_topc(E_334,C_338,B_337)
      | ~ v1_funct_2(E_334,u1_struct_0(C_338),u1_struct_0(B_337))
      | ~ v1_funct_1(E_334)
      | ~ m1_pre_topc(D_335,A_336)
      | v2_struct_0(D_335)
      | ~ m1_pre_topc(C_338,A_336)
      | v2_struct_0(C_338)
      | ~ l1_pre_topc(B_337)
      | ~ v2_pre_topc(B_337)
      | v2_struct_0(B_337)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_1232,plain,(
    ! [A_336,D_335] :
      ( v5_pre_topc(k3_tmap_1(A_336,'#skF_2','#skF_3',D_335,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),D_335,'#skF_2')
      | ~ m1_pre_topc(D_335,'#skF_3')
      | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
      | ~ m1_pre_topc(D_335,A_336)
      | v2_struct_0(D_335)
      | ~ m1_pre_topc('#skF_3',A_336)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_34,c_1226])).

tff(c_1242,plain,(
    ! [A_336,D_335] :
      ( v5_pre_topc(k3_tmap_1(A_336,'#skF_2','#skF_3',D_335,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),D_335,'#skF_2')
      | ~ m1_pre_topc(D_335,'#skF_3')
      | ~ m1_pre_topc(D_335,A_336)
      | v2_struct_0(D_335)
      | ~ m1_pre_topc('#skF_3',A_336)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_40,c_38,c_36,c_1232])).

tff(c_1243,plain,(
    ! [A_336,D_335] :
      ( v5_pre_topc(k3_tmap_1(A_336,'#skF_2','#skF_3',D_335,k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),D_335,'#skF_2')
      | ~ m1_pre_topc(D_335,'#skF_3')
      | ~ m1_pre_topc(D_335,A_336)
      | v2_struct_0(D_335)
      | ~ m1_pre_topc('#skF_3',A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1242])).

tff(c_1491,plain,(
    ! [A_336,D_335] :
      ( v5_pre_topc(k3_tmap_1(A_336,'#skF_2','#skF_3',D_335,k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),D_335,'#skF_2')
      | ~ m1_pre_topc(D_335,'#skF_3')
      | ~ m1_pre_topc(D_335,A_336)
      | v2_struct_0(D_335)
      | ~ m1_pre_topc('#skF_3',A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1243])).

tff(c_2967,plain,(
    ! [D_443,A_444] :
      ( v5_pre_topc(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0(D_443)),D_443,'#skF_2')
      | ~ m1_pre_topc(D_443,'#skF_3')
      | ~ m1_pre_topc(D_443,A_444)
      | v2_struct_0(D_443)
      | ~ m1_pre_topc('#skF_3',A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444)
      | ~ m1_pre_topc(D_443,'#skF_3')
      | ~ m1_pre_topc(D_443,A_444)
      | ~ m1_pre_topc('#skF_3',A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_1491])).

tff(c_2971,plain,
    ( v5_pre_topc(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),'#skF_5','#skF_2')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1361,c_2967])).

tff(c_2996,plain,
    ( v5_pre_topc(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),'#skF_5','#skF_2')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_1361,c_48,c_2971])).

tff(c_2997,plain,(
    v5_pre_topc(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3'),u1_struct_0('#skF_5')),'#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_2996])).

tff(c_3032,plain,(
    ! [A_327] :
      ( v5_pre_topc(k3_tmap_1(A_327,'#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),'#skF_5','#skF_2')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ m1_pre_topc('#skF_5',A_327)
      | ~ m1_pre_topc('#skF_3',A_327)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1679,c_2997])).

tff(c_3037,plain,(
    ! [A_327] :
      ( v5_pre_topc(k3_tmap_1(A_327,'#skF_2','#skF_3','#skF_5',k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_3')),'#skF_5','#skF_2')
      | ~ m1_pre_topc('#skF_5',A_327)
      | ~ m1_pre_topc('#skF_3',A_327)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3032])).

tff(c_3135,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),'#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_3037])).

tff(c_3179,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_4','#skF_2','#skF_6','#skF_5'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_97,c_50,c_1361,c_3135])).

tff(c_3181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1463,c_3179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:58:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.44  
% 7.58/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.44  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.58/2.44  
% 7.58/2.44  %Foreground sorts:
% 7.58/2.44  
% 7.58/2.44  
% 7.58/2.44  %Background operators:
% 7.58/2.44  
% 7.58/2.44  
% 7.58/2.44  %Foreground operators:
% 7.58/2.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.58/2.44  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.58/2.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.58/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.58/2.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.58/2.44  tff('#skF_5', type, '#skF_5': $i).
% 7.58/2.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.58/2.44  tff('#skF_6', type, '#skF_6': $i).
% 7.58/2.44  tff('#skF_2', type, '#skF_2': $i).
% 7.58/2.44  tff('#skF_3', type, '#skF_3': $i).
% 7.58/2.44  tff('#skF_1', type, '#skF_1': $i).
% 7.58/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.58/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.58/2.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.58/2.44  tff('#skF_4', type, '#skF_4': $i).
% 7.58/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.58/2.44  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.58/2.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.58/2.44  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.58/2.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.58/2.44  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.58/2.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.58/2.44  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.58/2.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.58/2.44  
% 7.58/2.47  tff(f_303, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(C, D) & m1_pre_topc(E, C)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((v1_funct_1(k3_tmap_1(A, B, D, C, F)) & v1_funct_2(k3_tmap_1(A, B, D, C, F), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, D, C, F), C, B)) & m1_subset_1(k3_tmap_1(A, B, D, C, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (((v1_funct_1(k3_tmap_1(A, B, D, E, F)) & v1_funct_2(k3_tmap_1(A, B, D, E, F), u1_struct_0(E), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, D, E, F), E, B)) & m1_subset_1(k3_tmap_1(A, B, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_tmap_1)).
% 7.58/2.47  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.58/2.47  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.58/2.47  tff(f_196, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 7.58/2.47  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.58/2.47  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.58/2.47  tff(f_146, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 7.58/2.47  tff(f_184, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 7.58/2.47  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.58/2.47  tff(f_242, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, C, D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_tmap_1)).
% 7.58/2.47  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_106, plain, (![B_190, A_191]: (v2_pre_topc(B_190) | ~m1_pre_topc(B_190, A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.58/2.47  tff(c_115, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_106])).
% 7.58/2.47  tff(c_130, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_115])).
% 7.58/2.47  tff(c_75, plain, (![B_188, A_189]: (l1_pre_topc(B_188) | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.58/2.47  tff(c_84, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_75])).
% 7.58/2.47  tff(c_97, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_84])).
% 7.58/2.47  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_141, plain, (![C_192, A_193, B_194]: (m1_pre_topc(C_192, A_193) | ~m1_pre_topc(C_192, B_194) | ~m1_pre_topc(B_194, A_193) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.58/2.47  tff(c_155, plain, (![A_193]: (m1_pre_topc('#skF_5', A_193) | ~m1_pre_topc('#skF_3', A_193) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193))), inference(resolution, [status(thm)], [c_48, c_141])).
% 7.58/2.47  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_44, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_1143, plain, (![E_328, C_329, D_330, A_327, B_331]: (k3_tmap_1(A_327, B_331, C_329, D_330, E_328)=k2_partfun1(u1_struct_0(C_329), u1_struct_0(B_331), E_328, u1_struct_0(D_330)) | ~m1_pre_topc(D_330, C_329) | ~m1_subset_1(E_328, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_329), u1_struct_0(B_331)))) | ~v1_funct_2(E_328, u1_struct_0(C_329), u1_struct_0(B_331)) | ~v1_funct_1(E_328) | ~m1_pre_topc(D_330, A_327) | ~m1_pre_topc(C_329, A_327) | ~l1_pre_topc(B_331) | ~v2_pre_topc(B_331) | v2_struct_0(B_331) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.58/2.47  tff(c_1151, plain, (![A_327, D_330]: (k3_tmap_1(A_327, '#skF_2', '#skF_4', D_330, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_330)) | ~m1_pre_topc(D_330, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_330, A_327) | ~m1_pre_topc('#skF_4', A_327) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(resolution, [status(thm)], [c_42, c_1143])).
% 7.58/2.47  tff(c_1163, plain, (![A_327, D_330]: (k3_tmap_1(A_327, '#skF_2', '#skF_4', D_330, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_330)) | ~m1_pre_topc(D_330, '#skF_4') | ~m1_pre_topc(D_330, A_327) | ~m1_pre_topc('#skF_4', A_327) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_46, c_44, c_1151])).
% 7.58/2.47  tff(c_1165, plain, (![A_332, D_333]: (k3_tmap_1(A_332, '#skF_2', '#skF_4', D_333, '#skF_6')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_333)) | ~m1_pre_topc(D_333, '#skF_4') | ~m1_pre_topc(D_333, A_332) | ~m1_pre_topc('#skF_4', A_332) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(negUnitSimplification, [status(thm)], [c_68, c_1163])).
% 7.58/2.47  tff(c_1177, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1165])).
% 7.58/2.47  tff(c_1198, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_1177])).
% 7.58/2.47  tff(c_1199, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_1198])).
% 7.58/2.47  tff(c_1346, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1199])).
% 7.58/2.47  tff(c_1352, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_155, c_1346])).
% 7.58/2.47  tff(c_1359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_1352])).
% 7.58/2.47  tff(c_1361, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1199])).
% 7.58/2.47  tff(c_1360, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1199])).
% 7.58/2.47  tff(c_1062, plain, (![A_304, B_305, C_306, D_307]: (k2_partfun1(u1_struct_0(A_304), u1_struct_0(B_305), C_306, u1_struct_0(D_307))=k2_tmap_1(A_304, B_305, C_306, D_307) | ~m1_pre_topc(D_307, A_304) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_304), u1_struct_0(B_305)))) | ~v1_funct_2(C_306, u1_struct_0(A_304), u1_struct_0(B_305)) | ~v1_funct_1(C_306) | ~l1_pre_topc(B_305) | ~v2_pre_topc(B_305) | v2_struct_0(B_305) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304) | v2_struct_0(A_304))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.58/2.47  tff(c_1068, plain, (![D_307]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_307))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_307) | ~m1_pre_topc(D_307, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_1062])).
% 7.58/2.47  tff(c_1079, plain, (![D_307]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_307))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_307) | ~m1_pre_topc(D_307, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_66, c_64, c_46, c_44, c_1068])).
% 7.58/2.47  tff(c_1080, plain, (![D_307]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_307))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', D_307) | ~m1_pre_topc(D_307, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_1079])).
% 7.58/2.47  tff(c_1446, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1360, c_1080])).
% 7.58/2.47  tff(c_1453, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_1446])).
% 7.58/2.47  tff(c_944, plain, (![E_285, C_288, D_287, A_286, B_284]: (v1_funct_2(k3_tmap_1(A_286, B_284, C_288, D_287, E_285), u1_struct_0(D_287), u1_struct_0(B_284)) | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_288), u1_struct_0(B_284)))) | ~v1_funct_2(E_285, u1_struct_0(C_288), u1_struct_0(B_284)) | ~v1_funct_1(E_285) | ~m1_pre_topc(D_287, A_286) | ~m1_pre_topc(C_288, A_286) | ~l1_pre_topc(B_284) | ~v2_pre_topc(B_284) | v2_struct_0(B_284) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.58/2.47  tff(c_950, plain, (![A_286, D_287]: (v1_funct_2(k3_tmap_1(A_286, '#skF_2', '#skF_4', D_287, '#skF_6'), u1_struct_0(D_287), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_287, A_286) | ~m1_pre_topc('#skF_4', A_286) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(resolution, [status(thm)], [c_42, c_944])).
% 7.58/2.47  tff(c_961, plain, (![A_286, D_287]: (v1_funct_2(k3_tmap_1(A_286, '#skF_2', '#skF_4', D_287, '#skF_6'), u1_struct_0(D_287), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_287, A_286) | ~m1_pre_topc('#skF_4', A_286) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_46, c_44, c_950])).
% 7.58/2.47  tff(c_963, plain, (![A_289, D_290]: (v1_funct_2(k3_tmap_1(A_289, '#skF_2', '#skF_4', D_290, '#skF_6'), u1_struct_0(D_290), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_290, A_289) | ~m1_pre_topc('#skF_4', A_289) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289) | v2_struct_0(A_289))), inference(negUnitSimplification, [status(thm)], [c_68, c_961])).
% 7.58/2.47  tff(c_752, plain, (![C_264, A_262, B_260, E_261, D_263]: (m1_subset_1(k3_tmap_1(A_262, B_260, C_264, D_263, E_261), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_263), u1_struct_0(B_260)))) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_264), u1_struct_0(B_260)))) | ~v1_funct_2(E_261, u1_struct_0(C_264), u1_struct_0(B_260)) | ~v1_funct_1(E_261) | ~m1_pre_topc(D_263, A_262) | ~m1_pre_topc(C_264, A_262) | ~l1_pre_topc(B_260) | ~v2_pre_topc(B_260) | v2_struct_0(B_260) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.58/2.47  tff(c_380, plain, (![C_217, D_216, A_215, B_213, E_214]: (v1_funct_1(k3_tmap_1(A_215, B_213, C_217, D_216, E_214)) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_217), u1_struct_0(B_213)))) | ~v1_funct_2(E_214, u1_struct_0(C_217), u1_struct_0(B_213)) | ~v1_funct_1(E_214) | ~m1_pre_topc(D_216, A_215) | ~m1_pre_topc(C_217, A_215) | ~l1_pre_topc(B_213) | ~v2_pre_topc(B_213) | v2_struct_0(B_213) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.58/2.47  tff(c_384, plain, (![A_215, D_216]: (v1_funct_1(k3_tmap_1(A_215, '#skF_2', '#skF_4', D_216, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_216, A_215) | ~m1_pre_topc('#skF_4', A_215) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_42, c_380])).
% 7.58/2.47  tff(c_391, plain, (![A_215, D_216]: (v1_funct_1(k3_tmap_1(A_215, '#skF_2', '#skF_4', D_216, '#skF_6')) | ~m1_pre_topc(D_216, A_215) | ~m1_pre_topc('#skF_4', A_215) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_46, c_44, c_384])).
% 7.58/2.47  tff(c_452, plain, (![A_220, D_221]: (v1_funct_1(k3_tmap_1(A_220, '#skF_2', '#skF_4', D_221, '#skF_6')) | ~m1_pre_topc(D_221, A_220) | ~m1_pre_topc('#skF_4', A_220) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(negUnitSimplification, [status(thm)], [c_68, c_391])).
% 7.58/2.47  tff(c_32, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_210, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_32])).
% 7.58/2.47  tff(c_455, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_452, c_210])).
% 7.58/2.47  tff(c_458, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_52, c_455])).
% 7.58/2.47  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_458])).
% 7.58/2.47  tff(c_461, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_32])).
% 7.58/2.47  tff(c_584, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_461])).
% 7.58/2.47  tff(c_761, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_752, c_584])).
% 7.58/2.47  tff(c_769, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_56, c_52, c_46, c_44, c_42, c_761])).
% 7.58/2.47  tff(c_771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_769])).
% 7.58/2.47  tff(c_772, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_461])).
% 7.58/2.47  tff(c_827, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_772])).
% 7.58/2.47  tff(c_966, plain, (~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_963, c_827])).
% 7.58/2.47  tff(c_969, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_52, c_966])).
% 7.58/2.47  tff(c_971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_969])).
% 7.58/2.47  tff(c_972, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), '#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_772])).
% 7.58/2.47  tff(c_1463, plain, (~v5_pre_topc(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), '#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_972])).
% 7.58/2.47  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_1183, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_1165])).
% 7.58/2.47  tff(c_1210, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_50, c_1183])).
% 7.58/2.47  tff(c_1211, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_1210])).
% 7.58/2.47  tff(c_1215, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1211, c_1080])).
% 7.58/2.47  tff(c_1222, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1215])).
% 7.58/2.47  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_121, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_106])).
% 7.58/2.47  tff(c_136, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_121])).
% 7.58/2.47  tff(c_90, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_75])).
% 7.58/2.47  tff(c_101, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_90])).
% 7.58/2.47  tff(c_40, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_38, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_34, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_1066, plain, (![D_307]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_307))=k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_307) | ~m1_pre_topc(D_307, '#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_1062])).
% 7.58/2.47  tff(c_1075, plain, (![D_307]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_307))=k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_307) | ~m1_pre_topc(D_307, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_101, c_66, c_64, c_40, c_38, c_1066])).
% 7.58/2.47  tff(c_1076, plain, (![D_307]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_307))=k2_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), D_307) | ~m1_pre_topc(D_307, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_1075])).
% 7.58/2.47  tff(c_1250, plain, (![D_307]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_307))=k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), D_307) | ~m1_pre_topc(D_307, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1222, c_1076])).
% 7.58/2.47  tff(c_1149, plain, (![A_327, D_330]: (k3_tmap_1(A_327, '#skF_2', '#skF_3', D_330, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_330)) | ~m1_pre_topc(D_330, '#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc(D_330, A_327) | ~m1_pre_topc('#skF_3', A_327) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(resolution, [status(thm)], [c_34, c_1143])).
% 7.58/2.47  tff(c_1159, plain, (![A_327, D_330]: (k3_tmap_1(A_327, '#skF_2', '#skF_3', D_330, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_330)) | ~m1_pre_topc(D_330, '#skF_3') | ~m1_pre_topc(D_330, A_327) | ~m1_pre_topc('#skF_3', A_327) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_40, c_38, c_1149])).
% 7.58/2.47  tff(c_1160, plain, (![A_327, D_330]: (k3_tmap_1(A_327, '#skF_2', '#skF_3', D_330, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0(D_330)) | ~m1_pre_topc(D_330, '#skF_3') | ~m1_pre_topc(D_330, A_327) | ~m1_pre_topc('#skF_3', A_327) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(negUnitSimplification, [status(thm)], [c_68, c_1159])).
% 7.58/2.47  tff(c_1679, plain, (![A_327, D_330]: (k3_tmap_1(A_327, '#skF_2', '#skF_3', D_330, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_330)) | ~m1_pre_topc(D_330, '#skF_3') | ~m1_pre_topc(D_330, A_327) | ~m1_pre_topc('#skF_3', A_327) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1222, c_1160])).
% 7.58/2.47  tff(c_1090, plain, (![D_312, B_309, C_313, A_311, E_310]: (v1_funct_2(k3_tmap_1(A_311, B_309, C_313, D_312, E_310), u1_struct_0(D_312), u1_struct_0(B_309)) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_313), u1_struct_0(B_309)))) | ~v1_funct_2(E_310, u1_struct_0(C_313), u1_struct_0(B_309)) | ~v1_funct_1(E_310) | ~m1_pre_topc(D_312, A_311) | ~m1_pre_topc(C_313, A_311) | ~l1_pre_topc(B_309) | ~v2_pre_topc(B_309) | v2_struct_0(B_309) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.58/2.47  tff(c_1094, plain, (![A_311, D_312]: (v1_funct_2(k3_tmap_1(A_311, '#skF_2', '#skF_3', D_312, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), u1_struct_0(D_312), u1_struct_0('#skF_2')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc(D_312, A_311) | ~m1_pre_topc('#skF_3', A_311) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(resolution, [status(thm)], [c_34, c_1090])).
% 7.58/2.47  tff(c_1103, plain, (![A_311, D_312]: (v1_funct_2(k3_tmap_1(A_311, '#skF_2', '#skF_3', D_312, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), u1_struct_0(D_312), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_312, A_311) | ~m1_pre_topc('#skF_3', A_311) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_40, c_38, c_1094])).
% 7.58/2.47  tff(c_1104, plain, (![A_311, D_312]: (v1_funct_2(k3_tmap_1(A_311, '#skF_2', '#skF_3', D_312, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), u1_struct_0(D_312), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_312, A_311) | ~m1_pre_topc('#skF_3', A_311) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(negUnitSimplification, [status(thm)], [c_68, c_1103])).
% 7.58/2.47  tff(c_1713, plain, (![A_361, D_362]: (v1_funct_2(k3_tmap_1(A_361, '#skF_2', '#skF_3', D_362, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), u1_struct_0(D_362), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_362, A_361) | ~m1_pre_topc('#skF_3', A_361) | ~l1_pre_topc(A_361) | ~v2_pre_topc(A_361) | v2_struct_0(A_361))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1104])).
% 7.58/2.47  tff(c_2726, plain, (![D_426, A_427]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_426)), u1_struct_0(D_426), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_426, A_427) | ~m1_pre_topc('#skF_3', A_427) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427) | ~m1_pre_topc(D_426, '#skF_3') | ~m1_pre_topc(D_426, A_427) | ~m1_pre_topc('#skF_3', A_427) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(superposition, [status(thm), theory('equality')], [c_1679, c_1713])).
% 7.58/2.47  tff(c_2730, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1361, c_2726])).
% 7.58/2.47  tff(c_2754, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_1361, c_48, c_2730])).
% 7.58/2.47  tff(c_2755, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2754])).
% 7.58/2.47  tff(c_2789, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1250, c_2755])).
% 7.58/2.47  tff(c_2793, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2789])).
% 7.58/2.47  tff(c_1680, plain, (![A_359, D_360]: (k3_tmap_1(A_359, '#skF_2', '#skF_3', D_360, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_360)) | ~m1_pre_topc(D_360, '#skF_3') | ~m1_pre_topc(D_360, A_359) | ~m1_pre_topc('#skF_3', A_359) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1222, c_1160])).
% 7.58/2.47  tff(c_1689, plain, (![A_359, D_360]: (k3_tmap_1(A_359, '#skF_2', '#skF_3', D_360, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), D_360) | ~m1_pre_topc(D_360, '#skF_3') | ~m1_pre_topc(D_360, '#skF_3') | ~m1_pre_topc(D_360, A_359) | ~m1_pre_topc('#skF_3', A_359) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(superposition, [status(thm), theory('equality')], [c_1680, c_1250])).
% 7.58/2.47  tff(c_1040, plain, (![D_296, B_293, C_297, A_295, E_294]: (v1_funct_1(k3_tmap_1(A_295, B_293, C_297, D_296, E_294)) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_297), u1_struct_0(B_293)))) | ~v1_funct_2(E_294, u1_struct_0(C_297), u1_struct_0(B_293)) | ~v1_funct_1(E_294) | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc(C_297, A_295) | ~l1_pre_topc(B_293) | ~v2_pre_topc(B_293) | v2_struct_0(B_293) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.58/2.47  tff(c_1044, plain, (![A_295, D_296]: (v1_funct_1(k3_tmap_1(A_295, '#skF_2', '#skF_3', D_296, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_3', A_295) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(resolution, [status(thm)], [c_34, c_1040])).
% 7.58/2.47  tff(c_1053, plain, (![A_295, D_296]: (v1_funct_1(k3_tmap_1(A_295, '#skF_2', '#skF_3', D_296, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))) | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_3', A_295) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_40, c_38, c_1044])).
% 7.58/2.47  tff(c_1054, plain, (![A_295, D_296]: (v1_funct_1(k3_tmap_1(A_295, '#skF_2', '#skF_3', D_296, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'))) | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_3', A_295) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(negUnitSimplification, [status(thm)], [c_68, c_1053])).
% 7.58/2.47  tff(c_1251, plain, (![A_295, D_296]: (v1_funct_1(k3_tmap_1(A_295, '#skF_2', '#skF_3', D_296, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))) | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_3', A_295) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1054])).
% 7.58/2.47  tff(c_2387, plain, (![D_405, A_406]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_405))) | ~m1_pre_topc(D_405, A_406) | ~m1_pre_topc('#skF_3', A_406) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406) | ~m1_pre_topc(D_405, '#skF_3') | ~m1_pre_topc(D_405, A_406) | ~m1_pre_topc('#skF_3', A_406) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(superposition, [status(thm), theory('equality')], [c_1680, c_1251])).
% 7.58/2.47  tff(c_2391, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1361, c_2387])).
% 7.58/2.47  tff(c_2415, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_1361, c_48, c_2391])).
% 7.58/2.47  tff(c_2416, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2415])).
% 7.58/2.47  tff(c_2450, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1250, c_2416])).
% 7.58/2.47  tff(c_2454, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2450])).
% 7.58/2.47  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_1046, plain, (![A_295, D_296]: (v1_funct_1(k3_tmap_1(A_295, '#skF_2', '#skF_4', D_296, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_4', A_295) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(resolution, [status(thm)], [c_42, c_1040])).
% 7.58/2.47  tff(c_1057, plain, (![A_295, D_296]: (v1_funct_1(k3_tmap_1(A_295, '#skF_2', '#skF_4', D_296, '#skF_6')) | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_4', A_295) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_46, c_44, c_1046])).
% 7.58/2.47  tff(c_1058, plain, (![A_295, D_296]: (v1_funct_1(k3_tmap_1(A_295, '#skF_2', '#skF_4', D_296, '#skF_6')) | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_4', A_295) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(negUnitSimplification, [status(thm)], [c_68, c_1057])).
% 7.58/2.47  tff(c_1475, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1453, c_1058])).
% 7.58/2.47  tff(c_1485, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_52, c_1475])).
% 7.58/2.47  tff(c_1486, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_1485])).
% 7.58/2.47  tff(c_973, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_772])).
% 7.58/2.47  tff(c_1462, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_973])).
% 7.58/2.47  tff(c_773, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_461])).
% 7.58/2.47  tff(c_1464, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_773])).
% 7.58/2.47  tff(c_1256, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_40])).
% 7.58/2.47  tff(c_1254, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_38])).
% 7.58/2.47  tff(c_1253, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_34])).
% 7.58/2.47  tff(c_14, plain, (![A_57, E_61, B_58, D_60, C_59]: (m1_subset_1(k3_tmap_1(A_57, B_58, C_59, D_60, E_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_60), u1_struct_0(B_58)))) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59), u1_struct_0(B_58)))) | ~v1_funct_2(E_61, u1_struct_0(C_59), u1_struct_0(B_58)) | ~v1_funct_1(E_61) | ~m1_pre_topc(D_60, A_57) | ~m1_pre_topc(C_59, A_57) | ~l1_pre_topc(B_58) | ~v2_pre_topc(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.58/2.47  tff(c_1698, plain, (![D_360, A_359]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_360)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_360), u1_struct_0('#skF_2')))) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')) | ~m1_pre_topc(D_360, A_359) | ~m1_pre_topc('#skF_3', A_359) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359) | ~m1_pre_topc(D_360, '#skF_3') | ~m1_pre_topc(D_360, A_359) | ~m1_pre_topc('#skF_3', A_359) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(superposition, [status(thm), theory('equality')], [c_1680, c_14])).
% 7.58/2.47  tff(c_1710, plain, (![D_360, A_359]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_360)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_360), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_360, '#skF_3') | ~m1_pre_topc(D_360, A_359) | ~m1_pre_topc('#skF_3', A_359) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1256, c_1254, c_1253, c_1698])).
% 7.58/2.47  tff(c_1861, plain, (![D_372, A_373]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_372)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_372), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_372, '#skF_3') | ~m1_pre_topc(D_372, A_373) | ~m1_pre_topc('#skF_3', A_373) | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373) | v2_struct_0(A_373))), inference(negUnitSimplification, [status(thm)], [c_68, c_1710])).
% 7.58/2.47  tff(c_1865, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1361, c_1861])).
% 7.58/2.47  tff(c_1889, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_48, c_1865])).
% 7.58/2.47  tff(c_1890, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_1889])).
% 7.58/2.47  tff(c_1933, plain, (![A_327]: (m1_subset_1(k3_tmap_1(A_327, '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', A_327) | ~m1_pre_topc('#skF_3', A_327) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(superposition, [status(thm), theory('equality')], [c_1679, c_1890])).
% 7.58/2.47  tff(c_1959, plain, (![A_327]: (m1_subset_1(k3_tmap_1(A_327, '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_5', A_327) | ~m1_pre_topc('#skF_3', A_327) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1933])).
% 7.58/2.47  tff(c_1318, plain, (![B_341, E_342, D_339, A_343, C_340]: (r2_funct_2(u1_struct_0(C_340), u1_struct_0(B_341), k3_tmap_1(A_343, B_341, D_339, C_340, k2_tmap_1(A_343, B_341, E_342, D_339)), k2_tmap_1(A_343, B_341, E_342, C_340)) | ~m1_pre_topc(C_340, D_339) | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_343), u1_struct_0(B_341)))) | ~v1_funct_2(E_342, u1_struct_0(A_343), u1_struct_0(B_341)) | ~v1_funct_1(E_342) | ~m1_pre_topc(D_339, A_343) | v2_struct_0(D_339) | ~m1_pre_topc(C_340, A_343) | v2_struct_0(C_340) | ~l1_pre_topc(B_341) | ~v2_pre_topc(B_341) | v2_struct_0(B_341) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.58/2.47  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.58/2.47  tff(c_3040, plain, (![E_447, B_445, D_448, C_449, A_446]: (k3_tmap_1(A_446, B_445, D_448, C_449, k2_tmap_1(A_446, B_445, E_447, D_448))=k2_tmap_1(A_446, B_445, E_447, C_449) | ~m1_subset_1(k2_tmap_1(A_446, B_445, E_447, C_449), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_449), u1_struct_0(B_445)))) | ~v1_funct_2(k2_tmap_1(A_446, B_445, E_447, C_449), u1_struct_0(C_449), u1_struct_0(B_445)) | ~v1_funct_1(k2_tmap_1(A_446, B_445, E_447, C_449)) | ~m1_subset_1(k3_tmap_1(A_446, B_445, D_448, C_449, k2_tmap_1(A_446, B_445, E_447, D_448)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_449), u1_struct_0(B_445)))) | ~v1_funct_2(k3_tmap_1(A_446, B_445, D_448, C_449, k2_tmap_1(A_446, B_445, E_447, D_448)), u1_struct_0(C_449), u1_struct_0(B_445)) | ~v1_funct_1(k3_tmap_1(A_446, B_445, D_448, C_449, k2_tmap_1(A_446, B_445, E_447, D_448))) | ~m1_pre_topc(C_449, D_448) | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_446), u1_struct_0(B_445)))) | ~v1_funct_2(E_447, u1_struct_0(A_446), u1_struct_0(B_445)) | ~v1_funct_1(E_447) | ~m1_pre_topc(D_448, A_446) | v2_struct_0(D_448) | ~m1_pre_topc(C_449, A_446) | v2_struct_0(C_449) | ~l1_pre_topc(B_445) | ~v2_pre_topc(B_445) | v2_struct_0(B_445) | ~l1_pre_topc(A_446) | ~v2_pre_topc(A_446) | v2_struct_0(A_446))), inference(resolution, [status(thm)], [c_1318, c_4])).
% 7.58/2.47  tff(c_3052, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5') | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1959, c_3040])).
% 7.58/2.47  tff(c_3065, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5') | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_1361, c_66, c_64, c_46, c_44, c_42, c_48, c_1486, c_1462, c_1464, c_3052])).
% 7.58/2.47  tff(c_3066, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5') | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_54, c_62, c_3065])).
% 7.58/2.47  tff(c_3085, plain, (~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')))), inference(splitLeft, [status(thm)], [c_3066])).
% 7.58/2.47  tff(c_3088, plain, (~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1689, c_3085])).
% 7.58/2.47  tff(c_3093, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_1361, c_48, c_48, c_2454, c_3088])).
% 7.58/2.47  tff(c_3095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3093])).
% 7.58/2.47  tff(c_3096, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_3066])).
% 7.58/2.47  tff(c_3104, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_3096])).
% 7.58/2.47  tff(c_3120, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1689, c_3104])).
% 7.58/2.47  tff(c_3125, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_1361, c_48, c_48, c_2793, c_3120])).
% 7.58/2.47  tff(c_3127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_3125])).
% 7.58/2.47  tff(c_3128, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_3096])).
% 7.58/2.47  tff(c_36, plain, (v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 7.58/2.47  tff(c_1226, plain, (![D_335, C_338, A_336, E_334, B_337]: (v5_pre_topc(k3_tmap_1(A_336, B_337, C_338, D_335, E_334), D_335, B_337) | ~m1_pre_topc(D_335, C_338) | ~m1_subset_1(E_334, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_338), u1_struct_0(B_337)))) | ~v5_pre_topc(E_334, C_338, B_337) | ~v1_funct_2(E_334, u1_struct_0(C_338), u1_struct_0(B_337)) | ~v1_funct_1(E_334) | ~m1_pre_topc(D_335, A_336) | v2_struct_0(D_335) | ~m1_pre_topc(C_338, A_336) | v2_struct_0(C_338) | ~l1_pre_topc(B_337) | ~v2_pre_topc(B_337) | v2_struct_0(B_337) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_242])).
% 7.58/2.47  tff(c_1232, plain, (![A_336, D_335]: (v5_pre_topc(k3_tmap_1(A_336, '#skF_2', '#skF_3', D_335, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), D_335, '#skF_2') | ~m1_pre_topc(D_335, '#skF_3') | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')) | ~m1_pre_topc(D_335, A_336) | v2_struct_0(D_335) | ~m1_pre_topc('#skF_3', A_336) | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_34, c_1226])).
% 7.58/2.47  tff(c_1242, plain, (![A_336, D_335]: (v5_pre_topc(k3_tmap_1(A_336, '#skF_2', '#skF_3', D_335, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), D_335, '#skF_2') | ~m1_pre_topc(D_335, '#skF_3') | ~m1_pre_topc(D_335, A_336) | v2_struct_0(D_335) | ~m1_pre_topc('#skF_3', A_336) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_40, c_38, c_36, c_1232])).
% 7.58/2.47  tff(c_1243, plain, (![A_336, D_335]: (v5_pre_topc(k3_tmap_1(A_336, '#skF_2', '#skF_3', D_335, k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_6')), D_335, '#skF_2') | ~m1_pre_topc(D_335, '#skF_3') | ~m1_pre_topc(D_335, A_336) | v2_struct_0(D_335) | ~m1_pre_topc('#skF_3', A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1242])).
% 7.58/2.47  tff(c_1491, plain, (![A_336, D_335]: (v5_pre_topc(k3_tmap_1(A_336, '#skF_2', '#skF_3', D_335, k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), D_335, '#skF_2') | ~m1_pre_topc(D_335, '#skF_3') | ~m1_pre_topc(D_335, A_336) | v2_struct_0(D_335) | ~m1_pre_topc('#skF_3', A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1243])).
% 7.58/2.47  tff(c_2967, plain, (![D_443, A_444]: (v5_pre_topc(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0(D_443)), D_443, '#skF_2') | ~m1_pre_topc(D_443, '#skF_3') | ~m1_pre_topc(D_443, A_444) | v2_struct_0(D_443) | ~m1_pre_topc('#skF_3', A_444) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444) | ~m1_pre_topc(D_443, '#skF_3') | ~m1_pre_topc(D_443, A_444) | ~m1_pre_topc('#skF_3', A_444) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(superposition, [status(thm), theory('equality')], [c_1680, c_1491])).
% 7.58/2.47  tff(c_2971, plain, (v5_pre_topc(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), '#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1361, c_2967])).
% 7.58/2.47  tff(c_2996, plain, (v5_pre_topc(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), '#skF_5', '#skF_2') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_1361, c_48, c_2971])).
% 7.58/2.47  tff(c_2997, plain, (v5_pre_topc(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3'), u1_struct_0('#skF_5')), '#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_2996])).
% 7.58/2.47  tff(c_3032, plain, (![A_327]: (v5_pre_topc(k3_tmap_1(A_327, '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), '#skF_5', '#skF_2') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', A_327) | ~m1_pre_topc('#skF_3', A_327) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(superposition, [status(thm), theory('equality')], [c_1679, c_2997])).
% 7.58/2.47  tff(c_3037, plain, (![A_327]: (v5_pre_topc(k3_tmap_1(A_327, '#skF_2', '#skF_3', '#skF_5', k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_3')), '#skF_5', '#skF_2') | ~m1_pre_topc('#skF_5', A_327) | ~m1_pre_topc('#skF_3', A_327) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3032])).
% 7.58/2.47  tff(c_3135, plain, (v5_pre_topc(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), '#skF_5', '#skF_2') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3128, c_3037])).
% 7.58/2.47  tff(c_3179, plain, (v5_pre_topc(k2_tmap_1('#skF_4', '#skF_2', '#skF_6', '#skF_5'), '#skF_5', '#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_97, c_50, c_1361, c_3135])).
% 7.58/2.47  tff(c_3181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1463, c_3179])).
% 7.58/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.47  
% 7.58/2.47  Inference rules
% 7.58/2.47  ----------------------
% 7.58/2.47  #Ref     : 0
% 7.58/2.47  #Sup     : 590
% 7.58/2.47  #Fact    : 0
% 7.58/2.47  #Define  : 0
% 7.58/2.47  #Split   : 18
% 7.58/2.47  #Chain   : 0
% 7.58/2.47  #Close   : 0
% 7.58/2.47  
% 7.58/2.47  Ordering : KBO
% 7.58/2.47  
% 7.58/2.47  Simplification rules
% 7.58/2.47  ----------------------
% 7.58/2.47  #Subsume      : 226
% 7.58/2.47  #Demod        : 1663
% 7.58/2.47  #Tautology    : 160
% 7.58/2.47  #SimpNegUnit  : 222
% 7.58/2.47  #BackRed      : 19
% 7.58/2.47  
% 7.58/2.47  #Partial instantiations: 0
% 7.58/2.47  #Strategies tried      : 1
% 7.58/2.47  
% 7.58/2.47  Timing (in seconds)
% 7.58/2.47  ----------------------
% 7.58/2.48  Preprocessing        : 0.43
% 7.58/2.48  Parsing              : 0.23
% 7.58/2.48  CNF conversion       : 0.06
% 7.58/2.48  Main loop            : 1.24
% 7.58/2.48  Inferencing          : 0.39
% 7.58/2.48  Reduction            : 0.45
% 7.58/2.48  Demodulation         : 0.32
% 7.58/2.48  BG Simplification    : 0.05
% 7.58/2.48  Subsumption          : 0.30
% 7.58/2.48  Abstraction          : 0.07
% 7.58/2.48  MUC search           : 0.00
% 7.58/2.48  Cooper               : 0.00
% 7.58/2.48  Total                : 1.74
% 7.58/2.48  Index Insertion      : 0.00
% 7.58/2.48  Index Deletion       : 0.00
% 7.58/2.48  Index Matching       : 0.00
% 7.58/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
