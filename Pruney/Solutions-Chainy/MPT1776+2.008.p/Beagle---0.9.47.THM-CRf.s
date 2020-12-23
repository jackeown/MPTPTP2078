%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:30 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 873 expanded)
%              Number of leaves         :   36 ( 353 expanded)
%              Depth                    :   18
%              Number of atoms          :  492 (7696 expanded)
%              Number of equality atoms :   41 ( 437 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_290,negated_conjecture,(
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

tff(f_100,axiom,(
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

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
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

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_124,axiom,(
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

tff(f_237,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( ( v1_tsep_1(C,D)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,B,E,F)
                                  <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_175,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_26,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_73,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_64])).

tff(c_172,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_40,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_332,plain,(
    ! [A_416,D_415,C_419,B_417,E_418] :
      ( k3_tmap_1(A_416,B_417,C_419,D_415,E_418) = k2_partfun1(u1_struct_0(C_419),u1_struct_0(B_417),E_418,u1_struct_0(D_415))
      | ~ m1_pre_topc(D_415,C_419)
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_419),u1_struct_0(B_417))))
      | ~ v1_funct_2(E_418,u1_struct_0(C_419),u1_struct_0(B_417))
      | ~ v1_funct_1(E_418)
      | ~ m1_pre_topc(D_415,A_416)
      | ~ m1_pre_topc(C_419,A_416)
      | ~ l1_pre_topc(B_417)
      | ~ v2_pre_topc(B_417)
      | v2_struct_0(B_417)
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_334,plain,(
    ! [A_416,D_415] :
      ( k3_tmap_1(A_416,'#skF_1','#skF_4',D_415,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_415))
      | ~ m1_pre_topc(D_415,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_415,A_416)
      | ~ m1_pre_topc('#skF_4',A_416)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416) ) ),
    inference(resolution,[status(thm)],[c_38,c_332])).

tff(c_337,plain,(
    ! [A_416,D_415] :
      ( k3_tmap_1(A_416,'#skF_1','#skF_4',D_415,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_415))
      | ~ m1_pre_topc(D_415,'#skF_4')
      | ~ m1_pre_topc(D_415,A_416)
      | ~ m1_pre_topc('#skF_4',A_416)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_42,c_40,c_334])).

tff(c_339,plain,(
    ! [A_420,D_421] :
      ( k3_tmap_1(A_420,'#skF_1','#skF_4',D_421,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_421))
      | ~ m1_pre_topc(D_421,'#skF_4')
      | ~ m1_pre_topc(D_421,A_420)
      | ~ m1_pre_topc('#skF_4',A_420)
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420)
      | v2_struct_0(A_420) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_337])).

tff(c_351,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_339])).

tff(c_370,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44,c_32,c_351])).

tff(c_371,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_370])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_103,plain,(
    ! [B_384,A_385] :
      ( v2_pre_topc(B_384)
      | ~ m1_pre_topc(B_384,A_385)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_112,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_122,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_112])).

tff(c_80,plain,(
    ! [B_382,A_383] :
      ( l1_pre_topc(B_382)
      | ~ m1_pre_topc(B_382,A_383)
      | ~ l1_pre_topc(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_80])).

tff(c_97,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_89])).

tff(c_284,plain,(
    ! [A_407,B_408,C_409,D_410] :
      ( k2_partfun1(u1_struct_0(A_407),u1_struct_0(B_408),C_409,u1_struct_0(D_410)) = k2_tmap_1(A_407,B_408,C_409,D_410)
      | ~ m1_pre_topc(D_410,A_407)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_407),u1_struct_0(B_408))))
      | ~ v1_funct_2(C_409,u1_struct_0(A_407),u1_struct_0(B_408))
      | ~ v1_funct_1(C_409)
      | ~ l1_pre_topc(B_408)
      | ~ v2_pre_topc(B_408)
      | v2_struct_0(B_408)
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407)
      | v2_struct_0(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_286,plain,(
    ! [D_410] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_410)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_410)
      | ~ m1_pre_topc(D_410,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_284])).

tff(c_289,plain,(
    ! [D_410] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_410)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_410)
      | ~ m1_pre_topc(D_410,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_97,c_60,c_58,c_42,c_40,c_286])).

tff(c_290,plain,(
    ! [D_410] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_410)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_410)
      | ~ m1_pre_topc(D_410,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_62,c_289])).

tff(c_375,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_290])).

tff(c_382,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_375])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_70])).

tff(c_173,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_72])).

tff(c_387,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_173])).

tff(c_14,plain,(
    ! [A_60] :
      ( m1_pre_topc(A_60,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_349,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_339])).

tff(c_366,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44,c_349])).

tff(c_367,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_366])).

tff(c_418,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_421,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_421])).

tff(c_427,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_386,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_371])).

tff(c_347,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_339])).

tff(c_362,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_97,c_32,c_347])).

tff(c_363,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_362])).

tff(c_416,plain,
    ( k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_363])).

tff(c_417,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_417])).

tff(c_463,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_36,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_290])).

tff(c_16,plain,(
    ! [B_63,A_61] :
      ( r1_tarski(u1_struct_0(B_63),u1_struct_0(A_61))
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_174,plain,(
    ! [B_394,C_395,A_396] :
      ( v1_tsep_1(B_394,C_395)
      | ~ r1_tarski(u1_struct_0(B_394),u1_struct_0(C_395))
      | ~ m1_pre_topc(C_395,A_396)
      | v2_struct_0(C_395)
      | ~ m1_pre_topc(B_394,A_396)
      | ~ v1_tsep_1(B_394,A_396)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_206,plain,(
    ! [B_402,A_403,A_404] :
      ( v1_tsep_1(B_402,A_403)
      | ~ m1_pre_topc(A_403,A_404)
      | v2_struct_0(A_403)
      | ~ m1_pre_topc(B_402,A_404)
      | ~ v1_tsep_1(B_402,A_404)
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404)
      | ~ m1_pre_topc(B_402,A_403)
      | ~ l1_pre_topc(A_403) ) ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_214,plain,(
    ! [B_402] :
      ( v1_tsep_1(B_402,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_402,'#skF_2')
      | ~ v1_tsep_1(B_402,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_402,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_206])).

tff(c_228,plain,(
    ! [B_402] :
      ( v1_tsep_1(B_402,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_402,'#skF_2')
      | ~ v1_tsep_1(B_402,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_402,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_54,c_52,c_214])).

tff(c_291,plain,(
    ! [B_411] :
      ( v1_tsep_1(B_411,'#skF_4')
      | ~ m1_pre_topc(B_411,'#skF_2')
      | ~ v1_tsep_1(B_411,'#skF_2')
      | ~ m1_pre_topc(B_411,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46,c_228])).

tff(c_294,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_291])).

tff(c_297,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_48,c_294])).

tff(c_462,plain,(
    k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_500,plain,(
    ! [C_427,E_431,B_428,G_432,A_429,D_430] :
      ( r1_tmap_1(D_430,B_428,E_431,G_432)
      | ~ r1_tmap_1(C_427,B_428,k3_tmap_1(A_429,B_428,D_430,C_427,E_431),G_432)
      | ~ m1_subset_1(G_432,u1_struct_0(C_427))
      | ~ m1_subset_1(G_432,u1_struct_0(D_430))
      | ~ m1_pre_topc(C_427,D_430)
      | ~ v1_tsep_1(C_427,D_430)
      | ~ m1_subset_1(E_431,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_430),u1_struct_0(B_428))))
      | ~ v1_funct_2(E_431,u1_struct_0(D_430),u1_struct_0(B_428))
      | ~ v1_funct_1(E_431)
      | ~ m1_pre_topc(D_430,A_429)
      | v2_struct_0(D_430)
      | ~ m1_pre_topc(C_427,A_429)
      | v2_struct_0(C_427)
      | ~ l1_pre_topc(B_428)
      | ~ v2_pre_topc(B_428)
      | v2_struct_0(B_428)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_502,plain,(
    ! [G_432] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',G_432)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_432)
      | ~ m1_subset_1(G_432,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_432,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ v1_tsep_1('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_500])).

tff(c_506,plain,(
    ! [G_432] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',G_432)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_432)
      | ~ m1_subset_1(G_432,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_432,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_97,c_60,c_58,c_32,c_463,c_42,c_40,c_38,c_297,c_32,c_502])).

tff(c_590,plain,(
    ! [G_439] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',G_439)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),G_439)
      | ~ m1_subset_1(G_439,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_439,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_62,c_50,c_506])).

tff(c_593,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_387,c_590])).

tff(c_596,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_74,c_593])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_596])).

tff(c_600,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_822,plain,(
    ! [A_472,F_468,D_469,B_471,C_470] :
      ( r1_tmap_1(D_469,A_472,k2_tmap_1(B_471,A_472,C_470,D_469),F_468)
      | ~ r1_tmap_1(B_471,A_472,C_470,F_468)
      | ~ m1_subset_1(F_468,u1_struct_0(D_469))
      | ~ m1_subset_1(F_468,u1_struct_0(B_471))
      | ~ m1_pre_topc(D_469,B_471)
      | v2_struct_0(D_469)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_471),u1_struct_0(A_472))))
      | ~ v1_funct_2(C_470,u1_struct_0(B_471),u1_struct_0(A_472))
      | ~ v1_funct_1(C_470)
      | ~ l1_pre_topc(B_471)
      | ~ v2_pre_topc(B_471)
      | v2_struct_0(B_471)
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472)
      | v2_struct_0(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_824,plain,(
    ! [D_469,F_468] :
      ( r1_tmap_1(D_469,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_469),F_468)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_468)
      | ~ m1_subset_1(F_468,u1_struct_0(D_469))
      | ~ m1_subset_1(F_468,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_469,'#skF_4')
      | v2_struct_0(D_469)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_822])).

tff(c_827,plain,(
    ! [D_469,F_468] :
      ( r1_tmap_1(D_469,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_469),F_468)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_468)
      | ~ m1_subset_1(F_468,u1_struct_0(D_469))
      | ~ m1_subset_1(F_468,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_469,'#skF_4')
      | v2_struct_0(D_469)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_122,c_97,c_42,c_40,c_824])).

tff(c_1079,plain,(
    ! [D_489,F_490] :
      ( r1_tmap_1(D_489,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_489),F_490)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_490)
      | ~ m1_subset_1(F_490,u1_struct_0(D_489))
      | ~ m1_subset_1(F_490,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_489,'#skF_4')
      | v2_struct_0(D_489) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46,c_827])).

tff(c_761,plain,(
    ! [C_465,E_464,A_462,D_461,B_463] :
      ( k3_tmap_1(A_462,B_463,C_465,D_461,E_464) = k2_partfun1(u1_struct_0(C_465),u1_struct_0(B_463),E_464,u1_struct_0(D_461))
      | ~ m1_pre_topc(D_461,C_465)
      | ~ m1_subset_1(E_464,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_465),u1_struct_0(B_463))))
      | ~ v1_funct_2(E_464,u1_struct_0(C_465),u1_struct_0(B_463))
      | ~ v1_funct_1(E_464)
      | ~ m1_pre_topc(D_461,A_462)
      | ~ m1_pre_topc(C_465,A_462)
      | ~ l1_pre_topc(B_463)
      | ~ v2_pre_topc(B_463)
      | v2_struct_0(B_463)
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_763,plain,(
    ! [A_462,D_461] :
      ( k3_tmap_1(A_462,'#skF_1','#skF_4',D_461,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_461))
      | ~ m1_pre_topc(D_461,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_461,A_462)
      | ~ m1_pre_topc('#skF_4',A_462)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(resolution,[status(thm)],[c_38,c_761])).

tff(c_766,plain,(
    ! [A_462,D_461] :
      ( k3_tmap_1(A_462,'#skF_1','#skF_4',D_461,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_461))
      | ~ m1_pre_topc(D_461,'#skF_4')
      | ~ m1_pre_topc(D_461,A_462)
      | ~ m1_pre_topc('#skF_4',A_462)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_42,c_40,c_763])).

tff(c_768,plain,(
    ! [A_466,D_467] :
      ( k3_tmap_1(A_466,'#skF_1','#skF_4',D_467,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_467))
      | ~ m1_pre_topc(D_467,'#skF_4')
      | ~ m1_pre_topc(D_467,A_466)
      | ~ m1_pre_topc('#skF_4',A_466)
      | ~ l1_pre_topc(A_466)
      | ~ v2_pre_topc(A_466)
      | v2_struct_0(A_466) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_766])).

tff(c_780,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_768])).

tff(c_799,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44,c_32,c_780])).

tff(c_800,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_799])).

tff(c_694,plain,(
    ! [A_454,B_455,C_456,D_457] :
      ( k2_partfun1(u1_struct_0(A_454),u1_struct_0(B_455),C_456,u1_struct_0(D_457)) = k2_tmap_1(A_454,B_455,C_456,D_457)
      | ~ m1_pre_topc(D_457,A_454)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_454),u1_struct_0(B_455))))
      | ~ v1_funct_2(C_456,u1_struct_0(A_454),u1_struct_0(B_455))
      | ~ v1_funct_1(C_456)
      | ~ l1_pre_topc(B_455)
      | ~ v2_pre_topc(B_455)
      | v2_struct_0(B_455)
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_696,plain,(
    ! [D_457] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_457)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_457)
      | ~ m1_pre_topc(D_457,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_694])).

tff(c_699,plain,(
    ! [D_457] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_457)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_457)
      | ~ m1_pre_topc(D_457,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_97,c_60,c_58,c_42,c_40,c_696])).

tff(c_700,plain,(
    ! [D_457] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_457)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_457)
      | ~ m1_pre_topc(D_457,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_62,c_699])).

tff(c_804,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_700])).

tff(c_811,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_804])).

tff(c_599,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_816,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_599])).

tff(c_1086,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1079,c_816])).

tff(c_1093,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_74,c_600,c_1086])).

tff(c_1095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1093])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:17:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.59  
% 3.86/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.59  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.86/1.59  
% 3.86/1.59  %Foreground sorts:
% 3.86/1.59  
% 3.86/1.59  
% 3.86/1.59  %Background operators:
% 3.86/1.59  
% 3.86/1.59  
% 3.86/1.59  %Foreground operators:
% 3.86/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.86/1.59  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.86/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.59  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.86/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.86/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.86/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.86/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.86/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.86/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.59  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.86/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.86/1.59  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.86/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.86/1.59  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.86/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.86/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.59  
% 3.86/1.61  tff(f_290, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.86/1.61  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.86/1.61  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.86/1.61  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.86/1.61  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.86/1.61  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.86/1.61  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.86/1.61  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 3.86/1.61  tff(f_237, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.86/1.61  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.86/1.61  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_26, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_28, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_74, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 3.86/1.61  tff(c_64, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_73, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_64])).
% 3.86/1.61  tff(c_172, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_73])).
% 3.86/1.61  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_40, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_332, plain, (![A_416, D_415, C_419, B_417, E_418]: (k3_tmap_1(A_416, B_417, C_419, D_415, E_418)=k2_partfun1(u1_struct_0(C_419), u1_struct_0(B_417), E_418, u1_struct_0(D_415)) | ~m1_pre_topc(D_415, C_419) | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_419), u1_struct_0(B_417)))) | ~v1_funct_2(E_418, u1_struct_0(C_419), u1_struct_0(B_417)) | ~v1_funct_1(E_418) | ~m1_pre_topc(D_415, A_416) | ~m1_pre_topc(C_419, A_416) | ~l1_pre_topc(B_417) | ~v2_pre_topc(B_417) | v2_struct_0(B_417) | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | v2_struct_0(A_416))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.86/1.61  tff(c_334, plain, (![A_416, D_415]: (k3_tmap_1(A_416, '#skF_1', '#skF_4', D_415, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_415)) | ~m1_pre_topc(D_415, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_415, A_416) | ~m1_pre_topc('#skF_4', A_416) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | v2_struct_0(A_416))), inference(resolution, [status(thm)], [c_38, c_332])).
% 3.86/1.61  tff(c_337, plain, (![A_416, D_415]: (k3_tmap_1(A_416, '#skF_1', '#skF_4', D_415, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_415)) | ~m1_pre_topc(D_415, '#skF_4') | ~m1_pre_topc(D_415, A_416) | ~m1_pre_topc('#skF_4', A_416) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | v2_struct_0(A_416))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_42, c_40, c_334])).
% 3.86/1.61  tff(c_339, plain, (![A_420, D_421]: (k3_tmap_1(A_420, '#skF_1', '#skF_4', D_421, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_421)) | ~m1_pre_topc(D_421, '#skF_4') | ~m1_pre_topc(D_421, A_420) | ~m1_pre_topc('#skF_4', A_420) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420) | v2_struct_0(A_420))), inference(negUnitSimplification, [status(thm)], [c_62, c_337])).
% 3.86/1.61  tff(c_351, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_339])).
% 3.86/1.61  tff(c_370, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44, c_32, c_351])).
% 3.86/1.61  tff(c_371, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_370])).
% 3.86/1.61  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_103, plain, (![B_384, A_385]: (v2_pre_topc(B_384) | ~m1_pre_topc(B_384, A_385) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.86/1.61  tff(c_112, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_103])).
% 3.86/1.61  tff(c_122, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_112])).
% 3.86/1.61  tff(c_80, plain, (![B_382, A_383]: (l1_pre_topc(B_382) | ~m1_pre_topc(B_382, A_383) | ~l1_pre_topc(A_383))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.86/1.61  tff(c_89, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_80])).
% 3.86/1.61  tff(c_97, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_89])).
% 3.86/1.61  tff(c_284, plain, (![A_407, B_408, C_409, D_410]: (k2_partfun1(u1_struct_0(A_407), u1_struct_0(B_408), C_409, u1_struct_0(D_410))=k2_tmap_1(A_407, B_408, C_409, D_410) | ~m1_pre_topc(D_410, A_407) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_407), u1_struct_0(B_408)))) | ~v1_funct_2(C_409, u1_struct_0(A_407), u1_struct_0(B_408)) | ~v1_funct_1(C_409) | ~l1_pre_topc(B_408) | ~v2_pre_topc(B_408) | v2_struct_0(B_408) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407) | v2_struct_0(A_407))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.86/1.61  tff(c_286, plain, (![D_410]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_410))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_410) | ~m1_pre_topc(D_410, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_284])).
% 3.86/1.61  tff(c_289, plain, (![D_410]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_410))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_410) | ~m1_pre_topc(D_410, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_97, c_60, c_58, c_42, c_40, c_286])).
% 3.86/1.61  tff(c_290, plain, (![D_410]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_410))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_410) | ~m1_pre_topc(D_410, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_62, c_289])).
% 3.86/1.61  tff(c_375, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_371, c_290])).
% 3.86/1.61  tff(c_382, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_375])).
% 3.86/1.61  tff(c_70, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_72, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_70])).
% 3.86/1.61  tff(c_173, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_172, c_72])).
% 3.86/1.61  tff(c_387, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_173])).
% 3.86/1.61  tff(c_14, plain, (![A_60]: (m1_pre_topc(A_60, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.86/1.61  tff(c_349, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_339])).
% 3.86/1.61  tff(c_366, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44, c_349])).
% 3.86/1.61  tff(c_367, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_366])).
% 3.86/1.61  tff(c_418, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_367])).
% 3.86/1.61  tff(c_421, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_418])).
% 3.86/1.61  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_421])).
% 3.86/1.61  tff(c_427, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_367])).
% 3.86/1.61  tff(c_386, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_371])).
% 3.86/1.61  tff(c_347, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_339])).
% 3.86/1.61  tff(c_362, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_97, c_32, c_347])).
% 3.86/1.61  tff(c_363, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_362])).
% 3.86/1.61  tff(c_416, plain, (k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_363])).
% 3.86/1.61  tff(c_417, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_416])).
% 3.86/1.61  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_427, c_417])).
% 3.86/1.61  tff(c_463, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_416])).
% 3.86/1.61  tff(c_36, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_290])).
% 3.86/1.61  tff(c_16, plain, (![B_63, A_61]: (r1_tarski(u1_struct_0(B_63), u1_struct_0(A_61)) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.86/1.61  tff(c_174, plain, (![B_394, C_395, A_396]: (v1_tsep_1(B_394, C_395) | ~r1_tarski(u1_struct_0(B_394), u1_struct_0(C_395)) | ~m1_pre_topc(C_395, A_396) | v2_struct_0(C_395) | ~m1_pre_topc(B_394, A_396) | ~v1_tsep_1(B_394, A_396) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.86/1.61  tff(c_206, plain, (![B_402, A_403, A_404]: (v1_tsep_1(B_402, A_403) | ~m1_pre_topc(A_403, A_404) | v2_struct_0(A_403) | ~m1_pre_topc(B_402, A_404) | ~v1_tsep_1(B_402, A_404) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404) | ~m1_pre_topc(B_402, A_403) | ~l1_pre_topc(A_403))), inference(resolution, [status(thm)], [c_16, c_174])).
% 3.86/1.61  tff(c_214, plain, (![B_402]: (v1_tsep_1(B_402, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_402, '#skF_2') | ~v1_tsep_1(B_402, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_402, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_206])).
% 3.86/1.61  tff(c_228, plain, (![B_402]: (v1_tsep_1(B_402, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_402, '#skF_2') | ~v1_tsep_1(B_402, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_402, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_54, c_52, c_214])).
% 3.86/1.61  tff(c_291, plain, (![B_411]: (v1_tsep_1(B_411, '#skF_4') | ~m1_pre_topc(B_411, '#skF_2') | ~v1_tsep_1(B_411, '#skF_2') | ~m1_pre_topc(B_411, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_46, c_228])).
% 3.86/1.61  tff(c_294, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_291])).
% 3.86/1.61  tff(c_297, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_48, c_294])).
% 3.86/1.61  tff(c_462, plain, (k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_416])).
% 3.86/1.61  tff(c_500, plain, (![C_427, E_431, B_428, G_432, A_429, D_430]: (r1_tmap_1(D_430, B_428, E_431, G_432) | ~r1_tmap_1(C_427, B_428, k3_tmap_1(A_429, B_428, D_430, C_427, E_431), G_432) | ~m1_subset_1(G_432, u1_struct_0(C_427)) | ~m1_subset_1(G_432, u1_struct_0(D_430)) | ~m1_pre_topc(C_427, D_430) | ~v1_tsep_1(C_427, D_430) | ~m1_subset_1(E_431, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_430), u1_struct_0(B_428)))) | ~v1_funct_2(E_431, u1_struct_0(D_430), u1_struct_0(B_428)) | ~v1_funct_1(E_431) | ~m1_pre_topc(D_430, A_429) | v2_struct_0(D_430) | ~m1_pre_topc(C_427, A_429) | v2_struct_0(C_427) | ~l1_pre_topc(B_428) | ~v2_pre_topc(B_428) | v2_struct_0(B_428) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(cnfTransformation, [status(thm)], [f_237])).
% 3.86/1.61  tff(c_502, plain, (![G_432]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_432) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_432) | ~m1_subset_1(G_432, u1_struct_0('#skF_3')) | ~m1_subset_1(G_432, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_462, c_500])).
% 3.86/1.61  tff(c_506, plain, (![G_432]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_432) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_432) | ~m1_subset_1(G_432, u1_struct_0('#skF_3')) | ~m1_subset_1(G_432, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_97, c_60, c_58, c_32, c_463, c_42, c_40, c_38, c_297, c_32, c_502])).
% 3.86/1.61  tff(c_590, plain, (![G_439]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_439) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), G_439) | ~m1_subset_1(G_439, u1_struct_0('#skF_3')) | ~m1_subset_1(G_439, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_46, c_62, c_50, c_506])).
% 3.86/1.61  tff(c_593, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_387, c_590])).
% 3.86/1.61  tff(c_596, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_74, c_593])).
% 3.86/1.61  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_596])).
% 3.86/1.61  tff(c_600, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_73])).
% 3.86/1.61  tff(c_822, plain, (![A_472, F_468, D_469, B_471, C_470]: (r1_tmap_1(D_469, A_472, k2_tmap_1(B_471, A_472, C_470, D_469), F_468) | ~r1_tmap_1(B_471, A_472, C_470, F_468) | ~m1_subset_1(F_468, u1_struct_0(D_469)) | ~m1_subset_1(F_468, u1_struct_0(B_471)) | ~m1_pre_topc(D_469, B_471) | v2_struct_0(D_469) | ~m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_471), u1_struct_0(A_472)))) | ~v1_funct_2(C_470, u1_struct_0(B_471), u1_struct_0(A_472)) | ~v1_funct_1(C_470) | ~l1_pre_topc(B_471) | ~v2_pre_topc(B_471) | v2_struct_0(B_471) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472) | v2_struct_0(A_472))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.86/1.61  tff(c_824, plain, (![D_469, F_468]: (r1_tmap_1(D_469, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_469), F_468) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_468) | ~m1_subset_1(F_468, u1_struct_0(D_469)) | ~m1_subset_1(F_468, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_469, '#skF_4') | v2_struct_0(D_469) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_822])).
% 3.86/1.61  tff(c_827, plain, (![D_469, F_468]: (r1_tmap_1(D_469, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_469), F_468) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_468) | ~m1_subset_1(F_468, u1_struct_0(D_469)) | ~m1_subset_1(F_468, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_469, '#skF_4') | v2_struct_0(D_469) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_122, c_97, c_42, c_40, c_824])).
% 3.86/1.61  tff(c_1079, plain, (![D_489, F_490]: (r1_tmap_1(D_489, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_489), F_490) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_490) | ~m1_subset_1(F_490, u1_struct_0(D_489)) | ~m1_subset_1(F_490, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_489, '#skF_4') | v2_struct_0(D_489))), inference(negUnitSimplification, [status(thm)], [c_62, c_46, c_827])).
% 3.86/1.61  tff(c_761, plain, (![C_465, E_464, A_462, D_461, B_463]: (k3_tmap_1(A_462, B_463, C_465, D_461, E_464)=k2_partfun1(u1_struct_0(C_465), u1_struct_0(B_463), E_464, u1_struct_0(D_461)) | ~m1_pre_topc(D_461, C_465) | ~m1_subset_1(E_464, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_465), u1_struct_0(B_463)))) | ~v1_funct_2(E_464, u1_struct_0(C_465), u1_struct_0(B_463)) | ~v1_funct_1(E_464) | ~m1_pre_topc(D_461, A_462) | ~m1_pre_topc(C_465, A_462) | ~l1_pre_topc(B_463) | ~v2_pre_topc(B_463) | v2_struct_0(B_463) | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.86/1.61  tff(c_763, plain, (![A_462, D_461]: (k3_tmap_1(A_462, '#skF_1', '#skF_4', D_461, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_461)) | ~m1_pre_topc(D_461, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_461, A_462) | ~m1_pre_topc('#skF_4', A_462) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(resolution, [status(thm)], [c_38, c_761])).
% 3.86/1.61  tff(c_766, plain, (![A_462, D_461]: (k3_tmap_1(A_462, '#skF_1', '#skF_4', D_461, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_461)) | ~m1_pre_topc(D_461, '#skF_4') | ~m1_pre_topc(D_461, A_462) | ~m1_pre_topc('#skF_4', A_462) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_42, c_40, c_763])).
% 3.86/1.61  tff(c_768, plain, (![A_466, D_467]: (k3_tmap_1(A_466, '#skF_1', '#skF_4', D_467, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_467)) | ~m1_pre_topc(D_467, '#skF_4') | ~m1_pre_topc(D_467, A_466) | ~m1_pre_topc('#skF_4', A_466) | ~l1_pre_topc(A_466) | ~v2_pre_topc(A_466) | v2_struct_0(A_466))), inference(negUnitSimplification, [status(thm)], [c_62, c_766])).
% 3.86/1.61  tff(c_780, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_768])).
% 3.86/1.61  tff(c_799, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44, c_32, c_780])).
% 3.86/1.61  tff(c_800, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_799])).
% 3.86/1.61  tff(c_694, plain, (![A_454, B_455, C_456, D_457]: (k2_partfun1(u1_struct_0(A_454), u1_struct_0(B_455), C_456, u1_struct_0(D_457))=k2_tmap_1(A_454, B_455, C_456, D_457) | ~m1_pre_topc(D_457, A_454) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_454), u1_struct_0(B_455)))) | ~v1_funct_2(C_456, u1_struct_0(A_454), u1_struct_0(B_455)) | ~v1_funct_1(C_456) | ~l1_pre_topc(B_455) | ~v2_pre_topc(B_455) | v2_struct_0(B_455) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.86/1.61  tff(c_696, plain, (![D_457]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_457))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_457) | ~m1_pre_topc(D_457, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_694])).
% 3.86/1.61  tff(c_699, plain, (![D_457]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_457))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_457) | ~m1_pre_topc(D_457, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_97, c_60, c_58, c_42, c_40, c_696])).
% 3.86/1.61  tff(c_700, plain, (![D_457]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_457))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_457) | ~m1_pre_topc(D_457, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_62, c_699])).
% 3.86/1.61  tff(c_804, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_800, c_700])).
% 3.86/1.61  tff(c_811, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_804])).
% 3.86/1.61  tff(c_599, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_73])).
% 3.86/1.61  tff(c_816, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_599])).
% 3.86/1.61  tff(c_1086, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1079, c_816])).
% 3.86/1.61  tff(c_1093, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_74, c_600, c_1086])).
% 3.86/1.61  tff(c_1095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1093])).
% 3.86/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.61  
% 3.86/1.61  Inference rules
% 3.86/1.61  ----------------------
% 3.86/1.61  #Ref     : 0
% 3.86/1.61  #Sup     : 195
% 3.86/1.61  #Fact    : 0
% 3.86/1.61  #Define  : 0
% 3.86/1.61  #Split   : 11
% 3.86/1.61  #Chain   : 0
% 3.86/1.61  #Close   : 0
% 3.86/1.61  
% 3.86/1.61  Ordering : KBO
% 3.86/1.61  
% 3.86/1.61  Simplification rules
% 3.86/1.61  ----------------------
% 3.86/1.61  #Subsume      : 14
% 3.86/1.61  #Demod        : 435
% 3.86/1.61  #Tautology    : 121
% 3.86/1.61  #SimpNegUnit  : 65
% 3.86/1.61  #BackRed      : 7
% 3.86/1.61  
% 3.86/1.61  #Partial instantiations: 0
% 3.86/1.61  #Strategies tried      : 1
% 3.86/1.61  
% 3.86/1.61  Timing (in seconds)
% 3.86/1.61  ----------------------
% 3.86/1.62  Preprocessing        : 0.40
% 3.86/1.62  Parsing              : 0.21
% 3.86/1.62  CNF conversion       : 0.06
% 3.86/1.62  Main loop            : 0.43
% 3.86/1.62  Inferencing          : 0.15
% 3.86/1.62  Reduction            : 0.15
% 3.86/1.62  Demodulation         : 0.11
% 3.86/1.62  BG Simplification    : 0.03
% 3.86/1.62  Subsumption          : 0.08
% 3.86/1.62  Abstraction          : 0.02
% 3.86/1.62  MUC search           : 0.00
% 3.86/1.62  Cooper               : 0.00
% 3.86/1.62  Total                : 0.89
% 3.86/1.62  Index Insertion      : 0.00
% 3.86/1.62  Index Deletion       : 0.00
% 3.86/1.62  Index Matching       : 0.00
% 3.86/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
