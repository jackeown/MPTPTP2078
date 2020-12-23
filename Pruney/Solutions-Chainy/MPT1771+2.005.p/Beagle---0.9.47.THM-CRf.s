%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:21 EST 2020

% Result     : Theorem 14.22s
% Output     : CNFRefutation 14.22s
% Verified   : 
% Statistics : Number of formulae       :  171 (11142 expanded)
%              Number of leaves         :   33 (4414 expanded)
%              Depth                    :   34
%              Number of atoms          :  884 (102316 expanded)
%              Number of equality atoms :   37 (6341 expanded)
%              Maximal formula depth    :   34 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_289,negated_conjecture,(
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
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(D,B,k2_tmap_1(A,B,E,D),F) )
                                   => r1_tmap_1(C,B,k2_tmap_1(A,B,E,C),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tmap_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_130,axiom,(
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

tff(f_180,axiom,(
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
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(D,C)
                          & m1_pre_topc(E,D) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

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

tff(f_240,axiom,(
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
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_28,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_61,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_26,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_16,plain,(
    ! [A_56] :
      ( m1_pre_topc(A_56,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_203,plain,(
    ! [B_419,C_420,A_418,D_417,E_416] :
      ( k3_tmap_1(A_418,B_419,C_420,D_417,E_416) = k2_partfun1(u1_struct_0(C_420),u1_struct_0(B_419),E_416,u1_struct_0(D_417))
      | ~ m1_pre_topc(D_417,C_420)
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_420),u1_struct_0(B_419))))
      | ~ v1_funct_2(E_416,u1_struct_0(C_420),u1_struct_0(B_419))
      | ~ v1_funct_1(E_416)
      | ~ m1_pre_topc(D_417,A_418)
      | ~ m1_pre_topc(C_420,A_418)
      | ~ l1_pre_topc(B_419)
      | ~ v2_pre_topc(B_419)
      | v2_struct_0(B_419)
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_207,plain,(
    ! [A_418,D_417] :
      ( k3_tmap_1(A_418,'#skF_2','#skF_1',D_417,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_417))
      | ~ m1_pre_topc(D_417,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_417,A_418)
      | ~ m1_pre_topc('#skF_1',A_418)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(resolution,[status(thm)],[c_36,c_203])).

tff(c_211,plain,(
    ! [A_418,D_417] :
      ( k3_tmap_1(A_418,'#skF_2','#skF_1',D_417,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_417))
      | ~ m1_pre_topc(D_417,'#skF_1')
      | ~ m1_pre_topc(D_417,A_418)
      | ~ m1_pre_topc('#skF_1',A_418)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_207])).

tff(c_213,plain,(
    ! [A_421,D_422] :
      ( k3_tmap_1(A_421,'#skF_2','#skF_1',D_422,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_422))
      | ~ m1_pre_topc(D_422,'#skF_1')
      | ~ m1_pre_topc(D_422,A_421)
      | ~ m1_pre_topc('#skF_1',A_421)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_211])).

tff(c_221,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_213])).

tff(c_235,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_221])).

tff(c_236,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_235])).

tff(c_245,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_249,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_245])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_249])).

tff(c_255,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_254,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_166,plain,(
    ! [A_399,B_400,C_401,D_402] :
      ( k2_partfun1(u1_struct_0(A_399),u1_struct_0(B_400),C_401,u1_struct_0(D_402)) = k2_tmap_1(A_399,B_400,C_401,D_402)
      | ~ m1_pre_topc(D_402,A_399)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_399),u1_struct_0(B_400))))
      | ~ v1_funct_2(C_401,u1_struct_0(A_399),u1_struct_0(B_400))
      | ~ v1_funct_1(C_401)
      | ~ l1_pre_topc(B_400)
      | ~ v2_pre_topc(B_400)
      | v2_struct_0(B_400)
      | ~ l1_pre_topc(A_399)
      | ~ v2_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_168,plain,(
    ! [D_402] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_402)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_402)
      | ~ m1_pre_topc(D_402,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_166])).

tff(c_171,plain,(
    ! [D_402] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_402)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_402)
      | ~ m1_pre_topc(D_402,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_40,c_38,c_168])).

tff(c_172,plain,(
    ! [D_402] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_402)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_402)
      | ~ m1_pre_topc(D_402,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_171])).

tff(c_284,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_172])).

tff(c_291,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_284])).

tff(c_158,plain,(
    ! [B_393,A_392,C_394,E_396,D_395] :
      ( v1_funct_1(k3_tmap_1(A_392,B_393,C_394,D_395,E_396))
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394),u1_struct_0(B_393))))
      | ~ v1_funct_2(E_396,u1_struct_0(C_394),u1_struct_0(B_393))
      | ~ v1_funct_1(E_396)
      | ~ m1_pre_topc(D_395,A_392)
      | ~ m1_pre_topc(C_394,A_392)
      | ~ l1_pre_topc(B_393)
      | ~ v2_pre_topc(B_393)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_160,plain,(
    ! [A_392,D_395] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_1',D_395,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_395,A_392)
      | ~ m1_pre_topc('#skF_1',A_392)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(resolution,[status(thm)],[c_36,c_158])).

tff(c_163,plain,(
    ! [A_392,D_395] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_1',D_395,'#skF_5'))
      | ~ m1_pre_topc(D_395,A_392)
      | ~ m1_pre_topc('#skF_1',A_392)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_160])).

tff(c_164,plain,(
    ! [A_392,D_395] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_1',D_395,'#skF_5'))
      | ~ m1_pre_topc(D_395,A_392)
      | ~ m1_pre_topc('#skF_1',A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_163])).

tff(c_305,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_164])).

tff(c_315,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_42,c_305])).

tff(c_316,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_315])).

tff(c_182,plain,(
    ! [C_406,A_404,D_407,E_408,B_405] :
      ( v1_funct_2(k3_tmap_1(A_404,B_405,C_406,D_407,E_408),u1_struct_0(D_407),u1_struct_0(B_405))
      | ~ m1_subset_1(E_408,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_406),u1_struct_0(B_405))))
      | ~ v1_funct_2(E_408,u1_struct_0(C_406),u1_struct_0(B_405))
      | ~ v1_funct_1(E_408)
      | ~ m1_pre_topc(D_407,A_404)
      | ~ m1_pre_topc(C_406,A_404)
      | ~ l1_pre_topc(B_405)
      | ~ v2_pre_topc(B_405)
      | v2_struct_0(B_405)
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_184,plain,(
    ! [A_404,D_407] :
      ( v1_funct_2(k3_tmap_1(A_404,'#skF_2','#skF_1',D_407,'#skF_5'),u1_struct_0(D_407),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_407,A_404)
      | ~ m1_pre_topc('#skF_1',A_404)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(resolution,[status(thm)],[c_36,c_182])).

tff(c_187,plain,(
    ! [A_404,D_407] :
      ( v1_funct_2(k3_tmap_1(A_404,'#skF_2','#skF_1',D_407,'#skF_5'),u1_struct_0(D_407),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_407,A_404)
      | ~ m1_pre_topc('#skF_1',A_404)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_184])).

tff(c_188,plain,(
    ! [A_404,D_407] :
      ( v1_funct_2(k3_tmap_1(A_404,'#skF_2','#skF_1',D_407,'#skF_5'),u1_struct_0(D_407),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_407,A_404)
      | ~ m1_pre_topc('#skF_1',A_404)
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_187])).

tff(c_302,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_188])).

tff(c_312,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_42,c_302])).

tff(c_313,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_312])).

tff(c_10,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] :
      ( m1_subset_1(k3_tmap_1(A_51,B_52,C_53,D_54,E_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_54),u1_struct_0(B_52))))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53),u1_struct_0(B_52))))
      | ~ v1_funct_2(E_55,u1_struct_0(C_53),u1_struct_0(B_52))
      | ~ v1_funct_1(E_55)
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc(C_53,A_51)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_299,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_10])).

tff(c_309,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_255,c_42,c_40,c_38,c_36,c_299])).

tff(c_310,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_309])).

tff(c_8,plain,(
    ! [E_50,D_48,B_36,A_20,C_44] :
      ( k3_tmap_1(A_20,B_36,C_44,D_48,E_50) = k2_partfun1(u1_struct_0(C_44),u1_struct_0(B_36),E_50,u1_struct_0(D_48))
      | ~ m1_pre_topc(D_48,C_44)
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_44),u1_struct_0(B_36))))
      | ~ v1_funct_2(E_50,u1_struct_0(C_44),u1_struct_0(B_36))
      | ~ v1_funct_1(E_50)
      | ~ m1_pre_topc(D_48,A_20)
      | ~ m1_pre_topc(C_44,A_20)
      | ~ l1_pre_topc(B_36)
      | ~ v2_pre_topc(B_36)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_332,plain,(
    ! [A_20,D_48] :
      ( k3_tmap_1(A_20,'#skF_2','#skF_4',D_48,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_48))
      | ~ m1_pre_topc(D_48,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_48,A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_310,c_8])).

tff(c_347,plain,(
    ! [A_20,D_48] :
      ( k3_tmap_1(A_20,'#skF_2','#skF_4',D_48,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_48))
      | ~ m1_pre_topc(D_48,'#skF_4')
      | ~ m1_pre_topc(D_48,A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_316,c_313,c_332])).

tff(c_1394,plain,(
    ! [A_509,D_510] :
      ( k3_tmap_1(A_509,'#skF_2','#skF_4',D_510,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_510))
      | ~ m1_pre_topc(D_510,'#skF_4')
      | ~ m1_pre_topc(D_510,A_509)
      | ~ m1_pre_topc('#skF_4',A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_347])).

tff(c_14,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] :
      ( v1_funct_1(k3_tmap_1(A_51,B_52,C_53,D_54,E_55))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53),u1_struct_0(B_52))))
      | ~ v1_funct_2(E_55,u1_struct_0(C_53),u1_struct_0(B_52))
      | ~ v1_funct_1(E_55)
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc(C_53,A_51)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_338,plain,(
    ! [A_51,D_54] :
      ( v1_funct_1(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_310,c_14])).

tff(c_359,plain,(
    ! [A_51,D_54] :
      ( v1_funct_1(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_316,c_313,c_338])).

tff(c_360,plain,(
    ! [A_51,D_54] :
      ( v1_funct_1(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_359])).

tff(c_12275,plain,(
    ! [D_1205,A_1206] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_1205)))
      | ~ m1_pre_topc(D_1205,A_1206)
      | ~ m1_pre_topc('#skF_4',A_1206)
      | ~ l1_pre_topc(A_1206)
      | ~ v2_pre_topc(A_1206)
      | v2_struct_0(A_1206)
      | ~ m1_pre_topc(D_1205,'#skF_4')
      | ~ m1_pre_topc(D_1205,A_1206)
      | ~ m1_pre_topc('#skF_4',A_1206)
      | ~ l1_pre_topc(A_1206)
      | ~ v2_pre_topc(A_1206)
      | v2_struct_0(A_1206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_360])).

tff(c_12287,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_12275])).

tff(c_12307,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_46,c_34,c_12287])).

tff(c_12308,plain,(
    v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_12307])).

tff(c_12,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] :
      ( v1_funct_2(k3_tmap_1(A_51,B_52,C_53,D_54,E_55),u1_struct_0(D_54),u1_struct_0(B_52))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53),u1_struct_0(B_52))))
      | ~ v1_funct_2(E_55,u1_struct_0(C_53),u1_struct_0(B_52))
      | ~ v1_funct_1(E_55)
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc(C_53,A_51)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_334,plain,(
    ! [A_51,D_54] :
      ( v1_funct_2(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_54),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_310,c_12])).

tff(c_351,plain,(
    ! [A_51,D_54] :
      ( v1_funct_2(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_54),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_316,c_313,c_334])).

tff(c_352,plain,(
    ! [A_51,D_54] :
      ( v1_funct_2(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_54),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_351])).

tff(c_12874,plain,(
    ! [D_1242,A_1243] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_1242)),u1_struct_0(D_1242),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_1242,A_1243)
      | ~ m1_pre_topc('#skF_4',A_1243)
      | ~ l1_pre_topc(A_1243)
      | ~ v2_pre_topc(A_1243)
      | v2_struct_0(A_1243)
      | ~ m1_pre_topc(D_1242,'#skF_4')
      | ~ m1_pre_topc(D_1242,A_1243)
      | ~ m1_pre_topc('#skF_4',A_1243)
      | ~ l1_pre_topc(A_1243)
      | ~ v2_pre_topc(A_1243)
      | v2_struct_0(A_1243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_352])).

tff(c_12886,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_12874])).

tff(c_12906,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_46,c_34,c_12886])).

tff(c_12907,plain,(
    v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_12906])).

tff(c_1428,plain,(
    ! [D_510,A_509] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_510)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_510),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_510,A_509)
      | ~ m1_pre_topc('#skF_4',A_509)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509)
      | ~ m1_pre_topc(D_510,'#skF_4')
      | ~ m1_pre_topc(D_510,A_509)
      | ~ m1_pre_topc('#skF_4',A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_10])).

tff(c_1458,plain,(
    ! [D_510,A_509] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_510)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_510),u1_struct_0('#skF_2'))))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_510,'#skF_4')
      | ~ m1_pre_topc(D_510,A_509)
      | ~ m1_pre_topc('#skF_4',A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509)
      | v2_struct_0(A_509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_316,c_313,c_310,c_1428])).

tff(c_1461,plain,(
    ! [D_511,A_512] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_511)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_511),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_511,'#skF_4')
      | ~ m1_pre_topc(D_511,A_512)
      | ~ m1_pre_topc('#skF_4',A_512)
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1458])).

tff(c_1473,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1461])).

tff(c_1493,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_34,c_1473])).

tff(c_1494,plain,(
    m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1493])).

tff(c_223,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_213])).

tff(c_239,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46,c_223])).

tff(c_240,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_239])).

tff(c_504,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_240])).

tff(c_508,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_172])).

tff(c_515,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_508])).

tff(c_535,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_164])).

tff(c_551,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_46,c_535])).

tff(c_552,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_551])).

tff(c_532,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_188])).

tff(c_548,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_46,c_532])).

tff(c_549,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_548])).

tff(c_529,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_10])).

tff(c_545,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_255,c_46,c_40,c_38,c_36,c_529])).

tff(c_546,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_545])).

tff(c_348,plain,(
    ! [A_20,D_48] :
      ( k3_tmap_1(A_20,'#skF_2','#skF_4',D_48,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_48))
      | ~ m1_pre_topc(D_48,'#skF_4')
      | ~ m1_pre_topc(D_48,A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_347])).

tff(c_13577,plain,(
    ! [A_1285,D_1284,A_1283] :
      ( k3_tmap_1(A_1285,'#skF_2','#skF_4',D_1284,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k3_tmap_1(A_1283,'#skF_2','#skF_4',D_1284,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_1284,'#skF_4')
      | ~ m1_pre_topc(D_1284,A_1285)
      | ~ m1_pre_topc('#skF_4',A_1285)
      | ~ l1_pre_topc(A_1285)
      | ~ v2_pre_topc(A_1285)
      | v2_struct_0(A_1285)
      | ~ m1_pre_topc(D_1284,'#skF_4')
      | ~ m1_pre_topc(D_1284,A_1283)
      | ~ m1_pre_topc('#skF_4',A_1283)
      | ~ l1_pre_topc(A_1283)
      | ~ v2_pre_topc(A_1283)
      | v2_struct_0(A_1283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_348])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_18,plain,(
    ! [A_57,C_105,B_89,E_117,D_113,F_119] :
      ( r2_funct_2(u1_struct_0(E_117),u1_struct_0(B_89),k3_tmap_1(A_57,B_89,D_113,E_117,k3_tmap_1(A_57,B_89,C_105,D_113,F_119)),k3_tmap_1(A_57,B_89,C_105,E_117,F_119))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_105),u1_struct_0(B_89))))
      | ~ v1_funct_2(F_119,u1_struct_0(C_105),u1_struct_0(B_89))
      | ~ v1_funct_1(F_119)
      | ~ m1_pre_topc(E_117,D_113)
      | ~ m1_pre_topc(D_113,C_105)
      | ~ m1_pre_topc(E_117,A_57)
      | v2_struct_0(E_117)
      | ~ m1_pre_topc(D_113,A_57)
      | v2_struct_0(D_113)
      | ~ m1_pre_topc(C_105,A_57)
      | v2_struct_0(C_105)
      | ~ l1_pre_topc(B_89)
      | ~ v2_pre_topc(B_89)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_526,plain,(
    ! [D_113] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_113,'#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_113,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_3',D_113)
      | ~ m1_pre_topc(D_113,'#skF_1')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_113,'#skF_1')
      | v2_struct_0(D_113)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_18])).

tff(c_542,plain,(
    ! [D_113] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_113,'#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_113,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3',D_113)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_113,'#skF_1')
      | v2_struct_0(D_113)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_255,c_46,c_40,c_38,c_36,c_526])).

tff(c_1066,plain,(
    ! [D_485] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',D_485,'#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1',D_485,'#skF_5')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3',D_485)
      | ~ m1_pre_topc(D_485,'#skF_1')
      | v2_struct_0(D_485) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_48,c_542])).

tff(c_1077,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_1066])).

tff(c_1088,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_1077])).

tff(c_1089,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1088])).

tff(c_13674,plain,(
    ! [A_1285] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_1285,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_1285)
      | ~ m1_pre_topc('#skF_4',A_1285)
      | ~ l1_pre_topc(A_1285)
      | ~ v2_pre_topc(A_1285)
      | v2_struct_0(A_1285)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13577,c_1089])).

tff(c_13813,plain,(
    ! [A_1285] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_1285,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1285)
      | ~ m1_pre_topc('#skF_4',A_1285)
      | ~ l1_pre_topc(A_1285)
      | ~ v2_pre_topc(A_1285)
      | v2_struct_0(A_1285)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_46,c_34,c_34,c_13674])).

tff(c_13860,plain,(
    ! [A_1286] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1(A_1286,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_1286)
      | ~ m1_pre_topc('#skF_4',A_1286)
      | ~ l1_pre_topc(A_1286)
      | ~ v2_pre_topc(A_1286)
      | v2_struct_0(A_1286) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13813])).

tff(c_13874,plain,(
    ! [A_20] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_13860])).

tff(c_13883,plain,(
    ! [A_20] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_13874])).

tff(c_13921,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13883])).

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

tff(c_13923,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_13921,c_4])).

tff(c_13929,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12308,c_12907,c_1494,c_552,c_549,c_546,c_13923])).

tff(c_13952,plain,(
    ! [A_20] :
      ( k3_tmap_1(A_20,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13929,c_348])).

tff(c_14003,plain,(
    ! [A_1290] :
      ( k3_tmap_1(A_1290,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1290)
      | ~ m1_pre_topc('#skF_4',A_1290)
      | ~ l1_pre_topc(A_1290)
      | ~ v2_pre_topc(A_1290)
      | v2_struct_0(A_1290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_13952])).

tff(c_318,plain,(
    ! [C_423,G_424,E_426,D_425,A_428,B_427] :
      ( r1_tmap_1(D_425,B_427,k3_tmap_1(A_428,B_427,C_423,D_425,E_426),G_424)
      | ~ r1_tmap_1(C_423,B_427,E_426,G_424)
      | ~ m1_pre_topc(D_425,C_423)
      | ~ m1_subset_1(G_424,u1_struct_0(D_425))
      | ~ m1_subset_1(G_424,u1_struct_0(C_423))
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_423),u1_struct_0(B_427))))
      | ~ v1_funct_2(E_426,u1_struct_0(C_423),u1_struct_0(B_427))
      | ~ v1_funct_1(E_426)
      | ~ m1_pre_topc(D_425,A_428)
      | v2_struct_0(D_425)
      | ~ m1_pre_topc(C_423,A_428)
      | v2_struct_0(C_423)
      | ~ l1_pre_topc(B_427)
      | ~ v2_pre_topc(B_427)
      | v2_struct_0(B_427)
      | ~ l1_pre_topc(A_428)
      | ~ v2_pre_topc(A_428)
      | v2_struct_0(A_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_1310,plain,(
    ! [B_500,G_498,D_505,D_502,C_501,A_503,A_499,E_504] :
      ( r1_tmap_1(D_505,B_500,k3_tmap_1(A_503,B_500,D_502,D_505,k3_tmap_1(A_499,B_500,C_501,D_502,E_504)),G_498)
      | ~ r1_tmap_1(D_502,B_500,k3_tmap_1(A_499,B_500,C_501,D_502,E_504),G_498)
      | ~ m1_pre_topc(D_505,D_502)
      | ~ m1_subset_1(G_498,u1_struct_0(D_505))
      | ~ m1_subset_1(G_498,u1_struct_0(D_502))
      | ~ v1_funct_2(k3_tmap_1(A_499,B_500,C_501,D_502,E_504),u1_struct_0(D_502),u1_struct_0(B_500))
      | ~ v1_funct_1(k3_tmap_1(A_499,B_500,C_501,D_502,E_504))
      | ~ m1_pre_topc(D_505,A_503)
      | v2_struct_0(D_505)
      | ~ m1_pre_topc(D_502,A_503)
      | v2_struct_0(D_502)
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503)
      | ~ m1_subset_1(E_504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_501),u1_struct_0(B_500))))
      | ~ v1_funct_2(E_504,u1_struct_0(C_501),u1_struct_0(B_500))
      | ~ v1_funct_1(E_504)
      | ~ m1_pre_topc(D_502,A_499)
      | ~ m1_pre_topc(C_501,A_499)
      | ~ l1_pre_topc(B_500)
      | ~ v2_pre_topc(B_500)
      | v2_struct_0(B_500)
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(resolution,[status(thm)],[c_10,c_318])).

tff(c_1326,plain,(
    ! [D_505,A_503,G_498] :
      ( r1_tmap_1(D_505,'#skF_2',k3_tmap_1(A_503,'#skF_2','#skF_4',D_505,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')),G_498)
      | ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),G_498)
      | ~ m1_pre_topc(D_505,'#skF_4')
      | ~ m1_subset_1(G_498,u1_struct_0(D_505))
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_4'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_505,A_503)
      | v2_struct_0(D_505)
      | ~ m1_pre_topc('#skF_4',A_503)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_1310])).

tff(c_1352,plain,(
    ! [D_505,A_503,G_498] :
      ( r1_tmap_1(D_505,'#skF_2',k3_tmap_1(A_503,'#skF_2','#skF_4',D_505,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),G_498)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_498)
      | ~ m1_pre_topc(D_505,'#skF_4')
      | ~ m1_subset_1(G_498,u1_struct_0(D_505))
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_505,A_503)
      | v2_struct_0(D_505)
      | ~ m1_pre_topc('#skF_4',A_503)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_255,c_42,c_40,c_38,c_36,c_316,c_291,c_313,c_291,c_291,c_1326])).

tff(c_1353,plain,(
    ! [D_505,A_503,G_498] :
      ( r1_tmap_1(D_505,'#skF_2',k3_tmap_1(A_503,'#skF_2','#skF_4',D_505,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),G_498)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_498)
      | ~ m1_pre_topc(D_505,'#skF_4')
      | ~ m1_subset_1(G_498,u1_struct_0(D_505))
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_505,A_503)
      | v2_struct_0(D_505)
      | ~ m1_pre_topc('#skF_4',A_503)
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_44,c_1352])).

tff(c_14043,plain,(
    ! [G_498,A_1290] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),G_498)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_498)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_1290)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4',A_1290)
      | ~ l1_pre_topc(A_1290)
      | ~ v2_pre_topc(A_1290)
      | v2_struct_0(A_1290)
      | ~ m1_pre_topc('#skF_3',A_1290)
      | ~ m1_pre_topc('#skF_4',A_1290)
      | ~ l1_pre_topc(A_1290)
      | ~ v2_pre_topc(A_1290)
      | v2_struct_0(A_1290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14003,c_1353])).

tff(c_14137,plain,(
    ! [G_498,A_1290] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),G_498)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_498)
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_1290)
      | ~ m1_pre_topc('#skF_4',A_1290)
      | ~ l1_pre_topc(A_1290)
      | ~ v2_pre_topc(A_1290)
      | v2_struct_0(A_1290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14043])).

tff(c_14138,plain,(
    ! [G_498,A_1290] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),G_498)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_498)
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_498,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_1290)
      | ~ m1_pre_topc('#skF_4',A_1290)
      | ~ l1_pre_topc(A_1290)
      | ~ v2_pre_topc(A_1290)
      | v2_struct_0(A_1290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_14137])).

tff(c_14185,plain,(
    ! [A_1291] :
      ( ~ m1_pre_topc('#skF_3',A_1291)
      | ~ m1_pre_topc('#skF_4',A_1291)
      | ~ l1_pre_topc(A_1291)
      | ~ v2_pre_topc(A_1291)
      | v2_struct_0(A_1291) ) ),
    inference(splitLeft,[status(thm)],[c_14138])).

tff(c_14198,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_14185])).

tff(c_14208,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_14198])).

tff(c_14210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_14208])).

tff(c_14212,plain,(
    ! [G_1292] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),G_1292)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_1292)
      | ~ m1_subset_1(G_1292,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_1292,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_14138])).

tff(c_24,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_62,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24])).

tff(c_14215,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_14212,c_62])).

tff(c_14219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_26,c_14215])).

tff(c_14259,plain,(
    ! [A_1294] :
      ( ~ m1_pre_topc('#skF_3',A_1294)
      | ~ m1_pre_topc('#skF_4',A_1294)
      | ~ l1_pre_topc(A_1294)
      | ~ v2_pre_topc(A_1294)
      | v2_struct_0(A_1294) ) ),
    inference(splitRight,[status(thm)],[c_13883])).

tff(c_14272,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_14259])).

tff(c_14282,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_14272])).

tff(c_14284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_14282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:45:47 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.22/6.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.22/6.31  
% 14.22/6.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.22/6.31  %$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.22/6.31  
% 14.22/6.31  %Foreground sorts:
% 14.22/6.31  
% 14.22/6.31  
% 14.22/6.31  %Background operators:
% 14.22/6.31  
% 14.22/6.31  
% 14.22/6.31  %Foreground operators:
% 14.22/6.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.22/6.31  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 14.22/6.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.22/6.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.22/6.31  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 14.22/6.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.22/6.31  tff('#skF_7', type, '#skF_7': $i).
% 14.22/6.31  tff('#skF_5', type, '#skF_5': $i).
% 14.22/6.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.22/6.31  tff('#skF_6', type, '#skF_6': $i).
% 14.22/6.31  tff('#skF_2', type, '#skF_2': $i).
% 14.22/6.31  tff('#skF_3', type, '#skF_3': $i).
% 14.22/6.31  tff('#skF_1', type, '#skF_1': $i).
% 14.22/6.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.22/6.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.22/6.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.22/6.31  tff('#skF_4', type, '#skF_4': $i).
% 14.22/6.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.22/6.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 14.22/6.31  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 14.22/6.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.22/6.31  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 14.22/6.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.22/6.31  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 14.22/6.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.22/6.31  
% 14.22/6.34  tff(f_289, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(D, B, k2_tmap_1(A, B, E, D), F)) => r1_tmap_1(C, B, k2_tmap_1(A, B, E, C), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_tmap_1)).
% 14.22/6.34  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 14.22/6.34  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 14.22/6.34  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 14.22/6.34  tff(f_130, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 14.22/6.34  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 14.22/6.34  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 14.22/6.34  tff(f_240, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 14.22/6.34  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_28, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_61, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 14.22/6.34  tff(c_26, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_16, plain, (![A_56]: (m1_pre_topc(A_56, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.22/6.34  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_203, plain, (![B_419, C_420, A_418, D_417, E_416]: (k3_tmap_1(A_418, B_419, C_420, D_417, E_416)=k2_partfun1(u1_struct_0(C_420), u1_struct_0(B_419), E_416, u1_struct_0(D_417)) | ~m1_pre_topc(D_417, C_420) | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_420), u1_struct_0(B_419)))) | ~v1_funct_2(E_416, u1_struct_0(C_420), u1_struct_0(B_419)) | ~v1_funct_1(E_416) | ~m1_pre_topc(D_417, A_418) | ~m1_pre_topc(C_420, A_418) | ~l1_pre_topc(B_419) | ~v2_pre_topc(B_419) | v2_struct_0(B_419) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.22/6.34  tff(c_207, plain, (![A_418, D_417]: (k3_tmap_1(A_418, '#skF_2', '#skF_1', D_417, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_417)) | ~m1_pre_topc(D_417, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_417, A_418) | ~m1_pre_topc('#skF_1', A_418) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418))), inference(resolution, [status(thm)], [c_36, c_203])).
% 14.22/6.34  tff(c_211, plain, (![A_418, D_417]: (k3_tmap_1(A_418, '#skF_2', '#skF_1', D_417, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_417)) | ~m1_pre_topc(D_417, '#skF_1') | ~m1_pre_topc(D_417, A_418) | ~m1_pre_topc('#skF_1', A_418) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_207])).
% 14.22/6.34  tff(c_213, plain, (![A_421, D_422]: (k3_tmap_1(A_421, '#skF_2', '#skF_1', D_422, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_422)) | ~m1_pre_topc(D_422, '#skF_1') | ~m1_pre_topc(D_422, A_421) | ~m1_pre_topc('#skF_1', A_421) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421) | v2_struct_0(A_421))), inference(negUnitSimplification, [status(thm)], [c_54, c_211])).
% 14.22/6.34  tff(c_221, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_213])).
% 14.22/6.34  tff(c_235, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_221])).
% 14.22/6.34  tff(c_236, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_235])).
% 14.22/6.34  tff(c_245, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_236])).
% 14.22/6.34  tff(c_249, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_245])).
% 14.22/6.34  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_249])).
% 14.22/6.34  tff(c_255, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_236])).
% 14.22/6.34  tff(c_254, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_236])).
% 14.22/6.34  tff(c_166, plain, (![A_399, B_400, C_401, D_402]: (k2_partfun1(u1_struct_0(A_399), u1_struct_0(B_400), C_401, u1_struct_0(D_402))=k2_tmap_1(A_399, B_400, C_401, D_402) | ~m1_pre_topc(D_402, A_399) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_399), u1_struct_0(B_400)))) | ~v1_funct_2(C_401, u1_struct_0(A_399), u1_struct_0(B_400)) | ~v1_funct_1(C_401) | ~l1_pre_topc(B_400) | ~v2_pre_topc(B_400) | v2_struct_0(B_400) | ~l1_pre_topc(A_399) | ~v2_pre_topc(A_399) | v2_struct_0(A_399))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.22/6.34  tff(c_168, plain, (![D_402]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_402))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_402) | ~m1_pre_topc(D_402, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_166])).
% 14.22/6.34  tff(c_171, plain, (![D_402]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_402))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_402) | ~m1_pre_topc(D_402, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_40, c_38, c_168])).
% 14.22/6.34  tff(c_172, plain, (![D_402]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_402))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_402) | ~m1_pre_topc(D_402, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_171])).
% 14.22/6.34  tff(c_284, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_254, c_172])).
% 14.22/6.34  tff(c_291, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_284])).
% 14.22/6.34  tff(c_158, plain, (![B_393, A_392, C_394, E_396, D_395]: (v1_funct_1(k3_tmap_1(A_392, B_393, C_394, D_395, E_396)) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394), u1_struct_0(B_393)))) | ~v1_funct_2(E_396, u1_struct_0(C_394), u1_struct_0(B_393)) | ~v1_funct_1(E_396) | ~m1_pre_topc(D_395, A_392) | ~m1_pre_topc(C_394, A_392) | ~l1_pre_topc(B_393) | ~v2_pre_topc(B_393) | v2_struct_0(B_393) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.22/6.34  tff(c_160, plain, (![A_392, D_395]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_1', D_395, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_395, A_392) | ~m1_pre_topc('#skF_1', A_392) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(resolution, [status(thm)], [c_36, c_158])).
% 14.22/6.34  tff(c_163, plain, (![A_392, D_395]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_1', D_395, '#skF_5')) | ~m1_pre_topc(D_395, A_392) | ~m1_pre_topc('#skF_1', A_392) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_160])).
% 14.22/6.34  tff(c_164, plain, (![A_392, D_395]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_1', D_395, '#skF_5')) | ~m1_pre_topc(D_395, A_392) | ~m1_pre_topc('#skF_1', A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(negUnitSimplification, [status(thm)], [c_54, c_163])).
% 14.22/6.34  tff(c_305, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_164])).
% 14.22/6.34  tff(c_315, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_42, c_305])).
% 14.22/6.34  tff(c_316, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_315])).
% 14.22/6.34  tff(c_182, plain, (![C_406, A_404, D_407, E_408, B_405]: (v1_funct_2(k3_tmap_1(A_404, B_405, C_406, D_407, E_408), u1_struct_0(D_407), u1_struct_0(B_405)) | ~m1_subset_1(E_408, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_406), u1_struct_0(B_405)))) | ~v1_funct_2(E_408, u1_struct_0(C_406), u1_struct_0(B_405)) | ~v1_funct_1(E_408) | ~m1_pre_topc(D_407, A_404) | ~m1_pre_topc(C_406, A_404) | ~l1_pre_topc(B_405) | ~v2_pre_topc(B_405) | v2_struct_0(B_405) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.22/6.34  tff(c_184, plain, (![A_404, D_407]: (v1_funct_2(k3_tmap_1(A_404, '#skF_2', '#skF_1', D_407, '#skF_5'), u1_struct_0(D_407), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_407, A_404) | ~m1_pre_topc('#skF_1', A_404) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(resolution, [status(thm)], [c_36, c_182])).
% 14.22/6.34  tff(c_187, plain, (![A_404, D_407]: (v1_funct_2(k3_tmap_1(A_404, '#skF_2', '#skF_1', D_407, '#skF_5'), u1_struct_0(D_407), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_407, A_404) | ~m1_pre_topc('#skF_1', A_404) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_184])).
% 14.22/6.34  tff(c_188, plain, (![A_404, D_407]: (v1_funct_2(k3_tmap_1(A_404, '#skF_2', '#skF_1', D_407, '#skF_5'), u1_struct_0(D_407), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_407, A_404) | ~m1_pre_topc('#skF_1', A_404) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(negUnitSimplification, [status(thm)], [c_54, c_187])).
% 14.22/6.34  tff(c_302, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_188])).
% 14.22/6.34  tff(c_312, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_42, c_302])).
% 14.22/6.34  tff(c_313, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_312])).
% 14.22/6.34  tff(c_10, plain, (![B_52, E_55, C_53, D_54, A_51]: (m1_subset_1(k3_tmap_1(A_51, B_52, C_53, D_54, E_55), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_54), u1_struct_0(B_52)))) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53), u1_struct_0(B_52)))) | ~v1_funct_2(E_55, u1_struct_0(C_53), u1_struct_0(B_52)) | ~v1_funct_1(E_55) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc(C_53, A_51) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | v2_struct_0(B_52) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.22/6.34  tff(c_299, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_10])).
% 14.22/6.34  tff(c_309, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_255, c_42, c_40, c_38, c_36, c_299])).
% 14.22/6.34  tff(c_310, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_309])).
% 14.22/6.34  tff(c_8, plain, (![E_50, D_48, B_36, A_20, C_44]: (k3_tmap_1(A_20, B_36, C_44, D_48, E_50)=k2_partfun1(u1_struct_0(C_44), u1_struct_0(B_36), E_50, u1_struct_0(D_48)) | ~m1_pre_topc(D_48, C_44) | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_44), u1_struct_0(B_36)))) | ~v1_funct_2(E_50, u1_struct_0(C_44), u1_struct_0(B_36)) | ~v1_funct_1(E_50) | ~m1_pre_topc(D_48, A_20) | ~m1_pre_topc(C_44, A_20) | ~l1_pre_topc(B_36) | ~v2_pre_topc(B_36) | v2_struct_0(B_36) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.22/6.34  tff(c_332, plain, (![A_20, D_48]: (k3_tmap_1(A_20, '#skF_2', '#skF_4', D_48, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_48)) | ~m1_pre_topc(D_48, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_48, A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(resolution, [status(thm)], [c_310, c_8])).
% 14.22/6.34  tff(c_347, plain, (![A_20, D_48]: (k3_tmap_1(A_20, '#skF_2', '#skF_4', D_48, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_48)) | ~m1_pre_topc(D_48, '#skF_4') | ~m1_pre_topc(D_48, A_20) | ~m1_pre_topc('#skF_4', A_20) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_316, c_313, c_332])).
% 14.22/6.34  tff(c_1394, plain, (![A_509, D_510]: (k3_tmap_1(A_509, '#skF_2', '#skF_4', D_510, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_510)) | ~m1_pre_topc(D_510, '#skF_4') | ~m1_pre_topc(D_510, A_509) | ~m1_pre_topc('#skF_4', A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509))), inference(negUnitSimplification, [status(thm)], [c_54, c_347])).
% 14.22/6.34  tff(c_14, plain, (![B_52, E_55, C_53, D_54, A_51]: (v1_funct_1(k3_tmap_1(A_51, B_52, C_53, D_54, E_55)) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53), u1_struct_0(B_52)))) | ~v1_funct_2(E_55, u1_struct_0(C_53), u1_struct_0(B_52)) | ~v1_funct_1(E_55) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc(C_53, A_51) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | v2_struct_0(B_52) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.22/6.34  tff(c_338, plain, (![A_51, D_54]: (v1_funct_1(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_310, c_14])).
% 14.22/6.34  tff(c_359, plain, (![A_51, D_54]: (v1_funct_1(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_316, c_313, c_338])).
% 14.22/6.34  tff(c_360, plain, (![A_51, D_54]: (v1_funct_1(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(negUnitSimplification, [status(thm)], [c_54, c_359])).
% 14.22/6.34  tff(c_12275, plain, (![D_1205, A_1206]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_1205))) | ~m1_pre_topc(D_1205, A_1206) | ~m1_pre_topc('#skF_4', A_1206) | ~l1_pre_topc(A_1206) | ~v2_pre_topc(A_1206) | v2_struct_0(A_1206) | ~m1_pre_topc(D_1205, '#skF_4') | ~m1_pre_topc(D_1205, A_1206) | ~m1_pre_topc('#skF_4', A_1206) | ~l1_pre_topc(A_1206) | ~v2_pre_topc(A_1206) | v2_struct_0(A_1206))), inference(superposition, [status(thm), theory('equality')], [c_1394, c_360])).
% 14.22/6.34  tff(c_12287, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_12275])).
% 14.22/6.34  tff(c_12307, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_46, c_34, c_12287])).
% 14.22/6.34  tff(c_12308, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_12307])).
% 14.22/6.34  tff(c_12, plain, (![B_52, E_55, C_53, D_54, A_51]: (v1_funct_2(k3_tmap_1(A_51, B_52, C_53, D_54, E_55), u1_struct_0(D_54), u1_struct_0(B_52)) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53), u1_struct_0(B_52)))) | ~v1_funct_2(E_55, u1_struct_0(C_53), u1_struct_0(B_52)) | ~v1_funct_1(E_55) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc(C_53, A_51) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | v2_struct_0(B_52) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.22/6.34  tff(c_334, plain, (![A_51, D_54]: (v1_funct_2(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_54), u1_struct_0('#skF_2')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_310, c_12])).
% 14.22/6.34  tff(c_351, plain, (![A_51, D_54]: (v1_funct_2(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_54), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_316, c_313, c_334])).
% 14.22/6.34  tff(c_352, plain, (![A_51, D_54]: (v1_funct_2(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_54), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(negUnitSimplification, [status(thm)], [c_54, c_351])).
% 14.22/6.34  tff(c_12874, plain, (![D_1242, A_1243]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_1242)), u1_struct_0(D_1242), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_1242, A_1243) | ~m1_pre_topc('#skF_4', A_1243) | ~l1_pre_topc(A_1243) | ~v2_pre_topc(A_1243) | v2_struct_0(A_1243) | ~m1_pre_topc(D_1242, '#skF_4') | ~m1_pre_topc(D_1242, A_1243) | ~m1_pre_topc('#skF_4', A_1243) | ~l1_pre_topc(A_1243) | ~v2_pre_topc(A_1243) | v2_struct_0(A_1243))), inference(superposition, [status(thm), theory('equality')], [c_1394, c_352])).
% 14.22/6.34  tff(c_12886, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_12874])).
% 14.22/6.34  tff(c_12906, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_46, c_34, c_12886])).
% 14.22/6.34  tff(c_12907, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_12906])).
% 14.22/6.34  tff(c_1428, plain, (![D_510, A_509]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_510)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_510), u1_struct_0('#skF_2')))) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_510, A_509) | ~m1_pre_topc('#skF_4', A_509) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509) | ~m1_pre_topc(D_510, '#skF_4') | ~m1_pre_topc(D_510, A_509) | ~m1_pre_topc('#skF_4', A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509))), inference(superposition, [status(thm), theory('equality')], [c_1394, c_10])).
% 14.22/6.34  tff(c_1458, plain, (![D_510, A_509]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_510)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_510), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_510, '#skF_4') | ~m1_pre_topc(D_510, A_509) | ~m1_pre_topc('#skF_4', A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509) | v2_struct_0(A_509))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_316, c_313, c_310, c_1428])).
% 14.22/6.34  tff(c_1461, plain, (![D_511, A_512]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_511)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_511), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_511, '#skF_4') | ~m1_pre_topc(D_511, A_512) | ~m1_pre_topc('#skF_4', A_512) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512))), inference(negUnitSimplification, [status(thm)], [c_54, c_1458])).
% 14.22/6.34  tff(c_1473, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1461])).
% 14.22/6.34  tff(c_1493, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_34, c_1473])).
% 14.22/6.34  tff(c_1494, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_1493])).
% 14.22/6.34  tff(c_223, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_213])).
% 14.22/6.34  tff(c_239, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46, c_223])).
% 14.22/6.34  tff(c_240, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_239])).
% 14.22/6.34  tff(c_504, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_240])).
% 14.22/6.34  tff(c_508, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_504, c_172])).
% 14.22/6.34  tff(c_515, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_508])).
% 14.22/6.34  tff(c_535, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_515, c_164])).
% 14.22/6.34  tff(c_551, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_46, c_535])).
% 14.22/6.34  tff(c_552, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_551])).
% 14.22/6.34  tff(c_532, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_515, c_188])).
% 14.22/6.34  tff(c_548, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_46, c_532])).
% 14.22/6.34  tff(c_549, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_548])).
% 14.22/6.34  tff(c_529, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_515, c_10])).
% 14.22/6.34  tff(c_545, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_255, c_46, c_40, c_38, c_36, c_529])).
% 14.22/6.34  tff(c_546, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_545])).
% 14.22/6.34  tff(c_348, plain, (![A_20, D_48]: (k3_tmap_1(A_20, '#skF_2', '#skF_4', D_48, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_48)) | ~m1_pre_topc(D_48, '#skF_4') | ~m1_pre_topc(D_48, A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(negUnitSimplification, [status(thm)], [c_54, c_347])).
% 14.22/6.34  tff(c_13577, plain, (![A_1285, D_1284, A_1283]: (k3_tmap_1(A_1285, '#skF_2', '#skF_4', D_1284, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k3_tmap_1(A_1283, '#skF_2', '#skF_4', D_1284, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_1284, '#skF_4') | ~m1_pre_topc(D_1284, A_1285) | ~m1_pre_topc('#skF_4', A_1285) | ~l1_pre_topc(A_1285) | ~v2_pre_topc(A_1285) | v2_struct_0(A_1285) | ~m1_pre_topc(D_1284, '#skF_4') | ~m1_pre_topc(D_1284, A_1283) | ~m1_pre_topc('#skF_4', A_1283) | ~l1_pre_topc(A_1283) | ~v2_pre_topc(A_1283) | v2_struct_0(A_1283))), inference(superposition, [status(thm), theory('equality')], [c_1394, c_348])).
% 14.22/6.34  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_18, plain, (![A_57, C_105, B_89, E_117, D_113, F_119]: (r2_funct_2(u1_struct_0(E_117), u1_struct_0(B_89), k3_tmap_1(A_57, B_89, D_113, E_117, k3_tmap_1(A_57, B_89, C_105, D_113, F_119)), k3_tmap_1(A_57, B_89, C_105, E_117, F_119)) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_105), u1_struct_0(B_89)))) | ~v1_funct_2(F_119, u1_struct_0(C_105), u1_struct_0(B_89)) | ~v1_funct_1(F_119) | ~m1_pre_topc(E_117, D_113) | ~m1_pre_topc(D_113, C_105) | ~m1_pre_topc(E_117, A_57) | v2_struct_0(E_117) | ~m1_pre_topc(D_113, A_57) | v2_struct_0(D_113) | ~m1_pre_topc(C_105, A_57) | v2_struct_0(C_105) | ~l1_pre_topc(B_89) | ~v2_pre_topc(B_89) | v2_struct_0(B_89) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_180])).
% 14.22/6.34  tff(c_526, plain, (![D_113]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_113, '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_113, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', D_113) | ~m1_pre_topc(D_113, '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_113, '#skF_1') | v2_struct_0(D_113) | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_515, c_18])).
% 14.22/6.34  tff(c_542, plain, (![D_113]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_113, '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_113, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', D_113) | v2_struct_0('#skF_3') | ~m1_pre_topc(D_113, '#skF_1') | v2_struct_0(D_113) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_255, c_46, c_40, c_38, c_36, c_526])).
% 14.22/6.34  tff(c_1066, plain, (![D_485]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', D_485, '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_485, '#skF_5')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', D_485) | ~m1_pre_topc(D_485, '#skF_1') | v2_struct_0(D_485))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_48, c_542])).
% 14.22/6.34  tff(c_1077, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_291, c_1066])).
% 14.22/6.34  tff(c_1088, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_1077])).
% 14.22/6.34  tff(c_1089, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_1088])).
% 14.22/6.34  tff(c_13674, plain, (![A_1285]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_1285, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', A_1285) | ~m1_pre_topc('#skF_4', A_1285) | ~l1_pre_topc(A_1285) | ~v2_pre_topc(A_1285) | v2_struct_0(A_1285) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13577, c_1089])).
% 14.22/6.34  tff(c_13813, plain, (![A_1285]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_1285, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', A_1285) | ~m1_pre_topc('#skF_4', A_1285) | ~l1_pre_topc(A_1285) | ~v2_pre_topc(A_1285) | v2_struct_0(A_1285) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_46, c_34, c_34, c_13674])).
% 14.22/6.34  tff(c_13860, plain, (![A_1286]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1(A_1286, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', A_1286) | ~m1_pre_topc('#skF_4', A_1286) | ~l1_pre_topc(A_1286) | ~v2_pre_topc(A_1286) | v2_struct_0(A_1286))), inference(negUnitSimplification, [status(thm)], [c_60, c_13813])).
% 14.22/6.34  tff(c_13874, plain, (![A_20]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(superposition, [status(thm), theory('equality')], [c_348, c_13860])).
% 14.22/6.34  tff(c_13883, plain, (![A_20]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_13874])).
% 14.22/6.34  tff(c_13921, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_13883])).
% 14.22/6.34  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.22/6.34  tff(c_13923, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_13921, c_4])).
% 14.22/6.34  tff(c_13929, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12308, c_12907, c_1494, c_552, c_549, c_546, c_13923])).
% 14.22/6.34  tff(c_13952, plain, (![A_20]: (k3_tmap_1(A_20, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(superposition, [status(thm), theory('equality')], [c_13929, c_348])).
% 14.22/6.34  tff(c_14003, plain, (![A_1290]: (k3_tmap_1(A_1290, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', A_1290) | ~m1_pre_topc('#skF_4', A_1290) | ~l1_pre_topc(A_1290) | ~v2_pre_topc(A_1290) | v2_struct_0(A_1290))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_13952])).
% 14.22/6.34  tff(c_318, plain, (![C_423, G_424, E_426, D_425, A_428, B_427]: (r1_tmap_1(D_425, B_427, k3_tmap_1(A_428, B_427, C_423, D_425, E_426), G_424) | ~r1_tmap_1(C_423, B_427, E_426, G_424) | ~m1_pre_topc(D_425, C_423) | ~m1_subset_1(G_424, u1_struct_0(D_425)) | ~m1_subset_1(G_424, u1_struct_0(C_423)) | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_423), u1_struct_0(B_427)))) | ~v1_funct_2(E_426, u1_struct_0(C_423), u1_struct_0(B_427)) | ~v1_funct_1(E_426) | ~m1_pre_topc(D_425, A_428) | v2_struct_0(D_425) | ~m1_pre_topc(C_423, A_428) | v2_struct_0(C_423) | ~l1_pre_topc(B_427) | ~v2_pre_topc(B_427) | v2_struct_0(B_427) | ~l1_pre_topc(A_428) | ~v2_pre_topc(A_428) | v2_struct_0(A_428))), inference(cnfTransformation, [status(thm)], [f_240])).
% 14.22/6.34  tff(c_1310, plain, (![B_500, G_498, D_505, D_502, C_501, A_503, A_499, E_504]: (r1_tmap_1(D_505, B_500, k3_tmap_1(A_503, B_500, D_502, D_505, k3_tmap_1(A_499, B_500, C_501, D_502, E_504)), G_498) | ~r1_tmap_1(D_502, B_500, k3_tmap_1(A_499, B_500, C_501, D_502, E_504), G_498) | ~m1_pre_topc(D_505, D_502) | ~m1_subset_1(G_498, u1_struct_0(D_505)) | ~m1_subset_1(G_498, u1_struct_0(D_502)) | ~v1_funct_2(k3_tmap_1(A_499, B_500, C_501, D_502, E_504), u1_struct_0(D_502), u1_struct_0(B_500)) | ~v1_funct_1(k3_tmap_1(A_499, B_500, C_501, D_502, E_504)) | ~m1_pre_topc(D_505, A_503) | v2_struct_0(D_505) | ~m1_pre_topc(D_502, A_503) | v2_struct_0(D_502) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503) | ~m1_subset_1(E_504, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_501), u1_struct_0(B_500)))) | ~v1_funct_2(E_504, u1_struct_0(C_501), u1_struct_0(B_500)) | ~v1_funct_1(E_504) | ~m1_pre_topc(D_502, A_499) | ~m1_pre_topc(C_501, A_499) | ~l1_pre_topc(B_500) | ~v2_pre_topc(B_500) | v2_struct_0(B_500) | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499))), inference(resolution, [status(thm)], [c_10, c_318])).
% 14.22/6.34  tff(c_1326, plain, (![D_505, A_503, G_498]: (r1_tmap_1(D_505, '#skF_2', k3_tmap_1(A_503, '#skF_2', '#skF_4', D_505, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), G_498) | ~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), G_498) | ~m1_pre_topc(D_505, '#skF_4') | ~m1_subset_1(G_498, u1_struct_0(D_505)) | ~m1_subset_1(G_498, u1_struct_0('#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_505, A_503) | v2_struct_0(D_505) | ~m1_pre_topc('#skF_4', A_503) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_1310])).
% 14.22/6.34  tff(c_1352, plain, (![D_505, A_503, G_498]: (r1_tmap_1(D_505, '#skF_2', k3_tmap_1(A_503, '#skF_2', '#skF_4', D_505, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), G_498) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_498) | ~m1_pre_topc(D_505, '#skF_4') | ~m1_subset_1(G_498, u1_struct_0(D_505)) | ~m1_subset_1(G_498, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_505, A_503) | v2_struct_0(D_505) | ~m1_pre_topc('#skF_4', A_503) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_255, c_42, c_40, c_38, c_36, c_316, c_291, c_313, c_291, c_291, c_1326])).
% 14.22/6.34  tff(c_1353, plain, (![D_505, A_503, G_498]: (r1_tmap_1(D_505, '#skF_2', k3_tmap_1(A_503, '#skF_2', '#skF_4', D_505, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), G_498) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_498) | ~m1_pre_topc(D_505, '#skF_4') | ~m1_subset_1(G_498, u1_struct_0(D_505)) | ~m1_subset_1(G_498, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_505, A_503) | v2_struct_0(D_505) | ~m1_pre_topc('#skF_4', A_503) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_44, c_1352])).
% 14.22/6.34  tff(c_14043, plain, (![G_498, A_1290]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), G_498) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_498) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1(G_498, u1_struct_0('#skF_3')) | ~m1_subset_1(G_498, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', A_1290) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', A_1290) | ~l1_pre_topc(A_1290) | ~v2_pre_topc(A_1290) | v2_struct_0(A_1290) | ~m1_pre_topc('#skF_3', A_1290) | ~m1_pre_topc('#skF_4', A_1290) | ~l1_pre_topc(A_1290) | ~v2_pre_topc(A_1290) | v2_struct_0(A_1290))), inference(superposition, [status(thm), theory('equality')], [c_14003, c_1353])).
% 14.22/6.34  tff(c_14137, plain, (![G_498, A_1290]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), G_498) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_498) | ~m1_subset_1(G_498, u1_struct_0('#skF_3')) | ~m1_subset_1(G_498, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', A_1290) | ~m1_pre_topc('#skF_4', A_1290) | ~l1_pre_topc(A_1290) | ~v2_pre_topc(A_1290) | v2_struct_0(A_1290))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14043])).
% 14.22/6.34  tff(c_14138, plain, (![G_498, A_1290]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), G_498) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_498) | ~m1_subset_1(G_498, u1_struct_0('#skF_3')) | ~m1_subset_1(G_498, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', A_1290) | ~m1_pre_topc('#skF_4', A_1290) | ~l1_pre_topc(A_1290) | ~v2_pre_topc(A_1290) | v2_struct_0(A_1290))), inference(negUnitSimplification, [status(thm)], [c_48, c_14137])).
% 14.22/6.34  tff(c_14185, plain, (![A_1291]: (~m1_pre_topc('#skF_3', A_1291) | ~m1_pre_topc('#skF_4', A_1291) | ~l1_pre_topc(A_1291) | ~v2_pre_topc(A_1291) | v2_struct_0(A_1291))), inference(splitLeft, [status(thm)], [c_14138])).
% 14.22/6.34  tff(c_14198, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_14185])).
% 14.22/6.34  tff(c_14208, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_14198])).
% 14.22/6.34  tff(c_14210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_14208])).
% 14.22/6.34  tff(c_14212, plain, (![G_1292]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), G_1292) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_1292) | ~m1_subset_1(G_1292, u1_struct_0('#skF_3')) | ~m1_subset_1(G_1292, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_14138])).
% 14.22/6.34  tff(c_24, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_289])).
% 14.22/6.34  tff(c_62, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24])).
% 14.22/6.34  tff(c_14215, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_14212, c_62])).
% 14.22/6.34  tff(c_14219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_26, c_14215])).
% 14.22/6.34  tff(c_14259, plain, (![A_1294]: (~m1_pre_topc('#skF_3', A_1294) | ~m1_pre_topc('#skF_4', A_1294) | ~l1_pre_topc(A_1294) | ~v2_pre_topc(A_1294) | v2_struct_0(A_1294))), inference(splitRight, [status(thm)], [c_13883])).
% 14.22/6.34  tff(c_14272, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_14259])).
% 14.22/6.34  tff(c_14282, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_14272])).
% 14.22/6.34  tff(c_14284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_14282])).
% 14.22/6.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.22/6.34  
% 14.22/6.34  Inference rules
% 14.22/6.34  ----------------------
% 14.22/6.34  #Ref     : 0
% 14.22/6.34  #Sup     : 2734
% 14.22/6.34  #Fact    : 0
% 14.22/6.34  #Define  : 0
% 14.22/6.34  #Split   : 33
% 14.22/6.34  #Chain   : 0
% 14.22/6.34  #Close   : 0
% 14.22/6.34  
% 14.22/6.34  Ordering : KBO
% 14.22/6.34  
% 14.22/6.34  Simplification rules
% 14.22/6.34  ----------------------
% 14.22/6.34  #Subsume      : 727
% 14.22/6.34  #Demod        : 8893
% 14.22/6.34  #Tautology    : 400
% 14.22/6.34  #SimpNegUnit  : 1660
% 14.22/6.34  #BackRed      : 22
% 14.22/6.34  
% 14.22/6.34  #Partial instantiations: 0
% 14.22/6.34  #Strategies tried      : 1
% 14.22/6.34  
% 14.22/6.34  Timing (in seconds)
% 14.22/6.34  ----------------------
% 14.22/6.35  Preprocessing        : 0.43
% 14.22/6.35  Parsing              : 0.23
% 14.22/6.35  CNF conversion       : 0.06
% 14.22/6.35  Main loop            : 5.10
% 14.22/6.35  Inferencing          : 1.31
% 14.22/6.35  Reduction            : 2.01
% 14.22/6.35  Demodulation         : 1.62
% 14.22/6.35  BG Simplification    : 0.15
% 14.22/6.35  Subsumption          : 1.48
% 14.22/6.35  Abstraction          : 0.27
% 14.22/6.35  MUC search           : 0.00
% 14.22/6.35  Cooper               : 0.00
% 14.22/6.35  Total                : 5.59
% 14.22/6.35  Index Insertion      : 0.00
% 14.22/6.35  Index Deletion       : 0.00
% 14.22/6.35  Index Matching       : 0.00
% 14.22/6.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
