%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:35 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  119 (1196 expanded)
%              Number of leaves         :   41 ( 437 expanded)
%              Depth                    :   18
%              Number of atoms          :  280 (6904 expanded)
%              Number of equality atoms :   29 (1138 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_228,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_179,axiom,(
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
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_119,plain,(
    ! [B_422,A_423] :
      ( v2_pre_topc(B_422)
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_135,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_128])).

tff(c_91,plain,(
    ! [B_416,A_417] :
      ( l1_pre_topc(B_416)
      | ~ m1_pre_topc(B_416,A_417)
      | ~ l1_pre_topc(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_91])).

tff(c_107,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_100])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_156,plain,(
    ! [B_425,A_426] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_425),u1_pre_topc(B_425)))
      | ~ m1_pre_topc(B_425,A_426)
      | ~ l1_pre_topc(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_160,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_156])).

tff(c_166,plain,(
    v1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_48,c_160])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_104,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97])).

tff(c_12,plain,(
    ! [A_10] :
      ( m1_subset_1(u1_pre_topc(A_10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,(
    ! [D_434,B_435,C_436,A_437] :
      ( D_434 = B_435
      | g1_pre_topc(C_436,D_434) != g1_pre_topc(A_437,B_435)
      | ~ m1_subset_1(B_435,k1_zfmisc_1(k1_zfmisc_1(A_437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_264,plain,(
    ! [D_434,C_436] :
      ( u1_pre_topc('#skF_4') = D_434
      | g1_pre_topc(C_436,D_434) != '#skF_5'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_256])).

tff(c_291,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_294,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_291])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_294])).

tff(c_304,plain,(
    ! [D_443,C_444] :
      ( u1_pre_topc('#skF_4') = D_443
      | g1_pre_topc(C_444,D_443) != '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_318,plain,(
    ! [A_445] :
      ( u1_pre_topc(A_445) = u1_pre_topc('#skF_4')
      | A_445 != '#skF_5'
      | ~ v1_pre_topc(A_445)
      | ~ l1_pre_topc(A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_304])).

tff(c_327,plain,
    ( u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_166,c_318])).

tff(c_334,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_327])).

tff(c_364,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) = '#skF_5'
    | ~ v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_6])).

tff(c_378,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_166,c_364])).

tff(c_303,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_339,plain,(
    ! [C_446,A_447,D_448,B_449] :
      ( C_446 = A_447
      | g1_pre_topc(C_446,D_448) != g1_pre_topc(A_447,B_449)
      | ~ m1_subset_1(B_449,k1_zfmisc_1(k1_zfmisc_1(A_447))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_347,plain,(
    ! [C_446,D_448] :
      ( u1_struct_0('#skF_4') = C_446
      | g1_pre_topc(C_446,D_448) != '#skF_5'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_339])).

tff(c_430,plain,(
    ! [C_452,D_453] :
      ( u1_struct_0('#skF_4') = C_452
      | g1_pre_topc(C_452,D_453) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_347])).

tff(c_440,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_430])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( m1_connsp_2('#skF_1'(A_24,B_25),A_24,B_25)
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1076,plain,(
    ! [C_479,A_480,B_481] :
      ( m1_subset_1(C_479,k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ m1_connsp_2(C_479,A_480,B_481)
      | ~ m1_subset_1(B_481,u1_struct_0(A_480))
      | ~ l1_pre_topc(A_480)
      | ~ v2_pre_topc(A_480)
      | v2_struct_0(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1627,plain,(
    ! [A_516,B_517] :
      ( m1_subset_1('#skF_1'(A_516,B_517),k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(B_517,u1_struct_0(A_516))
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516) ) ),
    inference(resolution,[status(thm)],[c_24,c_1076])).

tff(c_1633,plain,(
    ! [B_517] :
      ( m1_subset_1('#skF_1'('#skF_5',B_517),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_517,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_1627])).

tff(c_1636,plain,(
    ! [B_517] :
      ( m1_subset_1('#skF_1'('#skF_5',B_517),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_517,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107,c_440,c_1633])).

tff(c_1638,plain,(
    ! [B_518] :
      ( m1_subset_1('#skF_1'('#skF_5',B_518),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_518,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1636])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1643,plain,(
    ! [B_519] :
      ( r1_tarski('#skF_1'('#skF_5',B_519),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_519,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1638,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_549,plain,(
    ! [A_460,B_461] :
      ( m1_pre_topc(A_460,g1_pre_topc(u1_struct_0(B_461),u1_pre_topc(B_461)))
      | ~ m1_pre_topc(A_460,B_461)
      | ~ l1_pre_topc(B_461)
      | ~ l1_pre_topc(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_577,plain,(
    ! [A_460] :
      ( m1_pre_topc(A_460,'#skF_5')
      | ~ m1_pre_topc(A_460,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_549])).

tff(c_591,plain,(
    ! [A_460] :
      ( m1_pre_topc(A_460,'#skF_5')
      | ~ m1_pre_topc(A_460,'#skF_4')
      | ~ l1_pre_topc(A_460) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_577])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_76,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_463,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_462,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_50])).

tff(c_40,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_1340,plain,(
    ! [F_502,B_500,H_501,C_498,A_496,D_499,E_497] :
      ( r1_tmap_1(D_499,B_500,E_497,H_501)
      | ~ r1_tmap_1(C_498,B_500,k3_tmap_1(A_496,B_500,D_499,C_498,E_497),H_501)
      | ~ m1_connsp_2(F_502,D_499,H_501)
      | ~ r1_tarski(F_502,u1_struct_0(C_498))
      | ~ m1_subset_1(H_501,u1_struct_0(C_498))
      | ~ m1_subset_1(H_501,u1_struct_0(D_499))
      | ~ m1_subset_1(F_502,k1_zfmisc_1(u1_struct_0(D_499)))
      | ~ m1_pre_topc(C_498,D_499)
      | ~ m1_subset_1(E_497,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_499),u1_struct_0(B_500))))
      | ~ v1_funct_2(E_497,u1_struct_0(D_499),u1_struct_0(B_500))
      | ~ v1_funct_1(E_497)
      | ~ m1_pre_topc(D_499,A_496)
      | v2_struct_0(D_499)
      | ~ m1_pre_topc(C_498,A_496)
      | v2_struct_0(C_498)
      | ~ l1_pre_topc(B_500)
      | ~ v2_pre_topc(B_500)
      | v2_struct_0(B_500)
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1342,plain,(
    ! [F_502] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_502,'#skF_5','#skF_8')
      | ~ r1_tarski(F_502,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_502,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_1340])).

tff(c_1345,plain,(
    ! [F_502] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_502,'#skF_5','#skF_8')
      | ~ r1_tarski(F_502,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_502,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_463,c_440,c_462,c_440,c_440,c_44,c_440,c_44,c_1342])).

tff(c_1346,plain,(
    ! [F_502] :
      ( ~ m1_connsp_2(F_502,'#skF_5','#skF_8')
      | ~ r1_tarski(F_502,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_502,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_76,c_1345])).

tff(c_1416,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1346])).

tff(c_1419,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_591,c_1416])).

tff(c_1422,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1419])).

tff(c_1425,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1422])).

tff(c_1429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1425])).

tff(c_1594,plain,(
    ! [F_513] :
      ( ~ m1_connsp_2(F_513,'#skF_5','#skF_8')
      | ~ r1_tarski(F_513,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_513,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1346])).

tff(c_1599,plain,(
    ! [A_1] :
      ( ~ m1_connsp_2(A_1,'#skF_5','#skF_8')
      | ~ r1_tarski(A_1,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1594])).

tff(c_1648,plain,(
    ! [B_520] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_520),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_520,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1643,c_1599])).

tff(c_1652,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1648])).

tff(c_1655,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107,c_44,c_440,c_44,c_1652])).

tff(c_1657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:29:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.64  
% 3.88/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.64  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.88/1.64  
% 3.88/1.64  %Foreground sorts:
% 3.88/1.64  
% 3.88/1.64  
% 3.88/1.64  %Background operators:
% 3.88/1.64  
% 3.88/1.64  
% 3.88/1.64  %Foreground operators:
% 3.88/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.88/1.64  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.88/1.64  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.88/1.64  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.88/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.64  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.88/1.64  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.88/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.88/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.88/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.88/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.88/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.64  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.88/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.88/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.64  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.88/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.88/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.88/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.64  
% 3.88/1.66  tff(f_228, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.88/1.66  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.88/1.66  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.88/1.66  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 3.88/1.66  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.88/1.66  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.88/1.66  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.88/1.66  tff(f_99, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.88/1.66  tff(f_87, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.88/1.66  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.88/1.66  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.88/1.66  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.88/1.66  tff(f_179, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.88/1.66  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_119, plain, (![B_422, A_423]: (v2_pre_topc(B_422) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.88/1.66  tff(c_128, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_119])).
% 3.88/1.66  tff(c_135, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_128])).
% 3.88/1.66  tff(c_91, plain, (![B_416, A_417]: (l1_pre_topc(B_416) | ~m1_pre_topc(B_416, A_417) | ~l1_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.88/1.66  tff(c_100, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_91])).
% 3.88/1.66  tff(c_107, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_100])).
% 3.88/1.66  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_156, plain, (![B_425, A_426]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_425), u1_pre_topc(B_425))) | ~m1_pre_topc(B_425, A_426) | ~l1_pre_topc(A_426))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.88/1.66  tff(c_160, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_156])).
% 3.88/1.66  tff(c_166, plain, (v1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_48, c_160])).
% 3.88/1.66  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.66  tff(c_97, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_91])).
% 3.88/1.66  tff(c_104, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97])).
% 3.88/1.66  tff(c_12, plain, (![A_10]: (m1_subset_1(u1_pre_topc(A_10), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.88/1.66  tff(c_256, plain, (![D_434, B_435, C_436, A_437]: (D_434=B_435 | g1_pre_topc(C_436, D_434)!=g1_pre_topc(A_437, B_435) | ~m1_subset_1(B_435, k1_zfmisc_1(k1_zfmisc_1(A_437))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.88/1.66  tff(c_264, plain, (![D_434, C_436]: (u1_pre_topc('#skF_4')=D_434 | g1_pre_topc(C_436, D_434)!='#skF_5' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_256])).
% 3.88/1.66  tff(c_291, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_264])).
% 3.88/1.66  tff(c_294, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_291])).
% 3.88/1.66  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_294])).
% 3.88/1.66  tff(c_304, plain, (![D_443, C_444]: (u1_pre_topc('#skF_4')=D_443 | g1_pre_topc(C_444, D_443)!='#skF_5')), inference(splitRight, [status(thm)], [c_264])).
% 3.88/1.66  tff(c_318, plain, (![A_445]: (u1_pre_topc(A_445)=u1_pre_topc('#skF_4') | A_445!='#skF_5' | ~v1_pre_topc(A_445) | ~l1_pre_topc(A_445))), inference(superposition, [status(thm), theory('equality')], [c_6, c_304])).
% 3.88/1.66  tff(c_327, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_166, c_318])).
% 3.88/1.66  tff(c_334, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_327])).
% 3.88/1.66  tff(c_364, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))='#skF_5' | ~v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_334, c_6])).
% 3.88/1.66  tff(c_378, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_166, c_364])).
% 3.88/1.66  tff(c_303, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_264])).
% 3.88/1.66  tff(c_339, plain, (![C_446, A_447, D_448, B_449]: (C_446=A_447 | g1_pre_topc(C_446, D_448)!=g1_pre_topc(A_447, B_449) | ~m1_subset_1(B_449, k1_zfmisc_1(k1_zfmisc_1(A_447))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.88/1.66  tff(c_347, plain, (![C_446, D_448]: (u1_struct_0('#skF_4')=C_446 | g1_pre_topc(C_446, D_448)!='#skF_5' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_339])).
% 3.88/1.66  tff(c_430, plain, (![C_452, D_453]: (u1_struct_0('#skF_4')=C_452 | g1_pre_topc(C_452, D_453)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_347])).
% 3.88/1.66  tff(c_440, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_378, c_430])).
% 3.88/1.66  tff(c_24, plain, (![A_24, B_25]: (m1_connsp_2('#skF_1'(A_24, B_25), A_24, B_25) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.88/1.66  tff(c_1076, plain, (![C_479, A_480, B_481]: (m1_subset_1(C_479, k1_zfmisc_1(u1_struct_0(A_480))) | ~m1_connsp_2(C_479, A_480, B_481) | ~m1_subset_1(B_481, u1_struct_0(A_480)) | ~l1_pre_topc(A_480) | ~v2_pre_topc(A_480) | v2_struct_0(A_480))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.88/1.66  tff(c_1627, plain, (![A_516, B_517]: (m1_subset_1('#skF_1'(A_516, B_517), k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(B_517, u1_struct_0(A_516)) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516))), inference(resolution, [status(thm)], [c_24, c_1076])).
% 3.88/1.66  tff(c_1633, plain, (![B_517]: (m1_subset_1('#skF_1'('#skF_5', B_517), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_517, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_440, c_1627])).
% 3.88/1.66  tff(c_1636, plain, (![B_517]: (m1_subset_1('#skF_1'('#skF_5', B_517), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_517, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107, c_440, c_1633])).
% 3.88/1.66  tff(c_1638, plain, (![B_518]: (m1_subset_1('#skF_1'('#skF_5', B_518), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_518, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1636])).
% 3.88/1.66  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.66  tff(c_1643, plain, (![B_519]: (r1_tarski('#skF_1'('#skF_5', B_519), u1_struct_0('#skF_4')) | ~m1_subset_1(B_519, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1638, c_2])).
% 3.88/1.66  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.66  tff(c_30, plain, (![A_30]: (m1_pre_topc(A_30, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.88/1.66  tff(c_549, plain, (![A_460, B_461]: (m1_pre_topc(A_460, g1_pre_topc(u1_struct_0(B_461), u1_pre_topc(B_461))) | ~m1_pre_topc(A_460, B_461) | ~l1_pre_topc(B_461) | ~l1_pre_topc(A_460))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.88/1.66  tff(c_577, plain, (![A_460]: (m1_pre_topc(A_460, '#skF_5') | ~m1_pre_topc(A_460, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_460))), inference(superposition, [status(thm), theory('equality')], [c_48, c_549])).
% 3.88/1.66  tff(c_591, plain, (![A_460]: (m1_pre_topc(A_460, '#skF_5') | ~m1_pre_topc(A_460, '#skF_4') | ~l1_pre_topc(A_460))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_577])).
% 3.88/1.66  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_38, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 3.88/1.66  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_463, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_52])).
% 3.88/1.66  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_462, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_50])).
% 3.88/1.66  tff(c_40, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.88/1.66  tff(c_1340, plain, (![F_502, B_500, H_501, C_498, A_496, D_499, E_497]: (r1_tmap_1(D_499, B_500, E_497, H_501) | ~r1_tmap_1(C_498, B_500, k3_tmap_1(A_496, B_500, D_499, C_498, E_497), H_501) | ~m1_connsp_2(F_502, D_499, H_501) | ~r1_tarski(F_502, u1_struct_0(C_498)) | ~m1_subset_1(H_501, u1_struct_0(C_498)) | ~m1_subset_1(H_501, u1_struct_0(D_499)) | ~m1_subset_1(F_502, k1_zfmisc_1(u1_struct_0(D_499))) | ~m1_pre_topc(C_498, D_499) | ~m1_subset_1(E_497, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_499), u1_struct_0(B_500)))) | ~v1_funct_2(E_497, u1_struct_0(D_499), u1_struct_0(B_500)) | ~v1_funct_1(E_497) | ~m1_pre_topc(D_499, A_496) | v2_struct_0(D_499) | ~m1_pre_topc(C_498, A_496) | v2_struct_0(C_498) | ~l1_pre_topc(B_500) | ~v2_pre_topc(B_500) | v2_struct_0(B_500) | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.88/1.66  tff(c_1342, plain, (![F_502]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_502, '#skF_5', '#skF_8') | ~r1_tarski(F_502, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_502, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1340])).
% 3.88/1.66  tff(c_1345, plain, (![F_502]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_502, '#skF_5', '#skF_8') | ~r1_tarski(F_502, u1_struct_0('#skF_4')) | ~m1_subset_1(F_502, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_463, c_440, c_462, c_440, c_440, c_44, c_440, c_44, c_1342])).
% 3.88/1.66  tff(c_1346, plain, (![F_502]: (~m1_connsp_2(F_502, '#skF_5', '#skF_8') | ~r1_tarski(F_502, u1_struct_0('#skF_4')) | ~m1_subset_1(F_502, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_76, c_1345])).
% 3.88/1.66  tff(c_1416, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1346])).
% 3.88/1.66  tff(c_1419, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_591, c_1416])).
% 3.88/1.66  tff(c_1422, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1419])).
% 3.88/1.66  tff(c_1425, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1422])).
% 3.88/1.66  tff(c_1429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1425])).
% 3.88/1.66  tff(c_1594, plain, (![F_513]: (~m1_connsp_2(F_513, '#skF_5', '#skF_8') | ~r1_tarski(F_513, u1_struct_0('#skF_4')) | ~m1_subset_1(F_513, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1346])).
% 3.88/1.66  tff(c_1599, plain, (![A_1]: (~m1_connsp_2(A_1, '#skF_5', '#skF_8') | ~r1_tarski(A_1, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_1594])).
% 3.88/1.66  tff(c_1648, plain, (![B_520]: (~m1_connsp_2('#skF_1'('#skF_5', B_520), '#skF_5', '#skF_8') | ~m1_subset_1(B_520, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1643, c_1599])).
% 3.88/1.66  tff(c_1652, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1648])).
% 3.88/1.66  tff(c_1655, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107, c_44, c_440, c_44, c_1652])).
% 3.88/1.66  tff(c_1657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1655])).
% 3.88/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.66  
% 3.88/1.66  Inference rules
% 3.88/1.66  ----------------------
% 3.88/1.66  #Ref     : 4
% 3.88/1.66  #Sup     : 315
% 3.88/1.66  #Fact    : 0
% 3.88/1.66  #Define  : 0
% 3.88/1.66  #Split   : 5
% 3.88/1.66  #Chain   : 0
% 3.88/1.66  #Close   : 0
% 3.88/1.66  
% 3.88/1.66  Ordering : KBO
% 3.88/1.66  
% 3.88/1.66  Simplification rules
% 3.88/1.66  ----------------------
% 3.88/1.66  #Subsume      : 71
% 3.88/1.66  #Demod        : 619
% 3.88/1.66  #Tautology    : 158
% 3.88/1.66  #SimpNegUnit  : 3
% 3.88/1.66  #BackRed      : 10
% 3.88/1.66  
% 3.88/1.66  #Partial instantiations: 0
% 3.88/1.66  #Strategies tried      : 1
% 3.88/1.66  
% 3.88/1.66  Timing (in seconds)
% 3.88/1.66  ----------------------
% 3.88/1.66  Preprocessing        : 0.41
% 3.88/1.66  Parsing              : 0.20
% 3.88/1.66  CNF conversion       : 0.06
% 3.88/1.66  Main loop            : 0.48
% 3.88/1.66  Inferencing          : 0.15
% 3.88/1.66  Reduction            : 0.18
% 3.88/1.66  Demodulation         : 0.13
% 3.88/1.66  BG Simplification    : 0.03
% 3.88/1.66  Subsumption          : 0.09
% 3.88/1.66  Abstraction          : 0.02
% 3.88/1.66  MUC search           : 0.00
% 3.88/1.66  Cooper               : 0.00
% 3.88/1.66  Total                : 0.93
% 3.88/1.66  Index Insertion      : 0.00
% 3.88/1.66  Index Deletion       : 0.00
% 3.88/1.66  Index Matching       : 0.00
% 3.88/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
