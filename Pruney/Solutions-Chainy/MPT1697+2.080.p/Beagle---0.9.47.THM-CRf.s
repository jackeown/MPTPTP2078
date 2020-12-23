%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:22 EST 2020

% Result     : Theorem 21.94s
% Output     : CNFRefutation 22.05s
% Verified   : 
% Statistics : Number of formulae       :  233 (1624 expanded)
%              Number of leaves         :   43 ( 605 expanded)
%              Depth                    :   23
%              Number of atoms          :  844 (8520 expanded)
%              Number of equality atoms :  162 (1587 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_212,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(A)) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ( r1_subset_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_170,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_136,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_42,plain,(
    ! [B_161,C_162,A_160,E_164,F_165,D_163] :
      ( v1_funct_2(k1_tmap_1(A_160,B_161,C_162,D_163,E_164,F_165),k4_subset_1(A_160,C_162,D_163),B_161)
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(D_163,B_161)))
      | ~ v1_funct_2(F_165,D_163,B_161)
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(C_162,B_161)))
      | ~ v1_funct_2(E_164,C_162,B_161)
      | ~ v1_funct_1(E_164)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(A_160))
      | v1_xboole_0(D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(A_160))
      | v1_xboole_0(C_162)
      | v1_xboole_0(B_161)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_16,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_182,plain,(
    ! [B_237,A_238] :
      ( v1_relat_1(B_237)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_238))
      | ~ v1_relat_1(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_185,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_182])).

tff(c_197,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_185])).

tff(c_82,plain,(
    ! [B_228,A_229] : k3_xboole_0(B_228,A_229) = k3_xboole_0(A_229,B_228) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [A_229] : k3_xboole_0(k1_xboole_0,A_229) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_5306,plain,(
    ! [A_416,B_417] :
      ( r1_xboole_0(A_416,B_417)
      | ~ r1_subset_1(A_416,B_417)
      | v1_xboole_0(B_417)
      | v1_xboole_0(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5327,plain,(
    ! [B_420,A_421] :
      ( r1_xboole_0(B_420,A_421)
      | ~ r1_subset_1(A_421,B_420)
      | v1_xboole_0(B_420)
      | v1_xboole_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_5306,c_8])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_subset_1(A_24,B_25)
      | ~ r1_xboole_0(A_24,B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5390,plain,(
    ! [B_429,A_430] :
      ( r1_subset_1(B_429,A_430)
      | ~ r1_subset_1(A_430,B_429)
      | v1_xboole_0(B_429)
      | v1_xboole_0(A_430) ) ),
    inference(resolution,[status(thm)],[c_5327,c_24])).

tff(c_5392,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_5390])).

tff(c_5395,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_5392])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | ~ r1_subset_1(A_24,B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5272,plain,(
    ! [C_411,A_412,B_413] :
      ( v4_relat_1(C_411,A_412)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5279,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_5272])).

tff(c_5281,plain,(
    ! [B_414,A_415] :
      ( k7_relat_1(B_414,A_415) = B_414
      | ~ v4_relat_1(B_414,A_415)
      | ~ v1_relat_1(B_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5287,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5279,c_5281])).

tff(c_5293,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_5287])).

tff(c_5401,plain,(
    ! [C_431,A_432,B_433] :
      ( k7_relat_1(k7_relat_1(C_431,A_432),B_433) = k1_xboole_0
      | ~ r1_xboole_0(A_432,B_433)
      | ~ v1_relat_1(C_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5416,plain,(
    ! [B_433] :
      ( k7_relat_1('#skF_6',B_433) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_433)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5293,c_5401])).

tff(c_5426,plain,(
    ! [B_434] :
      ( k7_relat_1('#skF_6',B_434) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_5416])).

tff(c_5434,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_6',B_25) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_5426])).

tff(c_5718,plain,(
    ! [B_448] :
      ( k7_relat_1('#skF_6',B_448) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_448)
      | v1_xboole_0(B_448) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5434])).

tff(c_5721,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5395,c_5718])).

tff(c_5724,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5721])).

tff(c_18,plain,(
    ! [C_18,A_16,B_17] :
      ( k3_xboole_0(k7_relat_1(C_18,A_16),k7_relat_1(C_18,B_17)) = k7_relat_1(C_18,k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5734,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',k3_xboole_0(A_16,'#skF_3')) = k3_xboole_0(k7_relat_1('#skF_6',A_16),k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5724,c_18])).

tff(c_5748,plain,(
    ! [A_16] : k7_relat_1('#skF_6',k3_xboole_0(A_16,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_98,c_2,c_5734])).

tff(c_188,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_182])).

tff(c_200,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_188])).

tff(c_5313,plain,(
    ! [B_417,A_416] :
      ( r1_xboole_0(B_417,A_416)
      | ~ r1_subset_1(A_416,B_417)
      | v1_xboole_0(B_417)
      | v1_xboole_0(A_416) ) ),
    inference(resolution,[status(thm)],[c_5306,c_8])).

tff(c_5280,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_5272])).

tff(c_5284,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5280,c_5281])).

tff(c_5290,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_5284])).

tff(c_5419,plain,(
    ! [B_433] :
      ( k7_relat_1('#skF_5',B_433) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_433)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5290,c_5401])).

tff(c_5451,plain,(
    ! [B_435] :
      ( k7_relat_1('#skF_5',B_435) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_5419])).

tff(c_5455,plain,(
    ! [A_416] :
      ( k7_relat_1('#skF_5',A_416) = k1_xboole_0
      | ~ r1_subset_1(A_416,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_416) ) ),
    inference(resolution,[status(thm)],[c_5313,c_5451])).

tff(c_5558,plain,(
    ! [A_440] :
      ( k7_relat_1('#skF_5',A_440) = k1_xboole_0
      | ~ r1_subset_1(A_440,'#skF_3')
      | v1_xboole_0(A_440) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5455])).

tff(c_5561,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5395,c_5558])).

tff(c_5564,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5561])).

tff(c_5568,plain,(
    ! [B_17] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_17)) = k3_xboole_0(k1_xboole_0,k7_relat_1('#skF_5',B_17))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5564,c_18])).

tff(c_5578,plain,(
    ! [B_17] : k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_17)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_98,c_5568])).

tff(c_5339,plain,(
    ! [A_422,B_423,C_424] :
      ( k9_subset_1(A_422,B_423,C_424) = k3_xboole_0(B_423,C_424)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(A_422)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5351,plain,(
    ! [B_423] : k9_subset_1('#skF_1',B_423,'#skF_4') = k3_xboole_0(B_423,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_5339])).

tff(c_6214,plain,(
    ! [D_463,C_461,A_465,B_462,E_464,F_466] :
      ( v1_funct_1(k1_tmap_1(A_465,B_462,C_461,D_463,E_464,F_466))
      | ~ m1_subset_1(F_466,k1_zfmisc_1(k2_zfmisc_1(D_463,B_462)))
      | ~ v1_funct_2(F_466,D_463,B_462)
      | ~ v1_funct_1(F_466)
      | ~ m1_subset_1(E_464,k1_zfmisc_1(k2_zfmisc_1(C_461,B_462)))
      | ~ v1_funct_2(E_464,C_461,B_462)
      | ~ v1_funct_1(E_464)
      | ~ m1_subset_1(D_463,k1_zfmisc_1(A_465))
      | v1_xboole_0(D_463)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(A_465))
      | v1_xboole_0(C_461)
      | v1_xboole_0(B_462)
      | v1_xboole_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_6216,plain,(
    ! [A_465,C_461,E_464] :
      ( v1_funct_1(k1_tmap_1(A_465,'#skF_2',C_461,'#skF_4',E_464,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_464,k1_zfmisc_1(k2_zfmisc_1(C_461,'#skF_2')))
      | ~ v1_funct_2(E_464,C_461,'#skF_2')
      | ~ v1_funct_1(E_464)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_465))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_461,k1_zfmisc_1(A_465))
      | v1_xboole_0(C_461)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_465) ) ),
    inference(resolution,[status(thm)],[c_48,c_6214])).

tff(c_6221,plain,(
    ! [A_465,C_461,E_464] :
      ( v1_funct_1(k1_tmap_1(A_465,'#skF_2',C_461,'#skF_4',E_464,'#skF_6'))
      | ~ m1_subset_1(E_464,k1_zfmisc_1(k2_zfmisc_1(C_461,'#skF_2')))
      | ~ v1_funct_2(E_464,C_461,'#skF_2')
      | ~ v1_funct_1(E_464)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_465))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_461,k1_zfmisc_1(A_465))
      | v1_xboole_0(C_461)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_465) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_6216])).

tff(c_7323,plain,(
    ! [A_511,C_512,E_513] :
      ( v1_funct_1(k1_tmap_1(A_511,'#skF_2',C_512,'#skF_4',E_513,'#skF_6'))
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(C_512,'#skF_2')))
      | ~ v1_funct_2(E_513,C_512,'#skF_2')
      | ~ v1_funct_1(E_513)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_511))
      | ~ m1_subset_1(C_512,k1_zfmisc_1(A_511))
      | v1_xboole_0(C_512)
      | v1_xboole_0(A_511) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_6221])).

tff(c_7330,plain,(
    ! [A_511] :
      ( v1_funct_1(k1_tmap_1(A_511,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_511))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_511))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_511) ) ),
    inference(resolution,[status(thm)],[c_54,c_7323])).

tff(c_7340,plain,(
    ! [A_511] :
      ( v1_funct_1(k1_tmap_1(A_511,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_511))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_511))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_7330])).

tff(c_8757,plain,(
    ! [A_539] :
      ( v1_funct_1(k1_tmap_1(A_539,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_539))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_539))
      | v1_xboole_0(A_539) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7340])).

tff(c_8760,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_8757])).

tff(c_8763,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8760])).

tff(c_8764,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_8763])).

tff(c_5680,plain,(
    ! [A_443,B_444,C_445,D_446] :
      ( k2_partfun1(A_443,B_444,C_445,D_446) = k7_relat_1(C_445,D_446)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444)))
      | ~ v1_funct_1(C_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5684,plain,(
    ! [D_446] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_446) = k7_relat_1('#skF_5',D_446)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_5680])).

tff(c_5690,plain,(
    ! [D_446] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_446) = k7_relat_1('#skF_5',D_446) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5684])).

tff(c_5682,plain,(
    ! [D_446] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_446) = k7_relat_1('#skF_6',D_446)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_5680])).

tff(c_5687,plain,(
    ! [D_446] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_446) = k7_relat_1('#skF_6',D_446) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5682])).

tff(c_40,plain,(
    ! [B_161,C_162,A_160,E_164,F_165,D_163] :
      ( m1_subset_1(k1_tmap_1(A_160,B_161,C_162,D_163,E_164,F_165),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160,C_162,D_163),B_161)))
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(D_163,B_161)))
      | ~ v1_funct_2(F_165,D_163,B_161)
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(C_162,B_161)))
      | ~ v1_funct_2(E_164,C_162,B_161)
      | ~ v1_funct_1(E_164)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(A_160))
      | v1_xboole_0(D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(A_160))
      | v1_xboole_0(C_162)
      | v1_xboole_0(B_161)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_6959,plain,(
    ! [D_500,B_497,C_499,E_496,A_495,F_498] :
      ( k2_partfun1(k4_subset_1(A_495,C_499,D_500),B_497,k1_tmap_1(A_495,B_497,C_499,D_500,E_496,F_498),D_500) = F_498
      | ~ m1_subset_1(k1_tmap_1(A_495,B_497,C_499,D_500,E_496,F_498),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_495,C_499,D_500),B_497)))
      | ~ v1_funct_2(k1_tmap_1(A_495,B_497,C_499,D_500,E_496,F_498),k4_subset_1(A_495,C_499,D_500),B_497)
      | ~ v1_funct_1(k1_tmap_1(A_495,B_497,C_499,D_500,E_496,F_498))
      | k2_partfun1(D_500,B_497,F_498,k9_subset_1(A_495,C_499,D_500)) != k2_partfun1(C_499,B_497,E_496,k9_subset_1(A_495,C_499,D_500))
      | ~ m1_subset_1(F_498,k1_zfmisc_1(k2_zfmisc_1(D_500,B_497)))
      | ~ v1_funct_2(F_498,D_500,B_497)
      | ~ v1_funct_1(F_498)
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(C_499,B_497)))
      | ~ v1_funct_2(E_496,C_499,B_497)
      | ~ v1_funct_1(E_496)
      | ~ m1_subset_1(D_500,k1_zfmisc_1(A_495))
      | v1_xboole_0(D_500)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(A_495))
      | v1_xboole_0(C_499)
      | v1_xboole_0(B_497)
      | v1_xboole_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16524,plain,(
    ! [F_691,A_690,D_688,E_689,B_687,C_686] :
      ( k2_partfun1(k4_subset_1(A_690,C_686,D_688),B_687,k1_tmap_1(A_690,B_687,C_686,D_688,E_689,F_691),D_688) = F_691
      | ~ v1_funct_2(k1_tmap_1(A_690,B_687,C_686,D_688,E_689,F_691),k4_subset_1(A_690,C_686,D_688),B_687)
      | ~ v1_funct_1(k1_tmap_1(A_690,B_687,C_686,D_688,E_689,F_691))
      | k2_partfun1(D_688,B_687,F_691,k9_subset_1(A_690,C_686,D_688)) != k2_partfun1(C_686,B_687,E_689,k9_subset_1(A_690,C_686,D_688))
      | ~ m1_subset_1(F_691,k1_zfmisc_1(k2_zfmisc_1(D_688,B_687)))
      | ~ v1_funct_2(F_691,D_688,B_687)
      | ~ v1_funct_1(F_691)
      | ~ m1_subset_1(E_689,k1_zfmisc_1(k2_zfmisc_1(C_686,B_687)))
      | ~ v1_funct_2(E_689,C_686,B_687)
      | ~ v1_funct_1(E_689)
      | ~ m1_subset_1(D_688,k1_zfmisc_1(A_690))
      | v1_xboole_0(D_688)
      | ~ m1_subset_1(C_686,k1_zfmisc_1(A_690))
      | v1_xboole_0(C_686)
      | v1_xboole_0(B_687)
      | v1_xboole_0(A_690) ) ),
    inference(resolution,[status(thm)],[c_40,c_6959])).

tff(c_40938,plain,(
    ! [C_926,F_931,D_928,A_930,E_929,B_927] :
      ( k2_partfun1(k4_subset_1(A_930,C_926,D_928),B_927,k1_tmap_1(A_930,B_927,C_926,D_928,E_929,F_931),D_928) = F_931
      | ~ v1_funct_1(k1_tmap_1(A_930,B_927,C_926,D_928,E_929,F_931))
      | k2_partfun1(D_928,B_927,F_931,k9_subset_1(A_930,C_926,D_928)) != k2_partfun1(C_926,B_927,E_929,k9_subset_1(A_930,C_926,D_928))
      | ~ m1_subset_1(F_931,k1_zfmisc_1(k2_zfmisc_1(D_928,B_927)))
      | ~ v1_funct_2(F_931,D_928,B_927)
      | ~ v1_funct_1(F_931)
      | ~ m1_subset_1(E_929,k1_zfmisc_1(k2_zfmisc_1(C_926,B_927)))
      | ~ v1_funct_2(E_929,C_926,B_927)
      | ~ v1_funct_1(E_929)
      | ~ m1_subset_1(D_928,k1_zfmisc_1(A_930))
      | v1_xboole_0(D_928)
      | ~ m1_subset_1(C_926,k1_zfmisc_1(A_930))
      | v1_xboole_0(C_926)
      | v1_xboole_0(B_927)
      | v1_xboole_0(A_930) ) ),
    inference(resolution,[status(thm)],[c_42,c_16524])).

tff(c_40942,plain,(
    ! [A_930,C_926,E_929] :
      ( k2_partfun1(k4_subset_1(A_930,C_926,'#skF_4'),'#skF_2',k1_tmap_1(A_930,'#skF_2',C_926,'#skF_4',E_929,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_930,'#skF_2',C_926,'#skF_4',E_929,'#skF_6'))
      | k2_partfun1(C_926,'#skF_2',E_929,k9_subset_1(A_930,C_926,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_930,C_926,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_929,k1_zfmisc_1(k2_zfmisc_1(C_926,'#skF_2')))
      | ~ v1_funct_2(E_929,C_926,'#skF_2')
      | ~ v1_funct_1(E_929)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_930))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_926,k1_zfmisc_1(A_930))
      | v1_xboole_0(C_926)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_930) ) ),
    inference(resolution,[status(thm)],[c_48,c_40938])).

tff(c_40948,plain,(
    ! [A_930,C_926,E_929] :
      ( k2_partfun1(k4_subset_1(A_930,C_926,'#skF_4'),'#skF_2',k1_tmap_1(A_930,'#skF_2',C_926,'#skF_4',E_929,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_930,'#skF_2',C_926,'#skF_4',E_929,'#skF_6'))
      | k2_partfun1(C_926,'#skF_2',E_929,k9_subset_1(A_930,C_926,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_930,C_926,'#skF_4'))
      | ~ m1_subset_1(E_929,k1_zfmisc_1(k2_zfmisc_1(C_926,'#skF_2')))
      | ~ v1_funct_2(E_929,C_926,'#skF_2')
      | ~ v1_funct_1(E_929)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_930))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_926,k1_zfmisc_1(A_930))
      | v1_xboole_0(C_926)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_930) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5687,c_40942])).

tff(c_62599,plain,(
    ! [A_1096,C_1097,E_1098] :
      ( k2_partfun1(k4_subset_1(A_1096,C_1097,'#skF_4'),'#skF_2',k1_tmap_1(A_1096,'#skF_2',C_1097,'#skF_4',E_1098,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1096,'#skF_2',C_1097,'#skF_4',E_1098,'#skF_6'))
      | k2_partfun1(C_1097,'#skF_2',E_1098,k9_subset_1(A_1096,C_1097,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1096,C_1097,'#skF_4'))
      | ~ m1_subset_1(E_1098,k1_zfmisc_1(k2_zfmisc_1(C_1097,'#skF_2')))
      | ~ v1_funct_2(E_1098,C_1097,'#skF_2')
      | ~ v1_funct_1(E_1098)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1096))
      | ~ m1_subset_1(C_1097,k1_zfmisc_1(A_1096))
      | v1_xboole_0(C_1097)
      | v1_xboole_0(A_1096) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_40948])).

tff(c_62606,plain,(
    ! [A_1096] :
      ( k2_partfun1(k4_subset_1(A_1096,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1096,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1096,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1096,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1096,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1096))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1096))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1096) ) ),
    inference(resolution,[status(thm)],[c_54,c_62599])).

tff(c_62616,plain,(
    ! [A_1096] :
      ( k2_partfun1(k4_subset_1(A_1096,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1096,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1096,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1096,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1096,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1096))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1096))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1096) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_5690,c_62606])).

tff(c_65822,plain,(
    ! [A_1119] :
      ( k2_partfun1(k4_subset_1(A_1119,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1119,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1119,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1119,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1119,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1119))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1119))
      | v1_xboole_0(A_1119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62616])).

tff(c_227,plain,(
    ! [C_244,A_245,B_246] :
      ( v4_relat_1(C_244,A_245)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_235,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_227])).

tff(c_236,plain,(
    ! [B_247,A_248] :
      ( k7_relat_1(B_247,A_248) = B_247
      | ~ v4_relat_1(B_247,A_248)
      | ~ v1_relat_1(B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_239,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_235,c_236])).

tff(c_245,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_239])).

tff(c_290,plain,(
    ! [C_255,A_256,B_257] :
      ( k7_relat_1(k7_relat_1(C_255,A_256),B_257) = k1_xboole_0
      | ~ r1_xboole_0(A_256,B_257)
      | ~ v1_relat_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_308,plain,(
    ! [B_257] :
      ( k7_relat_1('#skF_5',B_257) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_257)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_290])).

tff(c_340,plain,(
    ! [B_259] :
      ( k7_relat_1('#skF_5',B_259) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_308])).

tff(c_348,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_5',B_25) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_340])).

tff(c_901,plain,(
    ! [B_287] :
      ( k7_relat_1('#skF_5',B_287) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_287)
      | v1_xboole_0(B_287) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_348])).

tff(c_904,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_901])).

tff(c_907,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_904])).

tff(c_911,plain,(
    ! [B_17] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_17)) = k3_xboole_0(k1_xboole_0,k7_relat_1('#skF_5',B_17))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_18])).

tff(c_933,plain,(
    ! [B_17] : k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_17)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_98,c_911])).

tff(c_859,plain,(
    ! [A_281,B_282,C_283,D_284] :
      ( k2_partfun1(A_281,B_282,C_283,D_284) = k7_relat_1(C_283,D_284)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_1(C_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_863,plain,(
    ! [D_284] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_284) = k7_relat_1('#skF_5',D_284)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_859])).

tff(c_869,plain,(
    ! [D_284] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_284) = k7_relat_1('#skF_5',D_284) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_863])).

tff(c_257,plain,(
    ! [A_249,B_250] :
      ( r1_xboole_0(A_249,B_250)
      | ~ r1_subset_1(A_249,B_250)
      | v1_xboole_0(B_250)
      | v1_xboole_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_264,plain,(
    ! [B_250,A_249] :
      ( r1_xboole_0(B_250,A_249)
      | ~ r1_subset_1(A_249,B_250)
      | v1_xboole_0(B_250)
      | v1_xboole_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_257,c_8])).

tff(c_234,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_227])).

tff(c_242,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_234,c_236])).

tff(c_248,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_242])).

tff(c_305,plain,(
    ! [B_257] :
      ( k7_relat_1('#skF_6',B_257) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_257)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_290])).

tff(c_315,plain,(
    ! [B_258] :
      ( k7_relat_1('#skF_6',B_258) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_305])).

tff(c_319,plain,(
    ! [A_249] :
      ( k7_relat_1('#skF_6',A_249) = k1_xboole_0
      | ~ r1_subset_1(A_249,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_264,c_315])).

tff(c_515,plain,(
    ! [A_272] :
      ( k7_relat_1('#skF_6',A_272) = k1_xboole_0
      | ~ r1_subset_1(A_272,'#skF_4')
      | v1_xboole_0(A_272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_319])).

tff(c_518,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_515])).

tff(c_521,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_518])).

tff(c_619,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',k3_xboole_0(A_16,'#skF_3')) = k3_xboole_0(k7_relat_1('#skF_6',A_16),k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_18])).

tff(c_640,plain,(
    ! [A_16] : k7_relat_1('#skF_6',k3_xboole_0(A_16,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_10,c_619])).

tff(c_861,plain,(
    ! [D_284] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_284) = k7_relat_1('#skF_6',D_284)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_859])).

tff(c_866,plain,(
    ! [D_284] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_284) = k7_relat_1('#skF_6',D_284) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_861])).

tff(c_408,plain,(
    ! [A_263,B_264,C_265] :
      ( k9_subset_1(A_263,B_264,C_265) = k3_xboole_0(B_264,C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(A_263)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_420,plain,(
    ! [B_264] : k9_subset_1('#skF_1',B_264,'#skF_4') = k3_xboole_0(B_264,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_408])).

tff(c_46,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_212,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_430,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_420,c_212])).

tff(c_431,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_430])).

tff(c_5255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_869,c_640,c_866,c_431])).

tff(c_5256,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5883,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5256])).

tff(c_65833,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65822,c_5883])).

tff(c_65847,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_5748,c_5578,c_2,c_5351,c_2,c_5351,c_8764,c_65833])).

tff(c_65849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_65847])).

tff(c_65850,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5256])).

tff(c_5731,plain,(
    ! [B_17] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_17)) = k3_xboole_0(k1_xboole_0,k7_relat_1('#skF_6',B_17))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5724,c_18])).

tff(c_5754,plain,(
    ! [B_449] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_449)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_98,c_5731])).

tff(c_5784,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_5754])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68973,plain,(
    ! [A_1215,B_1216] :
      ( k3_xboole_0(A_1215,B_1216) = k1_xboole_0
      | ~ r1_subset_1(A_1215,B_1216)
      | v1_xboole_0(B_1216)
      | v1_xboole_0(A_1215) ) ),
    inference(resolution,[status(thm)],[c_5306,c_4])).

tff(c_68982,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_68973])).

tff(c_68988,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_68982])).

tff(c_68989,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_68988])).

tff(c_166,plain,(
    ! [A_233,B_234] :
      ( r1_xboole_0(A_233,B_234)
      | k3_xboole_0(A_233,B_234) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [B_235,A_236] :
      ( r1_xboole_0(B_235,A_236)
      | k3_xboole_0(A_236,B_235) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_166,c_8])).

tff(c_180,plain,(
    ! [B_235,A_236] :
      ( k3_xboole_0(B_235,A_236) = k1_xboole_0
      | k3_xboole_0(A_236,B_235) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_69057,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68989,c_180])).

tff(c_5584,plain,(
    ! [B_441] : k7_relat_1('#skF_5',k3_xboole_0('#skF_4',B_441)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_98,c_5568])).

tff(c_5608,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_5584])).

tff(c_66493,plain,(
    ! [F_1143,B_1139,D_1140,E_1141,A_1142,C_1138] :
      ( v1_funct_1(k1_tmap_1(A_1142,B_1139,C_1138,D_1140,E_1141,F_1143))
      | ~ m1_subset_1(F_1143,k1_zfmisc_1(k2_zfmisc_1(D_1140,B_1139)))
      | ~ v1_funct_2(F_1143,D_1140,B_1139)
      | ~ v1_funct_1(F_1143)
      | ~ m1_subset_1(E_1141,k1_zfmisc_1(k2_zfmisc_1(C_1138,B_1139)))
      | ~ v1_funct_2(E_1141,C_1138,B_1139)
      | ~ v1_funct_1(E_1141)
      | ~ m1_subset_1(D_1140,k1_zfmisc_1(A_1142))
      | v1_xboole_0(D_1140)
      | ~ m1_subset_1(C_1138,k1_zfmisc_1(A_1142))
      | v1_xboole_0(C_1138)
      | v1_xboole_0(B_1139)
      | v1_xboole_0(A_1142) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_66495,plain,(
    ! [A_1142,C_1138,E_1141] :
      ( v1_funct_1(k1_tmap_1(A_1142,'#skF_2',C_1138,'#skF_4',E_1141,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1141,k1_zfmisc_1(k2_zfmisc_1(C_1138,'#skF_2')))
      | ~ v1_funct_2(E_1141,C_1138,'#skF_2')
      | ~ v1_funct_1(E_1141)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1142))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1138,k1_zfmisc_1(A_1142))
      | v1_xboole_0(C_1138)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1142) ) ),
    inference(resolution,[status(thm)],[c_48,c_66493])).

tff(c_66500,plain,(
    ! [A_1142,C_1138,E_1141] :
      ( v1_funct_1(k1_tmap_1(A_1142,'#skF_2',C_1138,'#skF_4',E_1141,'#skF_6'))
      | ~ m1_subset_1(E_1141,k1_zfmisc_1(k2_zfmisc_1(C_1138,'#skF_2')))
      | ~ v1_funct_2(E_1141,C_1138,'#skF_2')
      | ~ v1_funct_1(E_1141)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1142))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1138,k1_zfmisc_1(A_1142))
      | v1_xboole_0(C_1138)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_66495])).

tff(c_67023,plain,(
    ! [A_1171,C_1172,E_1173] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2',C_1172,'#skF_4',E_1173,'#skF_6'))
      | ~ m1_subset_1(E_1173,k1_zfmisc_1(k2_zfmisc_1(C_1172,'#skF_2')))
      | ~ v1_funct_2(E_1173,C_1172,'#skF_2')
      | ~ v1_funct_1(E_1173)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1(C_1172,k1_zfmisc_1(A_1171))
      | v1_xboole_0(C_1172)
      | v1_xboole_0(A_1171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_66500])).

tff(c_67030,plain,(
    ! [A_1171] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1171))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1171) ) ),
    inference(resolution,[status(thm)],[c_54,c_67023])).

tff(c_67040,plain,(
    ! [A_1171] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1171))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_67030])).

tff(c_68454,plain,(
    ! [A_1205] :
      ( v1_funct_1(k1_tmap_1(A_1205,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1205))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1205))
      | v1_xboole_0(A_1205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_67040])).

tff(c_68457,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_68454])).

tff(c_68460,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_68457])).

tff(c_68461,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68460])).

tff(c_5746,plain,(
    ! [B_17] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_17)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_98,c_5731])).

tff(c_5571,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_5',k3_xboole_0(A_16,'#skF_4')) = k3_xboole_0(k7_relat_1('#skF_5',A_16),k1_xboole_0)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5564,c_18])).

tff(c_5580,plain,(
    ! [A_16] : k7_relat_1('#skF_5',k3_xboole_0(A_16,'#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_98,c_2,c_5571])).

tff(c_66936,plain,(
    ! [D_1169,E_1165,A_1164,F_1167,C_1168,B_1166] :
      ( k2_partfun1(k4_subset_1(A_1164,C_1168,D_1169),B_1166,k1_tmap_1(A_1164,B_1166,C_1168,D_1169,E_1165,F_1167),C_1168) = E_1165
      | ~ m1_subset_1(k1_tmap_1(A_1164,B_1166,C_1168,D_1169,E_1165,F_1167),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1164,C_1168,D_1169),B_1166)))
      | ~ v1_funct_2(k1_tmap_1(A_1164,B_1166,C_1168,D_1169,E_1165,F_1167),k4_subset_1(A_1164,C_1168,D_1169),B_1166)
      | ~ v1_funct_1(k1_tmap_1(A_1164,B_1166,C_1168,D_1169,E_1165,F_1167))
      | k2_partfun1(D_1169,B_1166,F_1167,k9_subset_1(A_1164,C_1168,D_1169)) != k2_partfun1(C_1168,B_1166,E_1165,k9_subset_1(A_1164,C_1168,D_1169))
      | ~ m1_subset_1(F_1167,k1_zfmisc_1(k2_zfmisc_1(D_1169,B_1166)))
      | ~ v1_funct_2(F_1167,D_1169,B_1166)
      | ~ v1_funct_1(F_1167)
      | ~ m1_subset_1(E_1165,k1_zfmisc_1(k2_zfmisc_1(C_1168,B_1166)))
      | ~ v1_funct_2(E_1165,C_1168,B_1166)
      | ~ v1_funct_1(E_1165)
      | ~ m1_subset_1(D_1169,k1_zfmisc_1(A_1164))
      | v1_xboole_0(D_1169)
      | ~ m1_subset_1(C_1168,k1_zfmisc_1(A_1164))
      | v1_xboole_0(C_1168)
      | v1_xboole_0(B_1166)
      | v1_xboole_0(A_1164) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_76080,plain,(
    ! [F_1351,A_1350,E_1349,B_1347,C_1346,D_1348] :
      ( k2_partfun1(k4_subset_1(A_1350,C_1346,D_1348),B_1347,k1_tmap_1(A_1350,B_1347,C_1346,D_1348,E_1349,F_1351),C_1346) = E_1349
      | ~ v1_funct_2(k1_tmap_1(A_1350,B_1347,C_1346,D_1348,E_1349,F_1351),k4_subset_1(A_1350,C_1346,D_1348),B_1347)
      | ~ v1_funct_1(k1_tmap_1(A_1350,B_1347,C_1346,D_1348,E_1349,F_1351))
      | k2_partfun1(D_1348,B_1347,F_1351,k9_subset_1(A_1350,C_1346,D_1348)) != k2_partfun1(C_1346,B_1347,E_1349,k9_subset_1(A_1350,C_1346,D_1348))
      | ~ m1_subset_1(F_1351,k1_zfmisc_1(k2_zfmisc_1(D_1348,B_1347)))
      | ~ v1_funct_2(F_1351,D_1348,B_1347)
      | ~ v1_funct_1(F_1351)
      | ~ m1_subset_1(E_1349,k1_zfmisc_1(k2_zfmisc_1(C_1346,B_1347)))
      | ~ v1_funct_2(E_1349,C_1346,B_1347)
      | ~ v1_funct_1(E_1349)
      | ~ m1_subset_1(D_1348,k1_zfmisc_1(A_1350))
      | v1_xboole_0(D_1348)
      | ~ m1_subset_1(C_1346,k1_zfmisc_1(A_1350))
      | v1_xboole_0(C_1346)
      | v1_xboole_0(B_1347)
      | v1_xboole_0(A_1350) ) ),
    inference(resolution,[status(thm)],[c_40,c_66936])).

tff(c_101615,plain,(
    ! [A_1600,B_1597,F_1601,D_1598,E_1599,C_1596] :
      ( k2_partfun1(k4_subset_1(A_1600,C_1596,D_1598),B_1597,k1_tmap_1(A_1600,B_1597,C_1596,D_1598,E_1599,F_1601),C_1596) = E_1599
      | ~ v1_funct_1(k1_tmap_1(A_1600,B_1597,C_1596,D_1598,E_1599,F_1601))
      | k2_partfun1(D_1598,B_1597,F_1601,k9_subset_1(A_1600,C_1596,D_1598)) != k2_partfun1(C_1596,B_1597,E_1599,k9_subset_1(A_1600,C_1596,D_1598))
      | ~ m1_subset_1(F_1601,k1_zfmisc_1(k2_zfmisc_1(D_1598,B_1597)))
      | ~ v1_funct_2(F_1601,D_1598,B_1597)
      | ~ v1_funct_1(F_1601)
      | ~ m1_subset_1(E_1599,k1_zfmisc_1(k2_zfmisc_1(C_1596,B_1597)))
      | ~ v1_funct_2(E_1599,C_1596,B_1597)
      | ~ v1_funct_1(E_1599)
      | ~ m1_subset_1(D_1598,k1_zfmisc_1(A_1600))
      | v1_xboole_0(D_1598)
      | ~ m1_subset_1(C_1596,k1_zfmisc_1(A_1600))
      | v1_xboole_0(C_1596)
      | v1_xboole_0(B_1597)
      | v1_xboole_0(A_1600) ) ),
    inference(resolution,[status(thm)],[c_42,c_76080])).

tff(c_101619,plain,(
    ! [A_1600,C_1596,E_1599] :
      ( k2_partfun1(k4_subset_1(A_1600,C_1596,'#skF_4'),'#skF_2',k1_tmap_1(A_1600,'#skF_2',C_1596,'#skF_4',E_1599,'#skF_6'),C_1596) = E_1599
      | ~ v1_funct_1(k1_tmap_1(A_1600,'#skF_2',C_1596,'#skF_4',E_1599,'#skF_6'))
      | k2_partfun1(C_1596,'#skF_2',E_1599,k9_subset_1(A_1600,C_1596,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1600,C_1596,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1599,k1_zfmisc_1(k2_zfmisc_1(C_1596,'#skF_2')))
      | ~ v1_funct_2(E_1599,C_1596,'#skF_2')
      | ~ v1_funct_1(E_1599)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1600))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1596,k1_zfmisc_1(A_1600))
      | v1_xboole_0(C_1596)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1600) ) ),
    inference(resolution,[status(thm)],[c_48,c_101615])).

tff(c_101625,plain,(
    ! [A_1600,C_1596,E_1599] :
      ( k2_partfun1(k4_subset_1(A_1600,C_1596,'#skF_4'),'#skF_2',k1_tmap_1(A_1600,'#skF_2',C_1596,'#skF_4',E_1599,'#skF_6'),C_1596) = E_1599
      | ~ v1_funct_1(k1_tmap_1(A_1600,'#skF_2',C_1596,'#skF_4',E_1599,'#skF_6'))
      | k2_partfun1(C_1596,'#skF_2',E_1599,k9_subset_1(A_1600,C_1596,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1600,C_1596,'#skF_4'))
      | ~ m1_subset_1(E_1599,k1_zfmisc_1(k2_zfmisc_1(C_1596,'#skF_2')))
      | ~ v1_funct_2(E_1599,C_1596,'#skF_2')
      | ~ v1_funct_1(E_1599)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1600))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1596,k1_zfmisc_1(A_1600))
      | v1_xboole_0(C_1596)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1600) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5687,c_101619])).

tff(c_102474,plain,(
    ! [A_1639,C_1640,E_1641] :
      ( k2_partfun1(k4_subset_1(A_1639,C_1640,'#skF_4'),'#skF_2',k1_tmap_1(A_1639,'#skF_2',C_1640,'#skF_4',E_1641,'#skF_6'),C_1640) = E_1641
      | ~ v1_funct_1(k1_tmap_1(A_1639,'#skF_2',C_1640,'#skF_4',E_1641,'#skF_6'))
      | k2_partfun1(C_1640,'#skF_2',E_1641,k9_subset_1(A_1639,C_1640,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1639,C_1640,'#skF_4'))
      | ~ m1_subset_1(E_1641,k1_zfmisc_1(k2_zfmisc_1(C_1640,'#skF_2')))
      | ~ v1_funct_2(E_1641,C_1640,'#skF_2')
      | ~ v1_funct_1(E_1641)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1639))
      | ~ m1_subset_1(C_1640,k1_zfmisc_1(A_1639))
      | v1_xboole_0(C_1640)
      | v1_xboole_0(A_1639) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_101625])).

tff(c_102481,plain,(
    ! [A_1639] :
      ( k2_partfun1(k4_subset_1(A_1639,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1639,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1639,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1639,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1639,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1639))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1639))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1639) ) ),
    inference(resolution,[status(thm)],[c_54,c_102474])).

tff(c_102491,plain,(
    ! [A_1639] :
      ( k2_partfun1(k4_subset_1(A_1639,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1639,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1639,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1639,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1639,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1639))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1639))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1639) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_5690,c_102481])).

tff(c_104865,plain,(
    ! [A_1651] :
      ( k2_partfun1(k4_subset_1(A_1651,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1651,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1651,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1651,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1651,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1651))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1651))
      | v1_xboole_0(A_1651) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_102491])).

tff(c_65851,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5256])).

tff(c_68002,plain,(
    ! [G_1198,C_1196,B_1195,D_1197,A_1194] :
      ( k1_tmap_1(A_1194,B_1195,C_1196,D_1197,k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,C_1196),k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,D_1197)) = G_1198
      | ~ m1_subset_1(G_1198,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1194,C_1196,D_1197),B_1195)))
      | ~ v1_funct_2(G_1198,k4_subset_1(A_1194,C_1196,D_1197),B_1195)
      | ~ v1_funct_1(G_1198)
      | k2_partfun1(D_1197,B_1195,k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,D_1197),k9_subset_1(A_1194,C_1196,D_1197)) != k2_partfun1(C_1196,B_1195,k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,C_1196),k9_subset_1(A_1194,C_1196,D_1197))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,D_1197),k1_zfmisc_1(k2_zfmisc_1(D_1197,B_1195)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,D_1197),D_1197,B_1195)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,D_1197))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,C_1196),k1_zfmisc_1(k2_zfmisc_1(C_1196,B_1195)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,C_1196),C_1196,B_1195)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_1194,C_1196,D_1197),B_1195,G_1198,C_1196))
      | ~ m1_subset_1(D_1197,k1_zfmisc_1(A_1194))
      | v1_xboole_0(D_1197)
      | ~ m1_subset_1(C_1196,k1_zfmisc_1(A_1194))
      | v1_xboole_0(C_1196)
      | v1_xboole_0(B_1195)
      | v1_xboole_0(A_1194) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_68004,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4')) = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65851,c_68002])).

tff(c_68006,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k3_xboole_0('#skF_4','#skF_3')) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_52,c_65851,c_50,c_65851,c_48,c_5748,c_5687,c_65851,c_2,c_2,c_5351,c_5351,c_65851,c_68004])).

tff(c_68007,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k3_xboole_0('#skF_4','#skF_3')) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_70,c_68,c_64,c_68006])).

tff(c_72176,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68989,c_68461,c_68007])).

tff(c_72177,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72176])).

tff(c_104874,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_104865,c_72177])).

tff(c_104887,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_5746,c_5351,c_5580,c_5351,c_68461,c_58,c_104874])).

tff(c_104889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_104887])).

tff(c_104890,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72176])).

tff(c_105609,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_104890])).

tff(c_105621,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_105609])).

tff(c_105624,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_58,c_56,c_54,c_52,c_50,c_48,c_105621])).

tff(c_105626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_70,c_68,c_64,c_105624])).

tff(c_105628,plain,(
    m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_104890])).

tff(c_38,plain,(
    ! [F_157,D_145,A_33,E_153,B_97,C_129] :
      ( k2_partfun1(k4_subset_1(A_33,C_129,D_145),B_97,k1_tmap_1(A_33,B_97,C_129,D_145,E_153,F_157),C_129) = E_153
      | ~ m1_subset_1(k1_tmap_1(A_33,B_97,C_129,D_145,E_153,F_157),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_33,C_129,D_145),B_97)))
      | ~ v1_funct_2(k1_tmap_1(A_33,B_97,C_129,D_145,E_153,F_157),k4_subset_1(A_33,C_129,D_145),B_97)
      | ~ v1_funct_1(k1_tmap_1(A_33,B_97,C_129,D_145,E_153,F_157))
      | k2_partfun1(D_145,B_97,F_157,k9_subset_1(A_33,C_129,D_145)) != k2_partfun1(C_129,B_97,E_153,k9_subset_1(A_33,C_129,D_145))
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(D_145,B_97)))
      | ~ v1_funct_2(F_157,D_145,B_97)
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(C_129,B_97)))
      | ~ v1_funct_2(E_153,C_129,B_97)
      | ~ v1_funct_1(E_153)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(A_33))
      | v1_xboole_0(D_145)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(A_33))
      | v1_xboole_0(C_129)
      | v1_xboole_0(B_97)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_105645,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_105628,c_38])).

tff(c_105673,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_58,c_56,c_54,c_52,c_50,c_48,c_5784,c_69057,c_5351,c_5608,c_69057,c_5351,c_5687,c_5690,c_68461,c_105645])).

tff(c_105674,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_70,c_68,c_64,c_65850,c_105673])).

tff(c_106582,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_105674])).

tff(c_106585,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_58,c_56,c_54,c_52,c_50,c_48,c_106582])).

tff(c_106587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_70,c_68,c_64,c_106585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:34 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.94/12.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.05/12.94  
% 22.05/12.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.05/12.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.05/12.94  
% 22.05/12.94  %Foreground sorts:
% 22.05/12.94  
% 22.05/12.94  
% 22.05/12.94  %Background operators:
% 22.05/12.94  
% 22.05/12.94  
% 22.05/12.94  %Foreground operators:
% 22.05/12.94  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 22.05/12.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.05/12.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.05/12.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 22.05/12.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.05/12.94  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 22.05/12.94  tff('#skF_5', type, '#skF_5': $i).
% 22.05/12.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.05/12.94  tff('#skF_6', type, '#skF_6': $i).
% 22.05/12.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.05/12.94  tff('#skF_2', type, '#skF_2': $i).
% 22.05/12.94  tff('#skF_3', type, '#skF_3': $i).
% 22.05/12.94  tff('#skF_1', type, '#skF_1': $i).
% 22.05/12.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.05/12.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.05/12.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.05/12.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.05/12.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.05/12.94  tff('#skF_4', type, '#skF_4': $i).
% 22.05/12.94  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.05/12.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.05/12.94  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 22.05/12.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.05/12.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.05/12.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.05/12.94  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 22.05/12.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.05/12.94  
% 22.05/12.98  tff(f_212, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 22.05/12.98  tff(f_170, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 22.05/12.98  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 22.05/12.98  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 22.05/12.98  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 22.05/12.98  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 22.05/12.98  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 22.05/12.98  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 22.05/12.98  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 22.05/12.98  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 22.05/12.98  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 22.05/12.98  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 22.05/12.98  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 22.05/12.98  tff(f_88, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 22.05/12.98  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 22.05/12.98  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 22.05/12.98  tff(c_72, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_42, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.05/12.98  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 22.05/12.98  tff(c_182, plain, (![B_237, A_238]: (v1_relat_1(B_237) | ~m1_subset_1(B_237, k1_zfmisc_1(A_238)) | ~v1_relat_1(A_238))), inference(cnfTransformation, [status(thm)], [f_48])).
% 22.05/12.98  tff(c_185, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_182])).
% 22.05/12.98  tff(c_197, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_185])).
% 22.05/12.98  tff(c_82, plain, (![B_228, A_229]: (k3_xboole_0(B_228, A_229)=k3_xboole_0(A_229, B_228))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.05/12.98  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.05/12.98  tff(c_98, plain, (![A_229]: (k3_xboole_0(k1_xboole_0, A_229)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 22.05/12.98  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.05/12.98  tff(c_60, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_5306, plain, (![A_416, B_417]: (r1_xboole_0(A_416, B_417) | ~r1_subset_1(A_416, B_417) | v1_xboole_0(B_417) | v1_xboole_0(A_416))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.05/12.98  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.05/12.98  tff(c_5327, plain, (![B_420, A_421]: (r1_xboole_0(B_420, A_421) | ~r1_subset_1(A_421, B_420) | v1_xboole_0(B_420) | v1_xboole_0(A_421))), inference(resolution, [status(thm)], [c_5306, c_8])).
% 22.05/12.98  tff(c_24, plain, (![A_24, B_25]: (r1_subset_1(A_24, B_25) | ~r1_xboole_0(A_24, B_25) | v1_xboole_0(B_25) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.05/12.98  tff(c_5390, plain, (![B_429, A_430]: (r1_subset_1(B_429, A_430) | ~r1_subset_1(A_430, B_429) | v1_xboole_0(B_429) | v1_xboole_0(A_430))), inference(resolution, [status(thm)], [c_5327, c_24])).
% 22.05/12.98  tff(c_5392, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_5390])).
% 22.05/12.98  tff(c_5395, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_5392])).
% 22.05/12.98  tff(c_26, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | ~r1_subset_1(A_24, B_25) | v1_xboole_0(B_25) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.05/12.98  tff(c_5272, plain, (![C_411, A_412, B_413]: (v4_relat_1(C_411, A_412) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.05/12.98  tff(c_5279, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_5272])).
% 22.05/12.98  tff(c_5281, plain, (![B_414, A_415]: (k7_relat_1(B_414, A_415)=B_414 | ~v4_relat_1(B_414, A_415) | ~v1_relat_1(B_414))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.05/12.98  tff(c_5287, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5279, c_5281])).
% 22.05/12.98  tff(c_5293, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_5287])).
% 22.05/12.98  tff(c_5401, plain, (![C_431, A_432, B_433]: (k7_relat_1(k7_relat_1(C_431, A_432), B_433)=k1_xboole_0 | ~r1_xboole_0(A_432, B_433) | ~v1_relat_1(C_431))), inference(cnfTransformation, [status(thm)], [f_60])).
% 22.05/12.98  tff(c_5416, plain, (![B_433]: (k7_relat_1('#skF_6', B_433)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_433) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5293, c_5401])).
% 22.05/12.98  tff(c_5426, plain, (![B_434]: (k7_relat_1('#skF_6', B_434)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_434))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_5416])).
% 22.05/12.98  tff(c_5434, plain, (![B_25]: (k7_relat_1('#skF_6', B_25)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_25) | v1_xboole_0(B_25) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_5426])).
% 22.05/12.98  tff(c_5718, plain, (![B_448]: (k7_relat_1('#skF_6', B_448)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_448) | v1_xboole_0(B_448))), inference(negUnitSimplification, [status(thm)], [c_64, c_5434])).
% 22.05/12.98  tff(c_5721, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_5395, c_5718])).
% 22.05/12.98  tff(c_5724, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_5721])).
% 22.05/12.98  tff(c_18, plain, (![C_18, A_16, B_17]: (k3_xboole_0(k7_relat_1(C_18, A_16), k7_relat_1(C_18, B_17))=k7_relat_1(C_18, k3_xboole_0(A_16, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 22.05/12.98  tff(c_5734, plain, (![A_16]: (k7_relat_1('#skF_6', k3_xboole_0(A_16, '#skF_3'))=k3_xboole_0(k7_relat_1('#skF_6', A_16), k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5724, c_18])).
% 22.05/12.98  tff(c_5748, plain, (![A_16]: (k7_relat_1('#skF_6', k3_xboole_0(A_16, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_98, c_2, c_5734])).
% 22.05/12.98  tff(c_188, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_182])).
% 22.05/12.98  tff(c_200, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_188])).
% 22.05/12.98  tff(c_5313, plain, (![B_417, A_416]: (r1_xboole_0(B_417, A_416) | ~r1_subset_1(A_416, B_417) | v1_xboole_0(B_417) | v1_xboole_0(A_416))), inference(resolution, [status(thm)], [c_5306, c_8])).
% 22.05/12.98  tff(c_5280, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_5272])).
% 22.05/12.98  tff(c_5284, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5280, c_5281])).
% 22.05/12.98  tff(c_5290, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_5284])).
% 22.05/12.98  tff(c_5419, plain, (![B_433]: (k7_relat_1('#skF_5', B_433)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_433) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5290, c_5401])).
% 22.05/12.98  tff(c_5451, plain, (![B_435]: (k7_relat_1('#skF_5', B_435)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_435))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_5419])).
% 22.05/12.98  tff(c_5455, plain, (![A_416]: (k7_relat_1('#skF_5', A_416)=k1_xboole_0 | ~r1_subset_1(A_416, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_416))), inference(resolution, [status(thm)], [c_5313, c_5451])).
% 22.05/12.98  tff(c_5558, plain, (![A_440]: (k7_relat_1('#skF_5', A_440)=k1_xboole_0 | ~r1_subset_1(A_440, '#skF_3') | v1_xboole_0(A_440))), inference(negUnitSimplification, [status(thm)], [c_68, c_5455])).
% 22.05/12.98  tff(c_5561, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_5395, c_5558])).
% 22.05/12.98  tff(c_5564, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_5561])).
% 22.05/12.98  tff(c_5568, plain, (![B_17]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_17))=k3_xboole_0(k1_xboole_0, k7_relat_1('#skF_5', B_17)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5564, c_18])).
% 22.05/12.98  tff(c_5578, plain, (![B_17]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_17))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_98, c_5568])).
% 22.05/12.98  tff(c_5339, plain, (![A_422, B_423, C_424]: (k9_subset_1(A_422, B_423, C_424)=k3_xboole_0(B_423, C_424) | ~m1_subset_1(C_424, k1_zfmisc_1(A_422)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.05/12.98  tff(c_5351, plain, (![B_423]: (k9_subset_1('#skF_1', B_423, '#skF_4')=k3_xboole_0(B_423, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_5339])).
% 22.05/12.98  tff(c_6214, plain, (![D_463, C_461, A_465, B_462, E_464, F_466]: (v1_funct_1(k1_tmap_1(A_465, B_462, C_461, D_463, E_464, F_466)) | ~m1_subset_1(F_466, k1_zfmisc_1(k2_zfmisc_1(D_463, B_462))) | ~v1_funct_2(F_466, D_463, B_462) | ~v1_funct_1(F_466) | ~m1_subset_1(E_464, k1_zfmisc_1(k2_zfmisc_1(C_461, B_462))) | ~v1_funct_2(E_464, C_461, B_462) | ~v1_funct_1(E_464) | ~m1_subset_1(D_463, k1_zfmisc_1(A_465)) | v1_xboole_0(D_463) | ~m1_subset_1(C_461, k1_zfmisc_1(A_465)) | v1_xboole_0(C_461) | v1_xboole_0(B_462) | v1_xboole_0(A_465))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.05/12.98  tff(c_6216, plain, (![A_465, C_461, E_464]: (v1_funct_1(k1_tmap_1(A_465, '#skF_2', C_461, '#skF_4', E_464, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_464, k1_zfmisc_1(k2_zfmisc_1(C_461, '#skF_2'))) | ~v1_funct_2(E_464, C_461, '#skF_2') | ~v1_funct_1(E_464) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_465)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_461, k1_zfmisc_1(A_465)) | v1_xboole_0(C_461) | v1_xboole_0('#skF_2') | v1_xboole_0(A_465))), inference(resolution, [status(thm)], [c_48, c_6214])).
% 22.05/12.98  tff(c_6221, plain, (![A_465, C_461, E_464]: (v1_funct_1(k1_tmap_1(A_465, '#skF_2', C_461, '#skF_4', E_464, '#skF_6')) | ~m1_subset_1(E_464, k1_zfmisc_1(k2_zfmisc_1(C_461, '#skF_2'))) | ~v1_funct_2(E_464, C_461, '#skF_2') | ~v1_funct_1(E_464) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_465)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_461, k1_zfmisc_1(A_465)) | v1_xboole_0(C_461) | v1_xboole_0('#skF_2') | v1_xboole_0(A_465))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_6216])).
% 22.05/12.98  tff(c_7323, plain, (![A_511, C_512, E_513]: (v1_funct_1(k1_tmap_1(A_511, '#skF_2', C_512, '#skF_4', E_513, '#skF_6')) | ~m1_subset_1(E_513, k1_zfmisc_1(k2_zfmisc_1(C_512, '#skF_2'))) | ~v1_funct_2(E_513, C_512, '#skF_2') | ~v1_funct_1(E_513) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_511)) | ~m1_subset_1(C_512, k1_zfmisc_1(A_511)) | v1_xboole_0(C_512) | v1_xboole_0(A_511))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_6221])).
% 22.05/12.98  tff(c_7330, plain, (![A_511]: (v1_funct_1(k1_tmap_1(A_511, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_511)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_511)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_511))), inference(resolution, [status(thm)], [c_54, c_7323])).
% 22.05/12.98  tff(c_7340, plain, (![A_511]: (v1_funct_1(k1_tmap_1(A_511, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_511)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_511)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_511))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_7330])).
% 22.05/12.98  tff(c_8757, plain, (![A_539]: (v1_funct_1(k1_tmap_1(A_539, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_539)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_539)) | v1_xboole_0(A_539))), inference(negUnitSimplification, [status(thm)], [c_68, c_7340])).
% 22.05/12.98  tff(c_8760, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_8757])).
% 22.05/12.98  tff(c_8763, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8760])).
% 22.05/12.98  tff(c_8764, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_8763])).
% 22.05/12.98  tff(c_5680, plain, (![A_443, B_444, C_445, D_446]: (k2_partfun1(A_443, B_444, C_445, D_446)=k7_relat_1(C_445, D_446) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))) | ~v1_funct_1(C_445))), inference(cnfTransformation, [status(thm)], [f_88])).
% 22.05/12.98  tff(c_5684, plain, (![D_446]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_446)=k7_relat_1('#skF_5', D_446) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_5680])).
% 22.05/12.98  tff(c_5690, plain, (![D_446]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_446)=k7_relat_1('#skF_5', D_446))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5684])).
% 22.05/12.98  tff(c_5682, plain, (![D_446]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_446)=k7_relat_1('#skF_6', D_446) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_5680])).
% 22.05/12.98  tff(c_5687, plain, (![D_446]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_446)=k7_relat_1('#skF_6', D_446))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5682])).
% 22.05/12.98  tff(c_40, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.05/12.98  tff(c_6959, plain, (![D_500, B_497, C_499, E_496, A_495, F_498]: (k2_partfun1(k4_subset_1(A_495, C_499, D_500), B_497, k1_tmap_1(A_495, B_497, C_499, D_500, E_496, F_498), D_500)=F_498 | ~m1_subset_1(k1_tmap_1(A_495, B_497, C_499, D_500, E_496, F_498), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_495, C_499, D_500), B_497))) | ~v1_funct_2(k1_tmap_1(A_495, B_497, C_499, D_500, E_496, F_498), k4_subset_1(A_495, C_499, D_500), B_497) | ~v1_funct_1(k1_tmap_1(A_495, B_497, C_499, D_500, E_496, F_498)) | k2_partfun1(D_500, B_497, F_498, k9_subset_1(A_495, C_499, D_500))!=k2_partfun1(C_499, B_497, E_496, k9_subset_1(A_495, C_499, D_500)) | ~m1_subset_1(F_498, k1_zfmisc_1(k2_zfmisc_1(D_500, B_497))) | ~v1_funct_2(F_498, D_500, B_497) | ~v1_funct_1(F_498) | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(C_499, B_497))) | ~v1_funct_2(E_496, C_499, B_497) | ~v1_funct_1(E_496) | ~m1_subset_1(D_500, k1_zfmisc_1(A_495)) | v1_xboole_0(D_500) | ~m1_subset_1(C_499, k1_zfmisc_1(A_495)) | v1_xboole_0(C_499) | v1_xboole_0(B_497) | v1_xboole_0(A_495))), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.05/12.98  tff(c_16524, plain, (![F_691, A_690, D_688, E_689, B_687, C_686]: (k2_partfun1(k4_subset_1(A_690, C_686, D_688), B_687, k1_tmap_1(A_690, B_687, C_686, D_688, E_689, F_691), D_688)=F_691 | ~v1_funct_2(k1_tmap_1(A_690, B_687, C_686, D_688, E_689, F_691), k4_subset_1(A_690, C_686, D_688), B_687) | ~v1_funct_1(k1_tmap_1(A_690, B_687, C_686, D_688, E_689, F_691)) | k2_partfun1(D_688, B_687, F_691, k9_subset_1(A_690, C_686, D_688))!=k2_partfun1(C_686, B_687, E_689, k9_subset_1(A_690, C_686, D_688)) | ~m1_subset_1(F_691, k1_zfmisc_1(k2_zfmisc_1(D_688, B_687))) | ~v1_funct_2(F_691, D_688, B_687) | ~v1_funct_1(F_691) | ~m1_subset_1(E_689, k1_zfmisc_1(k2_zfmisc_1(C_686, B_687))) | ~v1_funct_2(E_689, C_686, B_687) | ~v1_funct_1(E_689) | ~m1_subset_1(D_688, k1_zfmisc_1(A_690)) | v1_xboole_0(D_688) | ~m1_subset_1(C_686, k1_zfmisc_1(A_690)) | v1_xboole_0(C_686) | v1_xboole_0(B_687) | v1_xboole_0(A_690))), inference(resolution, [status(thm)], [c_40, c_6959])).
% 22.05/12.98  tff(c_40938, plain, (![C_926, F_931, D_928, A_930, E_929, B_927]: (k2_partfun1(k4_subset_1(A_930, C_926, D_928), B_927, k1_tmap_1(A_930, B_927, C_926, D_928, E_929, F_931), D_928)=F_931 | ~v1_funct_1(k1_tmap_1(A_930, B_927, C_926, D_928, E_929, F_931)) | k2_partfun1(D_928, B_927, F_931, k9_subset_1(A_930, C_926, D_928))!=k2_partfun1(C_926, B_927, E_929, k9_subset_1(A_930, C_926, D_928)) | ~m1_subset_1(F_931, k1_zfmisc_1(k2_zfmisc_1(D_928, B_927))) | ~v1_funct_2(F_931, D_928, B_927) | ~v1_funct_1(F_931) | ~m1_subset_1(E_929, k1_zfmisc_1(k2_zfmisc_1(C_926, B_927))) | ~v1_funct_2(E_929, C_926, B_927) | ~v1_funct_1(E_929) | ~m1_subset_1(D_928, k1_zfmisc_1(A_930)) | v1_xboole_0(D_928) | ~m1_subset_1(C_926, k1_zfmisc_1(A_930)) | v1_xboole_0(C_926) | v1_xboole_0(B_927) | v1_xboole_0(A_930))), inference(resolution, [status(thm)], [c_42, c_16524])).
% 22.05/12.98  tff(c_40942, plain, (![A_930, C_926, E_929]: (k2_partfun1(k4_subset_1(A_930, C_926, '#skF_4'), '#skF_2', k1_tmap_1(A_930, '#skF_2', C_926, '#skF_4', E_929, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_930, '#skF_2', C_926, '#skF_4', E_929, '#skF_6')) | k2_partfun1(C_926, '#skF_2', E_929, k9_subset_1(A_930, C_926, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_930, C_926, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_929, k1_zfmisc_1(k2_zfmisc_1(C_926, '#skF_2'))) | ~v1_funct_2(E_929, C_926, '#skF_2') | ~v1_funct_1(E_929) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_930)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_926, k1_zfmisc_1(A_930)) | v1_xboole_0(C_926) | v1_xboole_0('#skF_2') | v1_xboole_0(A_930))), inference(resolution, [status(thm)], [c_48, c_40938])).
% 22.05/12.98  tff(c_40948, plain, (![A_930, C_926, E_929]: (k2_partfun1(k4_subset_1(A_930, C_926, '#skF_4'), '#skF_2', k1_tmap_1(A_930, '#skF_2', C_926, '#skF_4', E_929, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_930, '#skF_2', C_926, '#skF_4', E_929, '#skF_6')) | k2_partfun1(C_926, '#skF_2', E_929, k9_subset_1(A_930, C_926, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_930, C_926, '#skF_4')) | ~m1_subset_1(E_929, k1_zfmisc_1(k2_zfmisc_1(C_926, '#skF_2'))) | ~v1_funct_2(E_929, C_926, '#skF_2') | ~v1_funct_1(E_929) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_930)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_926, k1_zfmisc_1(A_930)) | v1_xboole_0(C_926) | v1_xboole_0('#skF_2') | v1_xboole_0(A_930))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5687, c_40942])).
% 22.05/12.98  tff(c_62599, plain, (![A_1096, C_1097, E_1098]: (k2_partfun1(k4_subset_1(A_1096, C_1097, '#skF_4'), '#skF_2', k1_tmap_1(A_1096, '#skF_2', C_1097, '#skF_4', E_1098, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1096, '#skF_2', C_1097, '#skF_4', E_1098, '#skF_6')) | k2_partfun1(C_1097, '#skF_2', E_1098, k9_subset_1(A_1096, C_1097, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1096, C_1097, '#skF_4')) | ~m1_subset_1(E_1098, k1_zfmisc_1(k2_zfmisc_1(C_1097, '#skF_2'))) | ~v1_funct_2(E_1098, C_1097, '#skF_2') | ~v1_funct_1(E_1098) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1096)) | ~m1_subset_1(C_1097, k1_zfmisc_1(A_1096)) | v1_xboole_0(C_1097) | v1_xboole_0(A_1096))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_40948])).
% 22.05/12.98  tff(c_62606, plain, (![A_1096]: (k2_partfun1(k4_subset_1(A_1096, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1096, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1096, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1096, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1096, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1096)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1096)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1096))), inference(resolution, [status(thm)], [c_54, c_62599])).
% 22.05/12.98  tff(c_62616, plain, (![A_1096]: (k2_partfun1(k4_subset_1(A_1096, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1096, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1096, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1096, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1096, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1096)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1096)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1096))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_5690, c_62606])).
% 22.05/12.98  tff(c_65822, plain, (![A_1119]: (k2_partfun1(k4_subset_1(A_1119, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1119, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1119, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1119, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1119, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1119)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1119)) | v1_xboole_0(A_1119))), inference(negUnitSimplification, [status(thm)], [c_68, c_62616])).
% 22.05/12.98  tff(c_227, plain, (![C_244, A_245, B_246]: (v4_relat_1(C_244, A_245) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.05/12.98  tff(c_235, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_227])).
% 22.05/12.98  tff(c_236, plain, (![B_247, A_248]: (k7_relat_1(B_247, A_248)=B_247 | ~v4_relat_1(B_247, A_248) | ~v1_relat_1(B_247))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.05/12.98  tff(c_239, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_235, c_236])).
% 22.05/12.98  tff(c_245, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_239])).
% 22.05/12.98  tff(c_290, plain, (![C_255, A_256, B_257]: (k7_relat_1(k7_relat_1(C_255, A_256), B_257)=k1_xboole_0 | ~r1_xboole_0(A_256, B_257) | ~v1_relat_1(C_255))), inference(cnfTransformation, [status(thm)], [f_60])).
% 22.05/12.98  tff(c_308, plain, (![B_257]: (k7_relat_1('#skF_5', B_257)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_257) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_245, c_290])).
% 22.05/12.98  tff(c_340, plain, (![B_259]: (k7_relat_1('#skF_5', B_259)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_259))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_308])).
% 22.05/12.98  tff(c_348, plain, (![B_25]: (k7_relat_1('#skF_5', B_25)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_25) | v1_xboole_0(B_25) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_340])).
% 22.05/12.98  tff(c_901, plain, (![B_287]: (k7_relat_1('#skF_5', B_287)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_287) | v1_xboole_0(B_287))), inference(negUnitSimplification, [status(thm)], [c_68, c_348])).
% 22.05/12.98  tff(c_904, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_901])).
% 22.05/12.98  tff(c_907, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_904])).
% 22.05/12.98  tff(c_911, plain, (![B_17]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_17))=k3_xboole_0(k1_xboole_0, k7_relat_1('#skF_5', B_17)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_907, c_18])).
% 22.05/12.98  tff(c_933, plain, (![B_17]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_17))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_98, c_911])).
% 22.05/12.98  tff(c_859, plain, (![A_281, B_282, C_283, D_284]: (k2_partfun1(A_281, B_282, C_283, D_284)=k7_relat_1(C_283, D_284) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_1(C_283))), inference(cnfTransformation, [status(thm)], [f_88])).
% 22.05/12.98  tff(c_863, plain, (![D_284]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_284)=k7_relat_1('#skF_5', D_284) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_859])).
% 22.05/12.98  tff(c_869, plain, (![D_284]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_284)=k7_relat_1('#skF_5', D_284))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_863])).
% 22.05/12.98  tff(c_257, plain, (![A_249, B_250]: (r1_xboole_0(A_249, B_250) | ~r1_subset_1(A_249, B_250) | v1_xboole_0(B_250) | v1_xboole_0(A_249))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.05/12.98  tff(c_264, plain, (![B_250, A_249]: (r1_xboole_0(B_250, A_249) | ~r1_subset_1(A_249, B_250) | v1_xboole_0(B_250) | v1_xboole_0(A_249))), inference(resolution, [status(thm)], [c_257, c_8])).
% 22.05/12.98  tff(c_234, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_227])).
% 22.05/12.98  tff(c_242, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_234, c_236])).
% 22.05/12.98  tff(c_248, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_242])).
% 22.05/12.98  tff(c_305, plain, (![B_257]: (k7_relat_1('#skF_6', B_257)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_257) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_290])).
% 22.05/12.98  tff(c_315, plain, (![B_258]: (k7_relat_1('#skF_6', B_258)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_258))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_305])).
% 22.05/12.98  tff(c_319, plain, (![A_249]: (k7_relat_1('#skF_6', A_249)=k1_xboole_0 | ~r1_subset_1(A_249, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_249))), inference(resolution, [status(thm)], [c_264, c_315])).
% 22.05/12.98  tff(c_515, plain, (![A_272]: (k7_relat_1('#skF_6', A_272)=k1_xboole_0 | ~r1_subset_1(A_272, '#skF_4') | v1_xboole_0(A_272))), inference(negUnitSimplification, [status(thm)], [c_64, c_319])).
% 22.05/12.98  tff(c_518, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_515])).
% 22.05/12.98  tff(c_521, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_518])).
% 22.05/12.98  tff(c_619, plain, (![A_16]: (k7_relat_1('#skF_6', k3_xboole_0(A_16, '#skF_3'))=k3_xboole_0(k7_relat_1('#skF_6', A_16), k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_521, c_18])).
% 22.05/12.98  tff(c_640, plain, (![A_16]: (k7_relat_1('#skF_6', k3_xboole_0(A_16, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_10, c_619])).
% 22.05/12.98  tff(c_861, plain, (![D_284]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_284)=k7_relat_1('#skF_6', D_284) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_859])).
% 22.05/12.98  tff(c_866, plain, (![D_284]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_284)=k7_relat_1('#skF_6', D_284))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_861])).
% 22.05/12.98  tff(c_408, plain, (![A_263, B_264, C_265]: (k9_subset_1(A_263, B_264, C_265)=k3_xboole_0(B_264, C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(A_263)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.05/12.98  tff(c_420, plain, (![B_264]: (k9_subset_1('#skF_1', B_264, '#skF_4')=k3_xboole_0(B_264, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_408])).
% 22.05/12.98  tff(c_46, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 22.05/12.98  tff(c_212, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 22.05/12.98  tff(c_430, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_420, c_212])).
% 22.05/12.98  tff(c_431, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_430])).
% 22.05/12.98  tff(c_5255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_933, c_869, c_640, c_866, c_431])).
% 22.05/12.98  tff(c_5256, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 22.05/12.98  tff(c_5883, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_5256])).
% 22.05/12.98  tff(c_65833, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65822, c_5883])).
% 22.05/12.98  tff(c_65847, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_5748, c_5578, c_2, c_5351, c_2, c_5351, c_8764, c_65833])).
% 22.05/12.98  tff(c_65849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_65847])).
% 22.05/12.98  tff(c_65850, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_5256])).
% 22.05/12.98  tff(c_5731, plain, (![B_17]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_17))=k3_xboole_0(k1_xboole_0, k7_relat_1('#skF_6', B_17)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5724, c_18])).
% 22.05/12.98  tff(c_5754, plain, (![B_449]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_449))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_98, c_5731])).
% 22.05/12.98  tff(c_5784, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10, c_5754])).
% 22.05/12.98  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.05/12.98  tff(c_68973, plain, (![A_1215, B_1216]: (k3_xboole_0(A_1215, B_1216)=k1_xboole_0 | ~r1_subset_1(A_1215, B_1216) | v1_xboole_0(B_1216) | v1_xboole_0(A_1215))), inference(resolution, [status(thm)], [c_5306, c_4])).
% 22.05/12.98  tff(c_68982, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_68973])).
% 22.05/12.98  tff(c_68988, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68982])).
% 22.05/12.98  tff(c_68989, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_68988])).
% 22.05/12.98  tff(c_166, plain, (![A_233, B_234]: (r1_xboole_0(A_233, B_234) | k3_xboole_0(A_233, B_234)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.05/12.98  tff(c_174, plain, (![B_235, A_236]: (r1_xboole_0(B_235, A_236) | k3_xboole_0(A_236, B_235)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_166, c_8])).
% 22.05/12.98  tff(c_180, plain, (![B_235, A_236]: (k3_xboole_0(B_235, A_236)=k1_xboole_0 | k3_xboole_0(A_236, B_235)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_174, c_4])).
% 22.05/12.98  tff(c_69057, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_68989, c_180])).
% 22.05/12.98  tff(c_5584, plain, (![B_441]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', B_441))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_98, c_5568])).
% 22.05/12.98  tff(c_5608, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10, c_5584])).
% 22.05/12.98  tff(c_66493, plain, (![F_1143, B_1139, D_1140, E_1141, A_1142, C_1138]: (v1_funct_1(k1_tmap_1(A_1142, B_1139, C_1138, D_1140, E_1141, F_1143)) | ~m1_subset_1(F_1143, k1_zfmisc_1(k2_zfmisc_1(D_1140, B_1139))) | ~v1_funct_2(F_1143, D_1140, B_1139) | ~v1_funct_1(F_1143) | ~m1_subset_1(E_1141, k1_zfmisc_1(k2_zfmisc_1(C_1138, B_1139))) | ~v1_funct_2(E_1141, C_1138, B_1139) | ~v1_funct_1(E_1141) | ~m1_subset_1(D_1140, k1_zfmisc_1(A_1142)) | v1_xboole_0(D_1140) | ~m1_subset_1(C_1138, k1_zfmisc_1(A_1142)) | v1_xboole_0(C_1138) | v1_xboole_0(B_1139) | v1_xboole_0(A_1142))), inference(cnfTransformation, [status(thm)], [f_170])).
% 22.05/12.98  tff(c_66495, plain, (![A_1142, C_1138, E_1141]: (v1_funct_1(k1_tmap_1(A_1142, '#skF_2', C_1138, '#skF_4', E_1141, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1141, k1_zfmisc_1(k2_zfmisc_1(C_1138, '#skF_2'))) | ~v1_funct_2(E_1141, C_1138, '#skF_2') | ~v1_funct_1(E_1141) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1142)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1138, k1_zfmisc_1(A_1142)) | v1_xboole_0(C_1138) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1142))), inference(resolution, [status(thm)], [c_48, c_66493])).
% 22.05/12.98  tff(c_66500, plain, (![A_1142, C_1138, E_1141]: (v1_funct_1(k1_tmap_1(A_1142, '#skF_2', C_1138, '#skF_4', E_1141, '#skF_6')) | ~m1_subset_1(E_1141, k1_zfmisc_1(k2_zfmisc_1(C_1138, '#skF_2'))) | ~v1_funct_2(E_1141, C_1138, '#skF_2') | ~v1_funct_1(E_1141) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1142)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1138, k1_zfmisc_1(A_1142)) | v1_xboole_0(C_1138) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1142))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_66495])).
% 22.05/12.98  tff(c_67023, plain, (![A_1171, C_1172, E_1173]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', C_1172, '#skF_4', E_1173, '#skF_6')) | ~m1_subset_1(E_1173, k1_zfmisc_1(k2_zfmisc_1(C_1172, '#skF_2'))) | ~v1_funct_2(E_1173, C_1172, '#skF_2') | ~v1_funct_1(E_1173) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1(C_1172, k1_zfmisc_1(A_1171)) | v1_xboole_0(C_1172) | v1_xboole_0(A_1171))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_66500])).
% 22.05/12.98  tff(c_67030, plain, (![A_1171]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1171)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1171))), inference(resolution, [status(thm)], [c_54, c_67023])).
% 22.05/12.98  tff(c_67040, plain, (![A_1171]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1171)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1171))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_67030])).
% 22.05/12.98  tff(c_68454, plain, (![A_1205]: (v1_funct_1(k1_tmap_1(A_1205, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1205)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1205)) | v1_xboole_0(A_1205))), inference(negUnitSimplification, [status(thm)], [c_68, c_67040])).
% 22.05/12.98  tff(c_68457, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_68454])).
% 22.05/12.98  tff(c_68460, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_68457])).
% 22.05/12.98  tff(c_68461, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_68460])).
% 22.05/12.98  tff(c_5746, plain, (![B_17]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_17))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_98, c_5731])).
% 22.05/12.98  tff(c_5571, plain, (![A_16]: (k7_relat_1('#skF_5', k3_xboole_0(A_16, '#skF_4'))=k3_xboole_0(k7_relat_1('#skF_5', A_16), k1_xboole_0) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5564, c_18])).
% 22.05/12.98  tff(c_5580, plain, (![A_16]: (k7_relat_1('#skF_5', k3_xboole_0(A_16, '#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_98, c_2, c_5571])).
% 22.05/12.98  tff(c_66936, plain, (![D_1169, E_1165, A_1164, F_1167, C_1168, B_1166]: (k2_partfun1(k4_subset_1(A_1164, C_1168, D_1169), B_1166, k1_tmap_1(A_1164, B_1166, C_1168, D_1169, E_1165, F_1167), C_1168)=E_1165 | ~m1_subset_1(k1_tmap_1(A_1164, B_1166, C_1168, D_1169, E_1165, F_1167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1164, C_1168, D_1169), B_1166))) | ~v1_funct_2(k1_tmap_1(A_1164, B_1166, C_1168, D_1169, E_1165, F_1167), k4_subset_1(A_1164, C_1168, D_1169), B_1166) | ~v1_funct_1(k1_tmap_1(A_1164, B_1166, C_1168, D_1169, E_1165, F_1167)) | k2_partfun1(D_1169, B_1166, F_1167, k9_subset_1(A_1164, C_1168, D_1169))!=k2_partfun1(C_1168, B_1166, E_1165, k9_subset_1(A_1164, C_1168, D_1169)) | ~m1_subset_1(F_1167, k1_zfmisc_1(k2_zfmisc_1(D_1169, B_1166))) | ~v1_funct_2(F_1167, D_1169, B_1166) | ~v1_funct_1(F_1167) | ~m1_subset_1(E_1165, k1_zfmisc_1(k2_zfmisc_1(C_1168, B_1166))) | ~v1_funct_2(E_1165, C_1168, B_1166) | ~v1_funct_1(E_1165) | ~m1_subset_1(D_1169, k1_zfmisc_1(A_1164)) | v1_xboole_0(D_1169) | ~m1_subset_1(C_1168, k1_zfmisc_1(A_1164)) | v1_xboole_0(C_1168) | v1_xboole_0(B_1166) | v1_xboole_0(A_1164))), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.05/12.98  tff(c_76080, plain, (![F_1351, A_1350, E_1349, B_1347, C_1346, D_1348]: (k2_partfun1(k4_subset_1(A_1350, C_1346, D_1348), B_1347, k1_tmap_1(A_1350, B_1347, C_1346, D_1348, E_1349, F_1351), C_1346)=E_1349 | ~v1_funct_2(k1_tmap_1(A_1350, B_1347, C_1346, D_1348, E_1349, F_1351), k4_subset_1(A_1350, C_1346, D_1348), B_1347) | ~v1_funct_1(k1_tmap_1(A_1350, B_1347, C_1346, D_1348, E_1349, F_1351)) | k2_partfun1(D_1348, B_1347, F_1351, k9_subset_1(A_1350, C_1346, D_1348))!=k2_partfun1(C_1346, B_1347, E_1349, k9_subset_1(A_1350, C_1346, D_1348)) | ~m1_subset_1(F_1351, k1_zfmisc_1(k2_zfmisc_1(D_1348, B_1347))) | ~v1_funct_2(F_1351, D_1348, B_1347) | ~v1_funct_1(F_1351) | ~m1_subset_1(E_1349, k1_zfmisc_1(k2_zfmisc_1(C_1346, B_1347))) | ~v1_funct_2(E_1349, C_1346, B_1347) | ~v1_funct_1(E_1349) | ~m1_subset_1(D_1348, k1_zfmisc_1(A_1350)) | v1_xboole_0(D_1348) | ~m1_subset_1(C_1346, k1_zfmisc_1(A_1350)) | v1_xboole_0(C_1346) | v1_xboole_0(B_1347) | v1_xboole_0(A_1350))), inference(resolution, [status(thm)], [c_40, c_66936])).
% 22.05/12.98  tff(c_101615, plain, (![A_1600, B_1597, F_1601, D_1598, E_1599, C_1596]: (k2_partfun1(k4_subset_1(A_1600, C_1596, D_1598), B_1597, k1_tmap_1(A_1600, B_1597, C_1596, D_1598, E_1599, F_1601), C_1596)=E_1599 | ~v1_funct_1(k1_tmap_1(A_1600, B_1597, C_1596, D_1598, E_1599, F_1601)) | k2_partfun1(D_1598, B_1597, F_1601, k9_subset_1(A_1600, C_1596, D_1598))!=k2_partfun1(C_1596, B_1597, E_1599, k9_subset_1(A_1600, C_1596, D_1598)) | ~m1_subset_1(F_1601, k1_zfmisc_1(k2_zfmisc_1(D_1598, B_1597))) | ~v1_funct_2(F_1601, D_1598, B_1597) | ~v1_funct_1(F_1601) | ~m1_subset_1(E_1599, k1_zfmisc_1(k2_zfmisc_1(C_1596, B_1597))) | ~v1_funct_2(E_1599, C_1596, B_1597) | ~v1_funct_1(E_1599) | ~m1_subset_1(D_1598, k1_zfmisc_1(A_1600)) | v1_xboole_0(D_1598) | ~m1_subset_1(C_1596, k1_zfmisc_1(A_1600)) | v1_xboole_0(C_1596) | v1_xboole_0(B_1597) | v1_xboole_0(A_1600))), inference(resolution, [status(thm)], [c_42, c_76080])).
% 22.05/12.98  tff(c_101619, plain, (![A_1600, C_1596, E_1599]: (k2_partfun1(k4_subset_1(A_1600, C_1596, '#skF_4'), '#skF_2', k1_tmap_1(A_1600, '#skF_2', C_1596, '#skF_4', E_1599, '#skF_6'), C_1596)=E_1599 | ~v1_funct_1(k1_tmap_1(A_1600, '#skF_2', C_1596, '#skF_4', E_1599, '#skF_6')) | k2_partfun1(C_1596, '#skF_2', E_1599, k9_subset_1(A_1600, C_1596, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1600, C_1596, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1599, k1_zfmisc_1(k2_zfmisc_1(C_1596, '#skF_2'))) | ~v1_funct_2(E_1599, C_1596, '#skF_2') | ~v1_funct_1(E_1599) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1600)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1596, k1_zfmisc_1(A_1600)) | v1_xboole_0(C_1596) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1600))), inference(resolution, [status(thm)], [c_48, c_101615])).
% 22.05/12.98  tff(c_101625, plain, (![A_1600, C_1596, E_1599]: (k2_partfun1(k4_subset_1(A_1600, C_1596, '#skF_4'), '#skF_2', k1_tmap_1(A_1600, '#skF_2', C_1596, '#skF_4', E_1599, '#skF_6'), C_1596)=E_1599 | ~v1_funct_1(k1_tmap_1(A_1600, '#skF_2', C_1596, '#skF_4', E_1599, '#skF_6')) | k2_partfun1(C_1596, '#skF_2', E_1599, k9_subset_1(A_1600, C_1596, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1600, C_1596, '#skF_4')) | ~m1_subset_1(E_1599, k1_zfmisc_1(k2_zfmisc_1(C_1596, '#skF_2'))) | ~v1_funct_2(E_1599, C_1596, '#skF_2') | ~v1_funct_1(E_1599) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1600)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1596, k1_zfmisc_1(A_1600)) | v1_xboole_0(C_1596) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1600))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5687, c_101619])).
% 22.05/12.98  tff(c_102474, plain, (![A_1639, C_1640, E_1641]: (k2_partfun1(k4_subset_1(A_1639, C_1640, '#skF_4'), '#skF_2', k1_tmap_1(A_1639, '#skF_2', C_1640, '#skF_4', E_1641, '#skF_6'), C_1640)=E_1641 | ~v1_funct_1(k1_tmap_1(A_1639, '#skF_2', C_1640, '#skF_4', E_1641, '#skF_6')) | k2_partfun1(C_1640, '#skF_2', E_1641, k9_subset_1(A_1639, C_1640, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1639, C_1640, '#skF_4')) | ~m1_subset_1(E_1641, k1_zfmisc_1(k2_zfmisc_1(C_1640, '#skF_2'))) | ~v1_funct_2(E_1641, C_1640, '#skF_2') | ~v1_funct_1(E_1641) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1639)) | ~m1_subset_1(C_1640, k1_zfmisc_1(A_1639)) | v1_xboole_0(C_1640) | v1_xboole_0(A_1639))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_101625])).
% 22.05/12.98  tff(c_102481, plain, (![A_1639]: (k2_partfun1(k4_subset_1(A_1639, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1639, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1639, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1639, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1639, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1639)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1639)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1639))), inference(resolution, [status(thm)], [c_54, c_102474])).
% 22.05/12.98  tff(c_102491, plain, (![A_1639]: (k2_partfun1(k4_subset_1(A_1639, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1639, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1639, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1639, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1639, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1639)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1639)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1639))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_5690, c_102481])).
% 22.05/12.99  tff(c_104865, plain, (![A_1651]: (k2_partfun1(k4_subset_1(A_1651, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1651, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1651, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1651, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1651, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1651)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1651)) | v1_xboole_0(A_1651))), inference(negUnitSimplification, [status(thm)], [c_68, c_102491])).
% 22.05/12.99  tff(c_65851, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_5256])).
% 22.05/12.99  tff(c_68002, plain, (![G_1198, C_1196, B_1195, D_1197, A_1194]: (k1_tmap_1(A_1194, B_1195, C_1196, D_1197, k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, C_1196), k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, D_1197))=G_1198 | ~m1_subset_1(G_1198, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1194, C_1196, D_1197), B_1195))) | ~v1_funct_2(G_1198, k4_subset_1(A_1194, C_1196, D_1197), B_1195) | ~v1_funct_1(G_1198) | k2_partfun1(D_1197, B_1195, k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, D_1197), k9_subset_1(A_1194, C_1196, D_1197))!=k2_partfun1(C_1196, B_1195, k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, C_1196), k9_subset_1(A_1194, C_1196, D_1197)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, D_1197), k1_zfmisc_1(k2_zfmisc_1(D_1197, B_1195))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, D_1197), D_1197, B_1195) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, D_1197)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, C_1196), k1_zfmisc_1(k2_zfmisc_1(C_1196, B_1195))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, C_1196), C_1196, B_1195) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_1194, C_1196, D_1197), B_1195, G_1198, C_1196)) | ~m1_subset_1(D_1197, k1_zfmisc_1(A_1194)) | v1_xboole_0(D_1197) | ~m1_subset_1(C_1196, k1_zfmisc_1(A_1194)) | v1_xboole_0(C_1196) | v1_xboole_0(B_1195) | v1_xboole_0(A_1194))), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.05/12.99  tff(c_68004, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'))=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65851, c_68002])).
% 22.05/12.99  tff(c_68006, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k3_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_52, c_65851, c_50, c_65851, c_48, c_5748, c_5687, c_65851, c_2, c_2, c_5351, c_5351, c_65851, c_68004])).
% 22.05/12.99  tff(c_68007, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k3_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_70, c_68, c_64, c_68006])).
% 22.05/12.99  tff(c_72176, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68989, c_68461, c_68007])).
% 22.05/12.99  tff(c_72177, plain, (~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_72176])).
% 22.05/12.99  tff(c_104874, plain, (~v1_funct_1('#skF_5') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_104865, c_72177])).
% 22.05/12.99  tff(c_104887, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_5746, c_5351, c_5580, c_5351, c_68461, c_58, c_104874])).
% 22.05/12.99  tff(c_104889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_104887])).
% 22.05/12.99  tff(c_104890, plain, (~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72176])).
% 22.05/12.99  tff(c_105609, plain, (~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_104890])).
% 22.05/12.99  tff(c_105621, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_105609])).
% 22.05/12.99  tff(c_105624, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_58, c_56, c_54, c_52, c_50, c_48, c_105621])).
% 22.05/12.99  tff(c_105626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_70, c_68, c_64, c_105624])).
% 22.05/12.99  tff(c_105628, plain, (m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitRight, [status(thm)], [c_104890])).
% 22.05/12.99  tff(c_38, plain, (![F_157, D_145, A_33, E_153, B_97, C_129]: (k2_partfun1(k4_subset_1(A_33, C_129, D_145), B_97, k1_tmap_1(A_33, B_97, C_129, D_145, E_153, F_157), C_129)=E_153 | ~m1_subset_1(k1_tmap_1(A_33, B_97, C_129, D_145, E_153, F_157), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_33, C_129, D_145), B_97))) | ~v1_funct_2(k1_tmap_1(A_33, B_97, C_129, D_145, E_153, F_157), k4_subset_1(A_33, C_129, D_145), B_97) | ~v1_funct_1(k1_tmap_1(A_33, B_97, C_129, D_145, E_153, F_157)) | k2_partfun1(D_145, B_97, F_157, k9_subset_1(A_33, C_129, D_145))!=k2_partfun1(C_129, B_97, E_153, k9_subset_1(A_33, C_129, D_145)) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(D_145, B_97))) | ~v1_funct_2(F_157, D_145, B_97) | ~v1_funct_1(F_157) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(C_129, B_97))) | ~v1_funct_2(E_153, C_129, B_97) | ~v1_funct_1(E_153) | ~m1_subset_1(D_145, k1_zfmisc_1(A_33)) | v1_xboole_0(D_145) | ~m1_subset_1(C_129, k1_zfmisc_1(A_33)) | v1_xboole_0(C_129) | v1_xboole_0(B_97) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.05/12.99  tff(c_105645, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_105628, c_38])).
% 22.05/12.99  tff(c_105673, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_58, c_56, c_54, c_52, c_50, c_48, c_5784, c_69057, c_5351, c_5608, c_69057, c_5351, c_5687, c_5690, c_68461, c_105645])).
% 22.05/12.99  tff(c_105674, plain, (~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_70, c_68, c_64, c_65850, c_105673])).
% 22.05/12.99  tff(c_106582, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_105674])).
% 22.05/12.99  tff(c_106585, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_58, c_56, c_54, c_52, c_50, c_48, c_106582])).
% 22.05/12.99  tff(c_106587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_70, c_68, c_64, c_106585])).
% 22.05/12.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.05/12.99  
% 22.05/12.99  Inference rules
% 22.05/12.99  ----------------------
% 22.05/12.99  #Ref     : 0
% 22.05/12.99  #Sup     : 24670
% 22.05/12.99  #Fact    : 0
% 22.05/12.99  #Define  : 0
% 22.05/12.99  #Split   : 20
% 22.05/12.99  #Chain   : 0
% 22.05/12.99  #Close   : 0
% 22.05/12.99  
% 22.05/12.99  Ordering : KBO
% 22.05/12.99  
% 22.05/12.99  Simplification rules
% 22.05/12.99  ----------------------
% 22.05/12.99  #Subsume      : 2356
% 22.05/12.99  #Demod        : 28890
% 22.05/12.99  #Tautology    : 19362
% 22.05/12.99  #SimpNegUnit  : 312
% 22.05/12.99  #BackRed      : 2
% 22.05/12.99  
% 22.05/12.99  #Partial instantiations: 0
% 22.05/12.99  #Strategies tried      : 1
% 22.05/12.99  
% 22.05/12.99  Timing (in seconds)
% 22.05/12.99  ----------------------
% 22.05/12.99  Preprocessing        : 0.43
% 22.05/12.99  Parsing              : 0.21
% 22.05/12.99  CNF conversion       : 0.06
% 22.05/12.99  Main loop            : 11.75
% 22.05/12.99  Inferencing          : 1.95
% 22.05/12.99  Reduction            : 6.48
% 22.05/12.99  Demodulation         : 5.63
% 22.05/12.99  BG Simplification    : 0.23
% 22.05/12.99  Subsumption          : 2.71
% 22.05/12.99  Abstraction          : 0.31
% 22.05/12.99  MUC search           : 0.00
% 22.05/12.99  Cooper               : 0.00
% 22.05/12.99  Total                : 12.26
% 22.05/12.99  Index Insertion      : 0.00
% 22.05/12.99  Index Deletion       : 0.00
% 22.05/12.99  Index Matching       : 0.00
% 22.05/12.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
