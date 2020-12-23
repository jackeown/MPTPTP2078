%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:20 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 8.20s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 637 expanded)
%              Number of leaves         :   45 ( 248 expanded)
%              Depth                    :   13
%              Number of atoms          :  646 (3225 expanded)
%              Number of equality atoms :  109 ( 580 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_216,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_174,axiom,(
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

tff(f_140,axiom,(
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

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_626,plain,(
    ! [C_317,A_318,B_319] :
      ( v1_relat_1(C_317)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_633,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_626])).

tff(c_24,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_636,plain,(
    ! [B_322,A_323] :
      ( v4_relat_1(B_322,A_323)
      | ~ r1_tarski(k1_relat_1(B_322),A_323)
      | ~ v1_relat_1(B_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_641,plain,(
    ! [B_322] :
      ( v4_relat_1(B_322,k1_relat_1(B_322))
      | ~ v1_relat_1(B_322) ) ),
    inference(resolution,[status(thm)],[c_10,c_636])).

tff(c_775,plain,(
    ! [C_346,A_347,B_348] :
      ( v4_relat_1(C_346,A_347)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(B_348))
      | ~ v4_relat_1(B_348,A_347)
      | ~ v1_relat_1(B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_777,plain,(
    ! [A_347] :
      ( v4_relat_1('#skF_6',A_347)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_347)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_775])).

tff(c_796,plain,(
    ! [A_349] :
      ( v4_relat_1('#skF_6',A_349)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_777])).

tff(c_800,plain,
    ( v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_641,c_796])).

tff(c_803,plain,(
    v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_800])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_806,plain,
    ( k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_803,c_28])).

tff(c_809,plain,(
    k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_806])).

tff(c_26,plain,(
    ! [C_21,A_19,B_20] :
      ( k7_relat_1(k7_relat_1(C_21,A_19),B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_814,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_26])).

tff(c_3105,plain,(
    ! [B_711] :
      ( k7_relat_1('#skF_6',B_711) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_711) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_814])).

tff(c_3120,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_3105])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_668,plain,(
    ! [A_328,B_329] :
      ( r1_xboole_0(A_328,B_329)
      | ~ r1_subset_1(A_328,B_329)
      | v1_xboole_0(B_329)
      | v1_xboole_0(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_764,plain,(
    ! [A_344,B_345] :
      ( k3_xboole_0(A_344,B_345) = k1_xboole_0
      | ~ r1_subset_1(A_344,B_345)
      | v1_xboole_0(B_345)
      | v1_xboole_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_668,c_2])).

tff(c_770,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_764])).

tff(c_774,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_770])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_834,plain,(
    ! [A_351,B_352,C_353,D_354] :
      ( k2_partfun1(A_351,B_352,C_353,D_354) = k7_relat_1(C_353,D_354)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352)))
      | ~ v1_funct_1(C_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_836,plain,(
    ! [D_354] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_354) = k7_relat_1('#skF_6',D_354)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_834])).

tff(c_841,plain,(
    ! [D_354] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_354) = k7_relat_1('#skF_6',D_354) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_836])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_838,plain,(
    ! [D_354] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_354) = k7_relat_1('#skF_5',D_354)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_834])).

tff(c_844,plain,(
    ! [D_354] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_354) = k7_relat_1('#skF_5',D_354) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_838])).

tff(c_686,plain,(
    ! [A_332,B_333,C_334] :
      ( k9_subset_1(A_332,B_333,C_334) = k3_xboole_0(B_333,C_334)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(A_332)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_698,plain,(
    ! [B_333] : k9_subset_1('#skF_1',B_333,'#skF_4') = k3_xboole_0(B_333,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_686])).

tff(c_115,plain,(
    ! [C_236,A_237,B_238] :
      ( v1_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_122,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_115])).

tff(c_125,plain,(
    ! [B_241,A_242] :
      ( v4_relat_1(B_241,A_242)
      | ~ r1_tarski(k1_relat_1(B_241),A_242)
      | ~ v1_relat_1(B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_130,plain,(
    ! [B_241] :
      ( v4_relat_1(B_241,k1_relat_1(B_241))
      | ~ v1_relat_1(B_241) ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_264,plain,(
    ! [C_265,A_266,B_267] :
      ( v4_relat_1(C_265,A_266)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(B_267))
      | ~ v4_relat_1(B_267,A_266)
      | ~ v1_relat_1(B_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_266,plain,(
    ! [A_266] :
      ( v4_relat_1('#skF_6',A_266)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_266)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_52,c_264])).

tff(c_292,plain,(
    ! [A_272] :
      ( v4_relat_1('#skF_6',A_272)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_266])).

tff(c_296,plain,
    ( v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_130,c_292])).

tff(c_299,plain,(
    v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_296])).

tff(c_302,plain,
    ( k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_299,c_28])).

tff(c_305,plain,(
    k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_302])).

tff(c_309,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_26])).

tff(c_466,plain,(
    ! [B_288] :
      ( k7_relat_1('#skF_6',B_288) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_309])).

tff(c_481,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_466])).

tff(c_123,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_115])).

tff(c_268,plain,(
    ! [A_266] :
      ( v4_relat_1('#skF_5',A_266)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_266)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_58,c_264])).

tff(c_325,plain,(
    ! [A_274] :
      ( v4_relat_1('#skF_5',A_274)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_268])).

tff(c_329,plain,
    ( v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_130,c_325])).

tff(c_332,plain,(
    v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_329])).

tff(c_335,plain,
    ( k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_332,c_28])).

tff(c_338,plain,(
    k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_335])).

tff(c_355,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_5',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_26])).

tff(c_370,plain,(
    ! [B_282] :
      ( k7_relat_1('#skF_5',B_282) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_355])).

tff(c_385,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_370])).

tff(c_281,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( k2_partfun1(A_268,B_269,C_270,D_271) = k7_relat_1(C_270,D_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ v1_funct_1(C_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_285,plain,(
    ! [D_271] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_271) = k7_relat_1('#skF_5',D_271)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_281])).

tff(c_291,plain,(
    ! [D_271] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_271) = k7_relat_1('#skF_5',D_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_285])).

tff(c_283,plain,(
    ! [D_271] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_271) = k7_relat_1('#skF_6',D_271)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_281])).

tff(c_288,plain,(
    ! [D_271] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_271) = k7_relat_1('#skF_6',D_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_283])).

tff(c_163,plain,(
    ! [A_249,B_250] :
      ( r1_xboole_0(A_249,B_250)
      | ~ r1_subset_1(A_249,B_250)
      | v1_xboole_0(B_250)
      | v1_xboole_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_248,plain,(
    ! [A_261,B_262] :
      ( k3_xboole_0(A_261,B_262) = k1_xboole_0
      | ~ r1_subset_1(A_261,B_262)
      | v1_xboole_0(B_262)
      | v1_xboole_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_251,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_248])).

tff(c_254,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_251])).

tff(c_172,plain,(
    ! [A_251,B_252,C_253] :
      ( k9_subset_1(A_251,B_252,C_253) = k3_xboole_0(B_252,C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(A_251)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    ! [B_252] : k9_subset_1('#skF_1',B_252,'#skF_4') = k3_xboole_0(B_252,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_172])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_100,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_194,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_184,c_100])).

tff(c_609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_385,c_291,c_288,c_254,c_254,c_194])).

tff(c_611,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_709,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_698,c_611])).

tff(c_3062,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_774,c_841,c_844,c_709])).

tff(c_3122,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3120,c_3062])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_3246,plain,(
    ! [A_723,E_722,F_724,C_719,D_721,B_720] :
      ( v1_funct_1(k1_tmap_1(A_723,B_720,C_719,D_721,E_722,F_724))
      | ~ m1_subset_1(F_724,k1_zfmisc_1(k2_zfmisc_1(D_721,B_720)))
      | ~ v1_funct_2(F_724,D_721,B_720)
      | ~ v1_funct_1(F_724)
      | ~ m1_subset_1(E_722,k1_zfmisc_1(k2_zfmisc_1(C_719,B_720)))
      | ~ v1_funct_2(E_722,C_719,B_720)
      | ~ v1_funct_1(E_722)
      | ~ m1_subset_1(D_721,k1_zfmisc_1(A_723))
      | v1_xboole_0(D_721)
      | ~ m1_subset_1(C_719,k1_zfmisc_1(A_723))
      | v1_xboole_0(C_719)
      | v1_xboole_0(B_720)
      | v1_xboole_0(A_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_3248,plain,(
    ! [A_723,C_719,E_722] :
      ( v1_funct_1(k1_tmap_1(A_723,'#skF_2',C_719,'#skF_4',E_722,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_722,k1_zfmisc_1(k2_zfmisc_1(C_719,'#skF_2')))
      | ~ v1_funct_2(E_722,C_719,'#skF_2')
      | ~ v1_funct_1(E_722)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_723))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_719,k1_zfmisc_1(A_723))
      | v1_xboole_0(C_719)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_723) ) ),
    inference(resolution,[status(thm)],[c_52,c_3246])).

tff(c_3253,plain,(
    ! [A_723,C_719,E_722] :
      ( v1_funct_1(k1_tmap_1(A_723,'#skF_2',C_719,'#skF_4',E_722,'#skF_6'))
      | ~ m1_subset_1(E_722,k1_zfmisc_1(k2_zfmisc_1(C_719,'#skF_2')))
      | ~ v1_funct_2(E_722,C_719,'#skF_2')
      | ~ v1_funct_1(E_722)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_723))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_719,k1_zfmisc_1(A_723))
      | v1_xboole_0(C_719)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_723) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3248])).

tff(c_3302,plain,(
    ! [A_730,C_731,E_732] :
      ( v1_funct_1(k1_tmap_1(A_730,'#skF_2',C_731,'#skF_4',E_732,'#skF_6'))
      | ~ m1_subset_1(E_732,k1_zfmisc_1(k2_zfmisc_1(C_731,'#skF_2')))
      | ~ v1_funct_2(E_732,C_731,'#skF_2')
      | ~ v1_funct_1(E_732)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_730))
      | ~ m1_subset_1(C_731,k1_zfmisc_1(A_730))
      | v1_xboole_0(C_731)
      | v1_xboole_0(A_730) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_3253])).

tff(c_3306,plain,(
    ! [A_730] :
      ( v1_funct_1(k1_tmap_1(A_730,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_730))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_730))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_730) ) ),
    inference(resolution,[status(thm)],[c_58,c_3302])).

tff(c_3313,plain,(
    ! [A_730] :
      ( v1_funct_1(k1_tmap_1(A_730,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_730))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_730))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_730) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3306])).

tff(c_3333,plain,(
    ! [A_742] :
      ( v1_funct_1(k1_tmap_1(A_742,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_742))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_742))
      | v1_xboole_0(A_742) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3313])).

tff(c_3336,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_3333])).

tff(c_3339,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3336])).

tff(c_3340,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3339])).

tff(c_46,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_44,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_3476,plain,(
    ! [D_768,C_767,E_764,B_765,F_766,A_763] :
      ( k2_partfun1(k4_subset_1(A_763,C_767,D_768),B_765,k1_tmap_1(A_763,B_765,C_767,D_768,E_764,F_766),C_767) = E_764
      | ~ m1_subset_1(k1_tmap_1(A_763,B_765,C_767,D_768,E_764,F_766),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_763,C_767,D_768),B_765)))
      | ~ v1_funct_2(k1_tmap_1(A_763,B_765,C_767,D_768,E_764,F_766),k4_subset_1(A_763,C_767,D_768),B_765)
      | ~ v1_funct_1(k1_tmap_1(A_763,B_765,C_767,D_768,E_764,F_766))
      | k2_partfun1(D_768,B_765,F_766,k9_subset_1(A_763,C_767,D_768)) != k2_partfun1(C_767,B_765,E_764,k9_subset_1(A_763,C_767,D_768))
      | ~ m1_subset_1(F_766,k1_zfmisc_1(k2_zfmisc_1(D_768,B_765)))
      | ~ v1_funct_2(F_766,D_768,B_765)
      | ~ v1_funct_1(F_766)
      | ~ m1_subset_1(E_764,k1_zfmisc_1(k2_zfmisc_1(C_767,B_765)))
      | ~ v1_funct_2(E_764,C_767,B_765)
      | ~ v1_funct_1(E_764)
      | ~ m1_subset_1(D_768,k1_zfmisc_1(A_763))
      | v1_xboole_0(D_768)
      | ~ m1_subset_1(C_767,k1_zfmisc_1(A_763))
      | v1_xboole_0(C_767)
      | v1_xboole_0(B_765)
      | v1_xboole_0(A_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4158,plain,(
    ! [F_893,D_890,C_888,E_891,B_889,A_892] :
      ( k2_partfun1(k4_subset_1(A_892,C_888,D_890),B_889,k1_tmap_1(A_892,B_889,C_888,D_890,E_891,F_893),C_888) = E_891
      | ~ v1_funct_2(k1_tmap_1(A_892,B_889,C_888,D_890,E_891,F_893),k4_subset_1(A_892,C_888,D_890),B_889)
      | ~ v1_funct_1(k1_tmap_1(A_892,B_889,C_888,D_890,E_891,F_893))
      | k2_partfun1(D_890,B_889,F_893,k9_subset_1(A_892,C_888,D_890)) != k2_partfun1(C_888,B_889,E_891,k9_subset_1(A_892,C_888,D_890))
      | ~ m1_subset_1(F_893,k1_zfmisc_1(k2_zfmisc_1(D_890,B_889)))
      | ~ v1_funct_2(F_893,D_890,B_889)
      | ~ v1_funct_1(F_893)
      | ~ m1_subset_1(E_891,k1_zfmisc_1(k2_zfmisc_1(C_888,B_889)))
      | ~ v1_funct_2(E_891,C_888,B_889)
      | ~ v1_funct_1(E_891)
      | ~ m1_subset_1(D_890,k1_zfmisc_1(A_892))
      | v1_xboole_0(D_890)
      | ~ m1_subset_1(C_888,k1_zfmisc_1(A_892))
      | v1_xboole_0(C_888)
      | v1_xboole_0(B_889)
      | v1_xboole_0(A_892) ) ),
    inference(resolution,[status(thm)],[c_44,c_3476])).

tff(c_4746,plain,(
    ! [D_988,F_991,C_986,E_989,A_990,B_987] :
      ( k2_partfun1(k4_subset_1(A_990,C_986,D_988),B_987,k1_tmap_1(A_990,B_987,C_986,D_988,E_989,F_991),C_986) = E_989
      | ~ v1_funct_1(k1_tmap_1(A_990,B_987,C_986,D_988,E_989,F_991))
      | k2_partfun1(D_988,B_987,F_991,k9_subset_1(A_990,C_986,D_988)) != k2_partfun1(C_986,B_987,E_989,k9_subset_1(A_990,C_986,D_988))
      | ~ m1_subset_1(F_991,k1_zfmisc_1(k2_zfmisc_1(D_988,B_987)))
      | ~ v1_funct_2(F_991,D_988,B_987)
      | ~ v1_funct_1(F_991)
      | ~ m1_subset_1(E_989,k1_zfmisc_1(k2_zfmisc_1(C_986,B_987)))
      | ~ v1_funct_2(E_989,C_986,B_987)
      | ~ v1_funct_1(E_989)
      | ~ m1_subset_1(D_988,k1_zfmisc_1(A_990))
      | v1_xboole_0(D_988)
      | ~ m1_subset_1(C_986,k1_zfmisc_1(A_990))
      | v1_xboole_0(C_986)
      | v1_xboole_0(B_987)
      | v1_xboole_0(A_990) ) ),
    inference(resolution,[status(thm)],[c_46,c_4158])).

tff(c_4750,plain,(
    ! [A_990,C_986,E_989] :
      ( k2_partfun1(k4_subset_1(A_990,C_986,'#skF_4'),'#skF_2',k1_tmap_1(A_990,'#skF_2',C_986,'#skF_4',E_989,'#skF_6'),C_986) = E_989
      | ~ v1_funct_1(k1_tmap_1(A_990,'#skF_2',C_986,'#skF_4',E_989,'#skF_6'))
      | k2_partfun1(C_986,'#skF_2',E_989,k9_subset_1(A_990,C_986,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_990,C_986,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_989,k1_zfmisc_1(k2_zfmisc_1(C_986,'#skF_2')))
      | ~ v1_funct_2(E_989,C_986,'#skF_2')
      | ~ v1_funct_1(E_989)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_990))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_986,k1_zfmisc_1(A_990))
      | v1_xboole_0(C_986)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_990) ) ),
    inference(resolution,[status(thm)],[c_52,c_4746])).

tff(c_4756,plain,(
    ! [A_990,C_986,E_989] :
      ( k2_partfun1(k4_subset_1(A_990,C_986,'#skF_4'),'#skF_2',k1_tmap_1(A_990,'#skF_2',C_986,'#skF_4',E_989,'#skF_6'),C_986) = E_989
      | ~ v1_funct_1(k1_tmap_1(A_990,'#skF_2',C_986,'#skF_4',E_989,'#skF_6'))
      | k2_partfun1(C_986,'#skF_2',E_989,k9_subset_1(A_990,C_986,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_990,C_986,'#skF_4'))
      | ~ m1_subset_1(E_989,k1_zfmisc_1(k2_zfmisc_1(C_986,'#skF_2')))
      | ~ v1_funct_2(E_989,C_986,'#skF_2')
      | ~ v1_funct_1(E_989)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_990))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_986,k1_zfmisc_1(A_990))
      | v1_xboole_0(C_986)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_990) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_841,c_4750])).

tff(c_5270,plain,(
    ! [A_1042,C_1043,E_1044] :
      ( k2_partfun1(k4_subset_1(A_1042,C_1043,'#skF_4'),'#skF_2',k1_tmap_1(A_1042,'#skF_2',C_1043,'#skF_4',E_1044,'#skF_6'),C_1043) = E_1044
      | ~ v1_funct_1(k1_tmap_1(A_1042,'#skF_2',C_1043,'#skF_4',E_1044,'#skF_6'))
      | k2_partfun1(C_1043,'#skF_2',E_1044,k9_subset_1(A_1042,C_1043,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1042,C_1043,'#skF_4'))
      | ~ m1_subset_1(E_1044,k1_zfmisc_1(k2_zfmisc_1(C_1043,'#skF_2')))
      | ~ v1_funct_2(E_1044,C_1043,'#skF_2')
      | ~ v1_funct_1(E_1044)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1042))
      | ~ m1_subset_1(C_1043,k1_zfmisc_1(A_1042))
      | v1_xboole_0(C_1043)
      | v1_xboole_0(A_1042) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_4756])).

tff(c_5277,plain,(
    ! [A_1042] :
      ( k2_partfun1(k4_subset_1(A_1042,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1042,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1042,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1042,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1042,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1042))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1042))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1042) ) ),
    inference(resolution,[status(thm)],[c_58,c_5270])).

tff(c_5287,plain,(
    ! [A_1042] :
      ( k2_partfun1(k4_subset_1(A_1042,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1042,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1042,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1042,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1042,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1042))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1042))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1042) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_844,c_5277])).

tff(c_5289,plain,(
    ! [A_1045] :
      ( k2_partfun1(k4_subset_1(A_1045,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1045,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1045,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1045,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1045,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1045))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1045))
      | v1_xboole_0(A_1045) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5287])).

tff(c_634,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_626])).

tff(c_779,plain,(
    ! [A_347] :
      ( v4_relat_1('#skF_5',A_347)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_347)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_58,c_775])).

tff(c_820,plain,(
    ! [A_350] :
      ( v4_relat_1('#skF_5',A_350)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_350) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_779])).

tff(c_824,plain,
    ( v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_641,c_820])).

tff(c_827,plain,(
    v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_824])).

tff(c_830,plain,
    ( k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_827,c_28])).

tff(c_833,plain,(
    k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_830])).

tff(c_848,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_5',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_26])).

tff(c_956,plain,(
    ! [B_360] :
      ( k7_relat_1('#skF_5',B_360) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_848])).

tff(c_971,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_956])).

tff(c_873,plain,(
    ! [B_357] :
      ( k7_relat_1('#skF_6',B_357) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_814])).

tff(c_888,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_873])).

tff(c_1051,plain,(
    ! [D_372,A_374,B_371,E_373,C_370,F_375] :
      ( v1_funct_1(k1_tmap_1(A_374,B_371,C_370,D_372,E_373,F_375))
      | ~ m1_subset_1(F_375,k1_zfmisc_1(k2_zfmisc_1(D_372,B_371)))
      | ~ v1_funct_2(F_375,D_372,B_371)
      | ~ v1_funct_1(F_375)
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_370,B_371)))
      | ~ v1_funct_2(E_373,C_370,B_371)
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1(D_372,k1_zfmisc_1(A_374))
      | v1_xboole_0(D_372)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(A_374))
      | v1_xboole_0(C_370)
      | v1_xboole_0(B_371)
      | v1_xboole_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1053,plain,(
    ! [A_374,C_370,E_373] :
      ( v1_funct_1(k1_tmap_1(A_374,'#skF_2',C_370,'#skF_4',E_373,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_370,'#skF_2')))
      | ~ v1_funct_2(E_373,C_370,'#skF_2')
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_374))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_370,k1_zfmisc_1(A_374))
      | v1_xboole_0(C_370)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_374) ) ),
    inference(resolution,[status(thm)],[c_52,c_1051])).

tff(c_1058,plain,(
    ! [A_374,C_370,E_373] :
      ( v1_funct_1(k1_tmap_1(A_374,'#skF_2',C_370,'#skF_4',E_373,'#skF_6'))
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_370,'#skF_2')))
      | ~ v1_funct_2(E_373,C_370,'#skF_2')
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_374))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_370,k1_zfmisc_1(A_374))
      | v1_xboole_0(C_370)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1053])).

tff(c_1071,plain,(
    ! [A_378,C_379,E_380] :
      ( v1_funct_1(k1_tmap_1(A_378,'#skF_2',C_379,'#skF_4',E_380,'#skF_6'))
      | ~ m1_subset_1(E_380,k1_zfmisc_1(k2_zfmisc_1(C_379,'#skF_2')))
      | ~ v1_funct_2(E_380,C_379,'#skF_2')
      | ~ v1_funct_1(E_380)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_378))
      | ~ m1_subset_1(C_379,k1_zfmisc_1(A_378))
      | v1_xboole_0(C_379)
      | v1_xboole_0(A_378) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1058])).

tff(c_1075,plain,(
    ! [A_378] :
      ( v1_funct_1(k1_tmap_1(A_378,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_378))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_378))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_58,c_1071])).

tff(c_1082,plain,(
    ! [A_378] :
      ( v1_funct_1(k1_tmap_1(A_378,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_378))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_378))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1075])).

tff(c_1125,plain,(
    ! [A_396] :
      ( v1_funct_1(k1_tmap_1(A_396,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_396))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_396))
      | v1_xboole_0(A_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1082])).

tff(c_1128,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1125])).

tff(c_1131,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1128])).

tff(c_1132,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1131])).

tff(c_1253,plain,(
    ! [F_412,A_409,C_413,E_410,B_411,D_414] :
      ( k2_partfun1(k4_subset_1(A_409,C_413,D_414),B_411,k1_tmap_1(A_409,B_411,C_413,D_414,E_410,F_412),D_414) = F_412
      | ~ m1_subset_1(k1_tmap_1(A_409,B_411,C_413,D_414,E_410,F_412),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_409,C_413,D_414),B_411)))
      | ~ v1_funct_2(k1_tmap_1(A_409,B_411,C_413,D_414,E_410,F_412),k4_subset_1(A_409,C_413,D_414),B_411)
      | ~ v1_funct_1(k1_tmap_1(A_409,B_411,C_413,D_414,E_410,F_412))
      | k2_partfun1(D_414,B_411,F_412,k9_subset_1(A_409,C_413,D_414)) != k2_partfun1(C_413,B_411,E_410,k9_subset_1(A_409,C_413,D_414))
      | ~ m1_subset_1(F_412,k1_zfmisc_1(k2_zfmisc_1(D_414,B_411)))
      | ~ v1_funct_2(F_412,D_414,B_411)
      | ~ v1_funct_1(F_412)
      | ~ m1_subset_1(E_410,k1_zfmisc_1(k2_zfmisc_1(C_413,B_411)))
      | ~ v1_funct_2(E_410,C_413,B_411)
      | ~ v1_funct_1(E_410)
      | ~ m1_subset_1(D_414,k1_zfmisc_1(A_409))
      | v1_xboole_0(D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(A_409))
      | v1_xboole_0(C_413)
      | v1_xboole_0(B_411)
      | v1_xboole_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1993,plain,(
    ! [C_546,B_547,D_548,E_549,F_551,A_550] :
      ( k2_partfun1(k4_subset_1(A_550,C_546,D_548),B_547,k1_tmap_1(A_550,B_547,C_546,D_548,E_549,F_551),D_548) = F_551
      | ~ v1_funct_2(k1_tmap_1(A_550,B_547,C_546,D_548,E_549,F_551),k4_subset_1(A_550,C_546,D_548),B_547)
      | ~ v1_funct_1(k1_tmap_1(A_550,B_547,C_546,D_548,E_549,F_551))
      | k2_partfun1(D_548,B_547,F_551,k9_subset_1(A_550,C_546,D_548)) != k2_partfun1(C_546,B_547,E_549,k9_subset_1(A_550,C_546,D_548))
      | ~ m1_subset_1(F_551,k1_zfmisc_1(k2_zfmisc_1(D_548,B_547)))
      | ~ v1_funct_2(F_551,D_548,B_547)
      | ~ v1_funct_1(F_551)
      | ~ m1_subset_1(E_549,k1_zfmisc_1(k2_zfmisc_1(C_546,B_547)))
      | ~ v1_funct_2(E_549,C_546,B_547)
      | ~ v1_funct_1(E_549)
      | ~ m1_subset_1(D_548,k1_zfmisc_1(A_550))
      | v1_xboole_0(D_548)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(A_550))
      | v1_xboole_0(C_546)
      | v1_xboole_0(B_547)
      | v1_xboole_0(A_550) ) ),
    inference(resolution,[status(thm)],[c_44,c_1253])).

tff(c_2270,plain,(
    ! [B_628,E_630,A_631,F_632,C_627,D_629] :
      ( k2_partfun1(k4_subset_1(A_631,C_627,D_629),B_628,k1_tmap_1(A_631,B_628,C_627,D_629,E_630,F_632),D_629) = F_632
      | ~ v1_funct_1(k1_tmap_1(A_631,B_628,C_627,D_629,E_630,F_632))
      | k2_partfun1(D_629,B_628,F_632,k9_subset_1(A_631,C_627,D_629)) != k2_partfun1(C_627,B_628,E_630,k9_subset_1(A_631,C_627,D_629))
      | ~ m1_subset_1(F_632,k1_zfmisc_1(k2_zfmisc_1(D_629,B_628)))
      | ~ v1_funct_2(F_632,D_629,B_628)
      | ~ v1_funct_1(F_632)
      | ~ m1_subset_1(E_630,k1_zfmisc_1(k2_zfmisc_1(C_627,B_628)))
      | ~ v1_funct_2(E_630,C_627,B_628)
      | ~ v1_funct_1(E_630)
      | ~ m1_subset_1(D_629,k1_zfmisc_1(A_631))
      | v1_xboole_0(D_629)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(A_631))
      | v1_xboole_0(C_627)
      | v1_xboole_0(B_628)
      | v1_xboole_0(A_631) ) ),
    inference(resolution,[status(thm)],[c_46,c_1993])).

tff(c_2274,plain,(
    ! [A_631,C_627,E_630] :
      ( k2_partfun1(k4_subset_1(A_631,C_627,'#skF_4'),'#skF_2',k1_tmap_1(A_631,'#skF_2',C_627,'#skF_4',E_630,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_631,'#skF_2',C_627,'#skF_4',E_630,'#skF_6'))
      | k2_partfun1(C_627,'#skF_2',E_630,k9_subset_1(A_631,C_627,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_631,C_627,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_630,k1_zfmisc_1(k2_zfmisc_1(C_627,'#skF_2')))
      | ~ v1_funct_2(E_630,C_627,'#skF_2')
      | ~ v1_funct_1(E_630)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_631))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_627,k1_zfmisc_1(A_631))
      | v1_xboole_0(C_627)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_631) ) ),
    inference(resolution,[status(thm)],[c_52,c_2270])).

tff(c_2280,plain,(
    ! [A_631,C_627,E_630] :
      ( k2_partfun1(k4_subset_1(A_631,C_627,'#skF_4'),'#skF_2',k1_tmap_1(A_631,'#skF_2',C_627,'#skF_4',E_630,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_631,'#skF_2',C_627,'#skF_4',E_630,'#skF_6'))
      | k2_partfun1(C_627,'#skF_2',E_630,k9_subset_1(A_631,C_627,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_631,C_627,'#skF_4'))
      | ~ m1_subset_1(E_630,k1_zfmisc_1(k2_zfmisc_1(C_627,'#skF_2')))
      | ~ v1_funct_2(E_630,C_627,'#skF_2')
      | ~ v1_funct_1(E_630)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_631))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_627,k1_zfmisc_1(A_631))
      | v1_xboole_0(C_627)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_841,c_2274])).

tff(c_2892,plain,(
    ! [A_689,C_690,E_691] :
      ( k2_partfun1(k4_subset_1(A_689,C_690,'#skF_4'),'#skF_2',k1_tmap_1(A_689,'#skF_2',C_690,'#skF_4',E_691,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_689,'#skF_2',C_690,'#skF_4',E_691,'#skF_6'))
      | k2_partfun1(C_690,'#skF_2',E_691,k9_subset_1(A_689,C_690,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_689,C_690,'#skF_4'))
      | ~ m1_subset_1(E_691,k1_zfmisc_1(k2_zfmisc_1(C_690,'#skF_2')))
      | ~ v1_funct_2(E_691,C_690,'#skF_2')
      | ~ v1_funct_1(E_691)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_689))
      | ~ m1_subset_1(C_690,k1_zfmisc_1(A_689))
      | v1_xboole_0(C_690)
      | v1_xboole_0(A_689) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2280])).

tff(c_2899,plain,(
    ! [A_689] :
      ( k2_partfun1(k4_subset_1(A_689,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_689,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_689,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_689,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_689,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_689))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_689))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_689) ) ),
    inference(resolution,[status(thm)],[c_58,c_2892])).

tff(c_2909,plain,(
    ! [A_689] :
      ( k2_partfun1(k4_subset_1(A_689,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_689,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_689,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_689,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_689,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_689))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_689))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_689) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_844,c_2899])).

tff(c_3032,plain,(
    ! [A_709] :
      ( k2_partfun1(k4_subset_1(A_709,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_709,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_709,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_709,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_709,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_709))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_709))
      | v1_xboole_0(A_709) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2909])).

tff(c_610,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_872,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_3043,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3032,c_872])).

tff(c_3057,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_971,c_888,c_774,c_774,c_698,c_698,c_1132,c_3043])).

tff(c_3059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3057])).

tff(c_3060,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_5298,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5289,c_3060])).

tff(c_5309,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_3122,c_3120,c_774,c_698,c_774,c_698,c_3340,c_5298])).

tff(c_5311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:59:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/2.82  
% 8.20/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/2.82  %$ v1_funct_2 > v4_relat_1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.20/2.82  
% 8.20/2.82  %Foreground sorts:
% 8.20/2.82  
% 8.20/2.82  
% 8.20/2.82  %Background operators:
% 8.20/2.82  
% 8.20/2.82  
% 8.20/2.82  %Foreground operators:
% 8.20/2.82  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.20/2.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.20/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.20/2.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.20/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.20/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.20/2.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.20/2.82  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.20/2.82  tff('#skF_5', type, '#skF_5': $i).
% 8.20/2.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.20/2.82  tff('#skF_6', type, '#skF_6': $i).
% 8.20/2.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.20/2.82  tff('#skF_2', type, '#skF_2': $i).
% 8.20/2.82  tff('#skF_3', type, '#skF_3': $i).
% 8.20/2.82  tff('#skF_1', type, '#skF_1': $i).
% 8.20/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.20/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.20/2.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.20/2.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.20/2.82  tff('#skF_4', type, '#skF_4': $i).
% 8.20/2.82  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.20/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.20/2.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.20/2.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.20/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.20/2.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.20/2.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.20/2.82  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.20/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.20/2.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.20/2.82  
% 8.20/2.85  tff(f_216, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.20/2.85  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.20/2.85  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.20/2.85  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.20/2.85  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.20/2.85  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.20/2.85  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_relat_1)).
% 8.20/2.85  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 8.20/2.85  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 8.20/2.85  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.20/2.85  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.20/2.85  tff(f_92, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.20/2.85  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.20/2.85  tff(f_174, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.20/2.85  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.20/2.85  tff(c_76, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.20/2.85  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_626, plain, (![C_317, A_318, B_319]: (v1_relat_1(C_317) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.20/2.85  tff(c_633, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_626])).
% 8.20/2.85  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.20/2.85  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.20/2.85  tff(c_636, plain, (![B_322, A_323]: (v4_relat_1(B_322, A_323) | ~r1_tarski(k1_relat_1(B_322), A_323) | ~v1_relat_1(B_322))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.20/2.85  tff(c_641, plain, (![B_322]: (v4_relat_1(B_322, k1_relat_1(B_322)) | ~v1_relat_1(B_322))), inference(resolution, [status(thm)], [c_10, c_636])).
% 8.20/2.85  tff(c_775, plain, (![C_346, A_347, B_348]: (v4_relat_1(C_346, A_347) | ~m1_subset_1(C_346, k1_zfmisc_1(B_348)) | ~v4_relat_1(B_348, A_347) | ~v1_relat_1(B_348))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.20/2.85  tff(c_777, plain, (![A_347]: (v4_relat_1('#skF_6', A_347) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_347) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_775])).
% 8.20/2.85  tff(c_796, plain, (![A_349]: (v4_relat_1('#skF_6', A_349) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_349))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_777])).
% 8.20/2.85  tff(c_800, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_641, c_796])).
% 8.20/2.85  tff(c_803, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_800])).
% 8.20/2.85  tff(c_28, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.20/2.85  tff(c_806, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_803, c_28])).
% 8.20/2.85  tff(c_809, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_633, c_806])).
% 8.20/2.85  tff(c_26, plain, (![C_21, A_19, B_20]: (k7_relat_1(k7_relat_1(C_21, A_19), B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.20/2.85  tff(c_814, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_809, c_26])).
% 8.20/2.85  tff(c_3105, plain, (![B_711]: (k7_relat_1('#skF_6', B_711)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_711))), inference(demodulation, [status(thm), theory('equality')], [c_633, c_814])).
% 8.20/2.85  tff(c_3120, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_3105])).
% 8.20/2.85  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_64, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_668, plain, (![A_328, B_329]: (r1_xboole_0(A_328, B_329) | ~r1_subset_1(A_328, B_329) | v1_xboole_0(B_329) | v1_xboole_0(A_328))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.20/2.85  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.20/2.85  tff(c_764, plain, (![A_344, B_345]: (k3_xboole_0(A_344, B_345)=k1_xboole_0 | ~r1_subset_1(A_344, B_345) | v1_xboole_0(B_345) | v1_xboole_0(A_344))), inference(resolution, [status(thm)], [c_668, c_2])).
% 8.20/2.85  tff(c_770, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_764])).
% 8.20/2.85  tff(c_774, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_770])).
% 8.20/2.85  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_834, plain, (![A_351, B_352, C_353, D_354]: (k2_partfun1(A_351, B_352, C_353, D_354)=k7_relat_1(C_353, D_354) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))) | ~v1_funct_1(C_353))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.20/2.85  tff(c_836, plain, (![D_354]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_354)=k7_relat_1('#skF_6', D_354) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_834])).
% 8.20/2.85  tff(c_841, plain, (![D_354]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_354)=k7_relat_1('#skF_6', D_354))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_836])).
% 8.20/2.85  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_838, plain, (![D_354]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_354)=k7_relat_1('#skF_5', D_354) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_834])).
% 8.20/2.85  tff(c_844, plain, (![D_354]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_354)=k7_relat_1('#skF_5', D_354))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_838])).
% 8.20/2.85  tff(c_686, plain, (![A_332, B_333, C_334]: (k9_subset_1(A_332, B_333, C_334)=k3_xboole_0(B_333, C_334) | ~m1_subset_1(C_334, k1_zfmisc_1(A_332)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.20/2.85  tff(c_698, plain, (![B_333]: (k9_subset_1('#skF_1', B_333, '#skF_4')=k3_xboole_0(B_333, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_686])).
% 8.20/2.85  tff(c_115, plain, (![C_236, A_237, B_238]: (v1_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.20/2.85  tff(c_122, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_115])).
% 8.20/2.85  tff(c_125, plain, (![B_241, A_242]: (v4_relat_1(B_241, A_242) | ~r1_tarski(k1_relat_1(B_241), A_242) | ~v1_relat_1(B_241))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.20/2.85  tff(c_130, plain, (![B_241]: (v4_relat_1(B_241, k1_relat_1(B_241)) | ~v1_relat_1(B_241))), inference(resolution, [status(thm)], [c_10, c_125])).
% 8.20/2.85  tff(c_264, plain, (![C_265, A_266, B_267]: (v4_relat_1(C_265, A_266) | ~m1_subset_1(C_265, k1_zfmisc_1(B_267)) | ~v4_relat_1(B_267, A_266) | ~v1_relat_1(B_267))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.20/2.85  tff(c_266, plain, (![A_266]: (v4_relat_1('#skF_6', A_266) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_266) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_52, c_264])).
% 8.20/2.85  tff(c_292, plain, (![A_272]: (v4_relat_1('#skF_6', A_272) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_272))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_266])).
% 8.20/2.85  tff(c_296, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_130, c_292])).
% 8.20/2.85  tff(c_299, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_296])).
% 8.20/2.85  tff(c_302, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_299, c_28])).
% 8.20/2.85  tff(c_305, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_302])).
% 8.20/2.85  tff(c_309, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_305, c_26])).
% 8.20/2.85  tff(c_466, plain, (![B_288]: (k7_relat_1('#skF_6', B_288)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_288))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_309])).
% 8.20/2.85  tff(c_481, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_466])).
% 8.20/2.85  tff(c_123, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_115])).
% 8.20/2.85  tff(c_268, plain, (![A_266]: (v4_relat_1('#skF_5', A_266) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_266) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_58, c_264])).
% 8.20/2.85  tff(c_325, plain, (![A_274]: (v4_relat_1('#skF_5', A_274) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_274))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_268])).
% 8.20/2.85  tff(c_329, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_130, c_325])).
% 8.20/2.85  tff(c_332, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_329])).
% 8.20/2.85  tff(c_335, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_332, c_28])).
% 8.20/2.85  tff(c_338, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_335])).
% 8.20/2.85  tff(c_355, plain, (![B_20]: (k7_relat_1('#skF_5', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_338, c_26])).
% 8.20/2.85  tff(c_370, plain, (![B_282]: (k7_relat_1('#skF_5', B_282)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_282))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_355])).
% 8.20/2.85  tff(c_385, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_370])).
% 8.20/2.85  tff(c_281, plain, (![A_268, B_269, C_270, D_271]: (k2_partfun1(A_268, B_269, C_270, D_271)=k7_relat_1(C_270, D_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~v1_funct_1(C_270))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.20/2.85  tff(c_285, plain, (![D_271]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_271)=k7_relat_1('#skF_5', D_271) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_281])).
% 8.20/2.85  tff(c_291, plain, (![D_271]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_271)=k7_relat_1('#skF_5', D_271))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_285])).
% 8.20/2.85  tff(c_283, plain, (![D_271]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_271)=k7_relat_1('#skF_6', D_271) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_281])).
% 8.20/2.85  tff(c_288, plain, (![D_271]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_271)=k7_relat_1('#skF_6', D_271))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_283])).
% 8.20/2.85  tff(c_163, plain, (![A_249, B_250]: (r1_xboole_0(A_249, B_250) | ~r1_subset_1(A_249, B_250) | v1_xboole_0(B_250) | v1_xboole_0(A_249))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.20/2.85  tff(c_248, plain, (![A_261, B_262]: (k3_xboole_0(A_261, B_262)=k1_xboole_0 | ~r1_subset_1(A_261, B_262) | v1_xboole_0(B_262) | v1_xboole_0(A_261))), inference(resolution, [status(thm)], [c_163, c_2])).
% 8.20/2.85  tff(c_251, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_248])).
% 8.20/2.85  tff(c_254, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_251])).
% 8.20/2.85  tff(c_172, plain, (![A_251, B_252, C_253]: (k9_subset_1(A_251, B_252, C_253)=k3_xboole_0(B_252, C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(A_251)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.20/2.85  tff(c_184, plain, (![B_252]: (k9_subset_1('#skF_1', B_252, '#skF_4')=k3_xboole_0(B_252, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_172])).
% 8.20/2.85  tff(c_50, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_100, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 8.20/2.85  tff(c_194, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_184, c_100])).
% 8.20/2.85  tff(c_609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_385, c_291, c_288, c_254, c_254, c_194])).
% 8.20/2.85  tff(c_611, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 8.20/2.85  tff(c_709, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_698, c_611])).
% 8.20/2.85  tff(c_3062, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_774, c_774, c_841, c_844, c_709])).
% 8.20/2.85  tff(c_3122, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3120, c_3062])).
% 8.20/2.85  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.20/2.85  tff(c_3246, plain, (![A_723, E_722, F_724, C_719, D_721, B_720]: (v1_funct_1(k1_tmap_1(A_723, B_720, C_719, D_721, E_722, F_724)) | ~m1_subset_1(F_724, k1_zfmisc_1(k2_zfmisc_1(D_721, B_720))) | ~v1_funct_2(F_724, D_721, B_720) | ~v1_funct_1(F_724) | ~m1_subset_1(E_722, k1_zfmisc_1(k2_zfmisc_1(C_719, B_720))) | ~v1_funct_2(E_722, C_719, B_720) | ~v1_funct_1(E_722) | ~m1_subset_1(D_721, k1_zfmisc_1(A_723)) | v1_xboole_0(D_721) | ~m1_subset_1(C_719, k1_zfmisc_1(A_723)) | v1_xboole_0(C_719) | v1_xboole_0(B_720) | v1_xboole_0(A_723))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.20/2.85  tff(c_3248, plain, (![A_723, C_719, E_722]: (v1_funct_1(k1_tmap_1(A_723, '#skF_2', C_719, '#skF_4', E_722, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_722, k1_zfmisc_1(k2_zfmisc_1(C_719, '#skF_2'))) | ~v1_funct_2(E_722, C_719, '#skF_2') | ~v1_funct_1(E_722) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_723)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_719, k1_zfmisc_1(A_723)) | v1_xboole_0(C_719) | v1_xboole_0('#skF_2') | v1_xboole_0(A_723))), inference(resolution, [status(thm)], [c_52, c_3246])).
% 8.20/2.85  tff(c_3253, plain, (![A_723, C_719, E_722]: (v1_funct_1(k1_tmap_1(A_723, '#skF_2', C_719, '#skF_4', E_722, '#skF_6')) | ~m1_subset_1(E_722, k1_zfmisc_1(k2_zfmisc_1(C_719, '#skF_2'))) | ~v1_funct_2(E_722, C_719, '#skF_2') | ~v1_funct_1(E_722) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_723)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_719, k1_zfmisc_1(A_723)) | v1_xboole_0(C_719) | v1_xboole_0('#skF_2') | v1_xboole_0(A_723))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3248])).
% 8.20/2.85  tff(c_3302, plain, (![A_730, C_731, E_732]: (v1_funct_1(k1_tmap_1(A_730, '#skF_2', C_731, '#skF_4', E_732, '#skF_6')) | ~m1_subset_1(E_732, k1_zfmisc_1(k2_zfmisc_1(C_731, '#skF_2'))) | ~v1_funct_2(E_732, C_731, '#skF_2') | ~v1_funct_1(E_732) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_730)) | ~m1_subset_1(C_731, k1_zfmisc_1(A_730)) | v1_xboole_0(C_731) | v1_xboole_0(A_730))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_3253])).
% 8.20/2.85  tff(c_3306, plain, (![A_730]: (v1_funct_1(k1_tmap_1(A_730, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_730)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_730)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_730))), inference(resolution, [status(thm)], [c_58, c_3302])).
% 8.20/2.85  tff(c_3313, plain, (![A_730]: (v1_funct_1(k1_tmap_1(A_730, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_730)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_730)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_730))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3306])).
% 8.20/2.85  tff(c_3333, plain, (![A_742]: (v1_funct_1(k1_tmap_1(A_742, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_742)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_742)) | v1_xboole_0(A_742))), inference(negUnitSimplification, [status(thm)], [c_72, c_3313])).
% 8.20/2.85  tff(c_3336, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_3333])).
% 8.20/2.85  tff(c_3339, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3336])).
% 8.20/2.85  tff(c_3340, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_3339])).
% 8.20/2.85  tff(c_46, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.20/2.85  tff(c_44, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.20/2.85  tff(c_3476, plain, (![D_768, C_767, E_764, B_765, F_766, A_763]: (k2_partfun1(k4_subset_1(A_763, C_767, D_768), B_765, k1_tmap_1(A_763, B_765, C_767, D_768, E_764, F_766), C_767)=E_764 | ~m1_subset_1(k1_tmap_1(A_763, B_765, C_767, D_768, E_764, F_766), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_763, C_767, D_768), B_765))) | ~v1_funct_2(k1_tmap_1(A_763, B_765, C_767, D_768, E_764, F_766), k4_subset_1(A_763, C_767, D_768), B_765) | ~v1_funct_1(k1_tmap_1(A_763, B_765, C_767, D_768, E_764, F_766)) | k2_partfun1(D_768, B_765, F_766, k9_subset_1(A_763, C_767, D_768))!=k2_partfun1(C_767, B_765, E_764, k9_subset_1(A_763, C_767, D_768)) | ~m1_subset_1(F_766, k1_zfmisc_1(k2_zfmisc_1(D_768, B_765))) | ~v1_funct_2(F_766, D_768, B_765) | ~v1_funct_1(F_766) | ~m1_subset_1(E_764, k1_zfmisc_1(k2_zfmisc_1(C_767, B_765))) | ~v1_funct_2(E_764, C_767, B_765) | ~v1_funct_1(E_764) | ~m1_subset_1(D_768, k1_zfmisc_1(A_763)) | v1_xboole_0(D_768) | ~m1_subset_1(C_767, k1_zfmisc_1(A_763)) | v1_xboole_0(C_767) | v1_xboole_0(B_765) | v1_xboole_0(A_763))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.20/2.85  tff(c_4158, plain, (![F_893, D_890, C_888, E_891, B_889, A_892]: (k2_partfun1(k4_subset_1(A_892, C_888, D_890), B_889, k1_tmap_1(A_892, B_889, C_888, D_890, E_891, F_893), C_888)=E_891 | ~v1_funct_2(k1_tmap_1(A_892, B_889, C_888, D_890, E_891, F_893), k4_subset_1(A_892, C_888, D_890), B_889) | ~v1_funct_1(k1_tmap_1(A_892, B_889, C_888, D_890, E_891, F_893)) | k2_partfun1(D_890, B_889, F_893, k9_subset_1(A_892, C_888, D_890))!=k2_partfun1(C_888, B_889, E_891, k9_subset_1(A_892, C_888, D_890)) | ~m1_subset_1(F_893, k1_zfmisc_1(k2_zfmisc_1(D_890, B_889))) | ~v1_funct_2(F_893, D_890, B_889) | ~v1_funct_1(F_893) | ~m1_subset_1(E_891, k1_zfmisc_1(k2_zfmisc_1(C_888, B_889))) | ~v1_funct_2(E_891, C_888, B_889) | ~v1_funct_1(E_891) | ~m1_subset_1(D_890, k1_zfmisc_1(A_892)) | v1_xboole_0(D_890) | ~m1_subset_1(C_888, k1_zfmisc_1(A_892)) | v1_xboole_0(C_888) | v1_xboole_0(B_889) | v1_xboole_0(A_892))), inference(resolution, [status(thm)], [c_44, c_3476])).
% 8.20/2.85  tff(c_4746, plain, (![D_988, F_991, C_986, E_989, A_990, B_987]: (k2_partfun1(k4_subset_1(A_990, C_986, D_988), B_987, k1_tmap_1(A_990, B_987, C_986, D_988, E_989, F_991), C_986)=E_989 | ~v1_funct_1(k1_tmap_1(A_990, B_987, C_986, D_988, E_989, F_991)) | k2_partfun1(D_988, B_987, F_991, k9_subset_1(A_990, C_986, D_988))!=k2_partfun1(C_986, B_987, E_989, k9_subset_1(A_990, C_986, D_988)) | ~m1_subset_1(F_991, k1_zfmisc_1(k2_zfmisc_1(D_988, B_987))) | ~v1_funct_2(F_991, D_988, B_987) | ~v1_funct_1(F_991) | ~m1_subset_1(E_989, k1_zfmisc_1(k2_zfmisc_1(C_986, B_987))) | ~v1_funct_2(E_989, C_986, B_987) | ~v1_funct_1(E_989) | ~m1_subset_1(D_988, k1_zfmisc_1(A_990)) | v1_xboole_0(D_988) | ~m1_subset_1(C_986, k1_zfmisc_1(A_990)) | v1_xboole_0(C_986) | v1_xboole_0(B_987) | v1_xboole_0(A_990))), inference(resolution, [status(thm)], [c_46, c_4158])).
% 8.20/2.85  tff(c_4750, plain, (![A_990, C_986, E_989]: (k2_partfun1(k4_subset_1(A_990, C_986, '#skF_4'), '#skF_2', k1_tmap_1(A_990, '#skF_2', C_986, '#skF_4', E_989, '#skF_6'), C_986)=E_989 | ~v1_funct_1(k1_tmap_1(A_990, '#skF_2', C_986, '#skF_4', E_989, '#skF_6')) | k2_partfun1(C_986, '#skF_2', E_989, k9_subset_1(A_990, C_986, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_990, C_986, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_989, k1_zfmisc_1(k2_zfmisc_1(C_986, '#skF_2'))) | ~v1_funct_2(E_989, C_986, '#skF_2') | ~v1_funct_1(E_989) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_990)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_986, k1_zfmisc_1(A_990)) | v1_xboole_0(C_986) | v1_xboole_0('#skF_2') | v1_xboole_0(A_990))), inference(resolution, [status(thm)], [c_52, c_4746])).
% 8.20/2.85  tff(c_4756, plain, (![A_990, C_986, E_989]: (k2_partfun1(k4_subset_1(A_990, C_986, '#skF_4'), '#skF_2', k1_tmap_1(A_990, '#skF_2', C_986, '#skF_4', E_989, '#skF_6'), C_986)=E_989 | ~v1_funct_1(k1_tmap_1(A_990, '#skF_2', C_986, '#skF_4', E_989, '#skF_6')) | k2_partfun1(C_986, '#skF_2', E_989, k9_subset_1(A_990, C_986, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_990, C_986, '#skF_4')) | ~m1_subset_1(E_989, k1_zfmisc_1(k2_zfmisc_1(C_986, '#skF_2'))) | ~v1_funct_2(E_989, C_986, '#skF_2') | ~v1_funct_1(E_989) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_990)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_986, k1_zfmisc_1(A_990)) | v1_xboole_0(C_986) | v1_xboole_0('#skF_2') | v1_xboole_0(A_990))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_841, c_4750])).
% 8.20/2.85  tff(c_5270, plain, (![A_1042, C_1043, E_1044]: (k2_partfun1(k4_subset_1(A_1042, C_1043, '#skF_4'), '#skF_2', k1_tmap_1(A_1042, '#skF_2', C_1043, '#skF_4', E_1044, '#skF_6'), C_1043)=E_1044 | ~v1_funct_1(k1_tmap_1(A_1042, '#skF_2', C_1043, '#skF_4', E_1044, '#skF_6')) | k2_partfun1(C_1043, '#skF_2', E_1044, k9_subset_1(A_1042, C_1043, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1042, C_1043, '#skF_4')) | ~m1_subset_1(E_1044, k1_zfmisc_1(k2_zfmisc_1(C_1043, '#skF_2'))) | ~v1_funct_2(E_1044, C_1043, '#skF_2') | ~v1_funct_1(E_1044) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1042)) | ~m1_subset_1(C_1043, k1_zfmisc_1(A_1042)) | v1_xboole_0(C_1043) | v1_xboole_0(A_1042))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_4756])).
% 8.20/2.85  tff(c_5277, plain, (![A_1042]: (k2_partfun1(k4_subset_1(A_1042, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1042, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1042, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1042, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1042, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1042)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1042)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1042))), inference(resolution, [status(thm)], [c_58, c_5270])).
% 8.20/2.85  tff(c_5287, plain, (![A_1042]: (k2_partfun1(k4_subset_1(A_1042, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1042, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1042, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1042, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1042, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1042)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1042)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1042))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_844, c_5277])).
% 8.20/2.85  tff(c_5289, plain, (![A_1045]: (k2_partfun1(k4_subset_1(A_1045, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1045, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1045, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1045, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1045, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1045)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1045)) | v1_xboole_0(A_1045))), inference(negUnitSimplification, [status(thm)], [c_72, c_5287])).
% 8.20/2.85  tff(c_634, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_626])).
% 8.20/2.85  tff(c_779, plain, (![A_347]: (v4_relat_1('#skF_5', A_347) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_347) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_58, c_775])).
% 8.20/2.85  tff(c_820, plain, (![A_350]: (v4_relat_1('#skF_5', A_350) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_350))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_779])).
% 8.20/2.85  tff(c_824, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_641, c_820])).
% 8.20/2.85  tff(c_827, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_824])).
% 8.20/2.85  tff(c_830, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_827, c_28])).
% 8.20/2.85  tff(c_833, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_634, c_830])).
% 8.20/2.85  tff(c_848, plain, (![B_20]: (k7_relat_1('#skF_5', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_833, c_26])).
% 8.20/2.85  tff(c_956, plain, (![B_360]: (k7_relat_1('#skF_5', B_360)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_360))), inference(demodulation, [status(thm), theory('equality')], [c_634, c_848])).
% 8.20/2.85  tff(c_971, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_956])).
% 8.20/2.85  tff(c_873, plain, (![B_357]: (k7_relat_1('#skF_6', B_357)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_357))), inference(demodulation, [status(thm), theory('equality')], [c_633, c_814])).
% 8.20/2.85  tff(c_888, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_873])).
% 8.20/2.85  tff(c_1051, plain, (![D_372, A_374, B_371, E_373, C_370, F_375]: (v1_funct_1(k1_tmap_1(A_374, B_371, C_370, D_372, E_373, F_375)) | ~m1_subset_1(F_375, k1_zfmisc_1(k2_zfmisc_1(D_372, B_371))) | ~v1_funct_2(F_375, D_372, B_371) | ~v1_funct_1(F_375) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_370, B_371))) | ~v1_funct_2(E_373, C_370, B_371) | ~v1_funct_1(E_373) | ~m1_subset_1(D_372, k1_zfmisc_1(A_374)) | v1_xboole_0(D_372) | ~m1_subset_1(C_370, k1_zfmisc_1(A_374)) | v1_xboole_0(C_370) | v1_xboole_0(B_371) | v1_xboole_0(A_374))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.20/2.85  tff(c_1053, plain, (![A_374, C_370, E_373]: (v1_funct_1(k1_tmap_1(A_374, '#skF_2', C_370, '#skF_4', E_373, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_370, '#skF_2'))) | ~v1_funct_2(E_373, C_370, '#skF_2') | ~v1_funct_1(E_373) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_374)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_370, k1_zfmisc_1(A_374)) | v1_xboole_0(C_370) | v1_xboole_0('#skF_2') | v1_xboole_0(A_374))), inference(resolution, [status(thm)], [c_52, c_1051])).
% 8.20/2.85  tff(c_1058, plain, (![A_374, C_370, E_373]: (v1_funct_1(k1_tmap_1(A_374, '#skF_2', C_370, '#skF_4', E_373, '#skF_6')) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_370, '#skF_2'))) | ~v1_funct_2(E_373, C_370, '#skF_2') | ~v1_funct_1(E_373) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_374)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_370, k1_zfmisc_1(A_374)) | v1_xboole_0(C_370) | v1_xboole_0('#skF_2') | v1_xboole_0(A_374))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1053])).
% 8.20/2.85  tff(c_1071, plain, (![A_378, C_379, E_380]: (v1_funct_1(k1_tmap_1(A_378, '#skF_2', C_379, '#skF_4', E_380, '#skF_6')) | ~m1_subset_1(E_380, k1_zfmisc_1(k2_zfmisc_1(C_379, '#skF_2'))) | ~v1_funct_2(E_380, C_379, '#skF_2') | ~v1_funct_1(E_380) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_378)) | ~m1_subset_1(C_379, k1_zfmisc_1(A_378)) | v1_xboole_0(C_379) | v1_xboole_0(A_378))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_1058])).
% 8.20/2.85  tff(c_1075, plain, (![A_378]: (v1_funct_1(k1_tmap_1(A_378, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_378)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_378)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_378))), inference(resolution, [status(thm)], [c_58, c_1071])).
% 8.20/2.85  tff(c_1082, plain, (![A_378]: (v1_funct_1(k1_tmap_1(A_378, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_378)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_378)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_378))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1075])).
% 8.20/2.85  tff(c_1125, plain, (![A_396]: (v1_funct_1(k1_tmap_1(A_396, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_396)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_396)) | v1_xboole_0(A_396))), inference(negUnitSimplification, [status(thm)], [c_72, c_1082])).
% 8.20/2.85  tff(c_1128, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_1125])).
% 8.20/2.85  tff(c_1131, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1128])).
% 8.20/2.85  tff(c_1132, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1131])).
% 8.20/2.85  tff(c_1253, plain, (![F_412, A_409, C_413, E_410, B_411, D_414]: (k2_partfun1(k4_subset_1(A_409, C_413, D_414), B_411, k1_tmap_1(A_409, B_411, C_413, D_414, E_410, F_412), D_414)=F_412 | ~m1_subset_1(k1_tmap_1(A_409, B_411, C_413, D_414, E_410, F_412), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_409, C_413, D_414), B_411))) | ~v1_funct_2(k1_tmap_1(A_409, B_411, C_413, D_414, E_410, F_412), k4_subset_1(A_409, C_413, D_414), B_411) | ~v1_funct_1(k1_tmap_1(A_409, B_411, C_413, D_414, E_410, F_412)) | k2_partfun1(D_414, B_411, F_412, k9_subset_1(A_409, C_413, D_414))!=k2_partfun1(C_413, B_411, E_410, k9_subset_1(A_409, C_413, D_414)) | ~m1_subset_1(F_412, k1_zfmisc_1(k2_zfmisc_1(D_414, B_411))) | ~v1_funct_2(F_412, D_414, B_411) | ~v1_funct_1(F_412) | ~m1_subset_1(E_410, k1_zfmisc_1(k2_zfmisc_1(C_413, B_411))) | ~v1_funct_2(E_410, C_413, B_411) | ~v1_funct_1(E_410) | ~m1_subset_1(D_414, k1_zfmisc_1(A_409)) | v1_xboole_0(D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(A_409)) | v1_xboole_0(C_413) | v1_xboole_0(B_411) | v1_xboole_0(A_409))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.20/2.85  tff(c_1993, plain, (![C_546, B_547, D_548, E_549, F_551, A_550]: (k2_partfun1(k4_subset_1(A_550, C_546, D_548), B_547, k1_tmap_1(A_550, B_547, C_546, D_548, E_549, F_551), D_548)=F_551 | ~v1_funct_2(k1_tmap_1(A_550, B_547, C_546, D_548, E_549, F_551), k4_subset_1(A_550, C_546, D_548), B_547) | ~v1_funct_1(k1_tmap_1(A_550, B_547, C_546, D_548, E_549, F_551)) | k2_partfun1(D_548, B_547, F_551, k9_subset_1(A_550, C_546, D_548))!=k2_partfun1(C_546, B_547, E_549, k9_subset_1(A_550, C_546, D_548)) | ~m1_subset_1(F_551, k1_zfmisc_1(k2_zfmisc_1(D_548, B_547))) | ~v1_funct_2(F_551, D_548, B_547) | ~v1_funct_1(F_551) | ~m1_subset_1(E_549, k1_zfmisc_1(k2_zfmisc_1(C_546, B_547))) | ~v1_funct_2(E_549, C_546, B_547) | ~v1_funct_1(E_549) | ~m1_subset_1(D_548, k1_zfmisc_1(A_550)) | v1_xboole_0(D_548) | ~m1_subset_1(C_546, k1_zfmisc_1(A_550)) | v1_xboole_0(C_546) | v1_xboole_0(B_547) | v1_xboole_0(A_550))), inference(resolution, [status(thm)], [c_44, c_1253])).
% 8.20/2.85  tff(c_2270, plain, (![B_628, E_630, A_631, F_632, C_627, D_629]: (k2_partfun1(k4_subset_1(A_631, C_627, D_629), B_628, k1_tmap_1(A_631, B_628, C_627, D_629, E_630, F_632), D_629)=F_632 | ~v1_funct_1(k1_tmap_1(A_631, B_628, C_627, D_629, E_630, F_632)) | k2_partfun1(D_629, B_628, F_632, k9_subset_1(A_631, C_627, D_629))!=k2_partfun1(C_627, B_628, E_630, k9_subset_1(A_631, C_627, D_629)) | ~m1_subset_1(F_632, k1_zfmisc_1(k2_zfmisc_1(D_629, B_628))) | ~v1_funct_2(F_632, D_629, B_628) | ~v1_funct_1(F_632) | ~m1_subset_1(E_630, k1_zfmisc_1(k2_zfmisc_1(C_627, B_628))) | ~v1_funct_2(E_630, C_627, B_628) | ~v1_funct_1(E_630) | ~m1_subset_1(D_629, k1_zfmisc_1(A_631)) | v1_xboole_0(D_629) | ~m1_subset_1(C_627, k1_zfmisc_1(A_631)) | v1_xboole_0(C_627) | v1_xboole_0(B_628) | v1_xboole_0(A_631))), inference(resolution, [status(thm)], [c_46, c_1993])).
% 8.20/2.85  tff(c_2274, plain, (![A_631, C_627, E_630]: (k2_partfun1(k4_subset_1(A_631, C_627, '#skF_4'), '#skF_2', k1_tmap_1(A_631, '#skF_2', C_627, '#skF_4', E_630, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_631, '#skF_2', C_627, '#skF_4', E_630, '#skF_6')) | k2_partfun1(C_627, '#skF_2', E_630, k9_subset_1(A_631, C_627, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_631, C_627, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_630, k1_zfmisc_1(k2_zfmisc_1(C_627, '#skF_2'))) | ~v1_funct_2(E_630, C_627, '#skF_2') | ~v1_funct_1(E_630) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_631)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_627, k1_zfmisc_1(A_631)) | v1_xboole_0(C_627) | v1_xboole_0('#skF_2') | v1_xboole_0(A_631))), inference(resolution, [status(thm)], [c_52, c_2270])).
% 8.20/2.85  tff(c_2280, plain, (![A_631, C_627, E_630]: (k2_partfun1(k4_subset_1(A_631, C_627, '#skF_4'), '#skF_2', k1_tmap_1(A_631, '#skF_2', C_627, '#skF_4', E_630, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_631, '#skF_2', C_627, '#skF_4', E_630, '#skF_6')) | k2_partfun1(C_627, '#skF_2', E_630, k9_subset_1(A_631, C_627, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_631, C_627, '#skF_4')) | ~m1_subset_1(E_630, k1_zfmisc_1(k2_zfmisc_1(C_627, '#skF_2'))) | ~v1_funct_2(E_630, C_627, '#skF_2') | ~v1_funct_1(E_630) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_631)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_627, k1_zfmisc_1(A_631)) | v1_xboole_0(C_627) | v1_xboole_0('#skF_2') | v1_xboole_0(A_631))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_841, c_2274])).
% 8.20/2.85  tff(c_2892, plain, (![A_689, C_690, E_691]: (k2_partfun1(k4_subset_1(A_689, C_690, '#skF_4'), '#skF_2', k1_tmap_1(A_689, '#skF_2', C_690, '#skF_4', E_691, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_689, '#skF_2', C_690, '#skF_4', E_691, '#skF_6')) | k2_partfun1(C_690, '#skF_2', E_691, k9_subset_1(A_689, C_690, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_689, C_690, '#skF_4')) | ~m1_subset_1(E_691, k1_zfmisc_1(k2_zfmisc_1(C_690, '#skF_2'))) | ~v1_funct_2(E_691, C_690, '#skF_2') | ~v1_funct_1(E_691) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_689)) | ~m1_subset_1(C_690, k1_zfmisc_1(A_689)) | v1_xboole_0(C_690) | v1_xboole_0(A_689))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2280])).
% 8.20/2.85  tff(c_2899, plain, (![A_689]: (k2_partfun1(k4_subset_1(A_689, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_689, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_689, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_689, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_689, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_689)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_689)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_689))), inference(resolution, [status(thm)], [c_58, c_2892])).
% 8.20/2.85  tff(c_2909, plain, (![A_689]: (k2_partfun1(k4_subset_1(A_689, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_689, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_689, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_689, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_689, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_689)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_689)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_689))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_844, c_2899])).
% 8.20/2.85  tff(c_3032, plain, (![A_709]: (k2_partfun1(k4_subset_1(A_709, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_709, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_709, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_709, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_709, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_709)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_709)) | v1_xboole_0(A_709))), inference(negUnitSimplification, [status(thm)], [c_72, c_2909])).
% 8.20/2.85  tff(c_610, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 8.20/2.85  tff(c_872, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_610])).
% 8.20/2.85  tff(c_3043, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3032, c_872])).
% 8.20/2.85  tff(c_3057, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_971, c_888, c_774, c_774, c_698, c_698, c_1132, c_3043])).
% 8.20/2.85  tff(c_3059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3057])).
% 8.20/2.85  tff(c_3060, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_610])).
% 8.20/2.85  tff(c_5298, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5289, c_3060])).
% 8.20/2.85  tff(c_5309, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_3122, c_3120, c_774, c_698, c_774, c_698, c_3340, c_5298])).
% 8.20/2.85  tff(c_5311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5309])).
% 8.20/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.20/2.85  
% 8.20/2.85  Inference rules
% 8.20/2.85  ----------------------
% 8.20/2.85  #Ref     : 0
% 8.20/2.85  #Sup     : 1103
% 8.20/2.85  #Fact    : 0
% 8.20/2.85  #Define  : 0
% 8.20/2.85  #Split   : 53
% 8.20/2.85  #Chain   : 0
% 8.20/2.85  #Close   : 0
% 8.20/2.85  
% 8.20/2.85  Ordering : KBO
% 8.20/2.85  
% 8.20/2.85  Simplification rules
% 8.20/2.85  ----------------------
% 8.20/2.85  #Subsume      : 321
% 8.20/2.85  #Demod        : 1011
% 8.20/2.85  #Tautology    : 334
% 8.20/2.85  #SimpNegUnit  : 216
% 8.20/2.85  #BackRed      : 4
% 8.20/2.85  
% 8.20/2.85  #Partial instantiations: 0
% 8.20/2.85  #Strategies tried      : 1
% 8.20/2.85  
% 8.20/2.85  Timing (in seconds)
% 8.20/2.85  ----------------------
% 8.20/2.85  Preprocessing        : 0.42
% 8.20/2.85  Parsing              : 0.21
% 8.20/2.85  CNF conversion       : 0.06
% 8.20/2.85  Main loop            : 1.65
% 8.20/2.85  Inferencing          : 0.59
% 8.20/2.85  Reduction            : 0.59
% 8.20/2.85  Demodulation         : 0.43
% 8.20/2.85  BG Simplification    : 0.06
% 8.20/2.85  Subsumption          : 0.32
% 8.20/2.85  Abstraction          : 0.07
% 8.20/2.85  MUC search           : 0.00
% 8.20/2.85  Cooper               : 0.00
% 8.20/2.85  Total                : 2.13
% 8.20/2.85  Index Insertion      : 0.00
% 8.20/2.85  Index Deletion       : 0.00
% 8.20/2.85  Index Matching       : 0.00
% 8.20/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
