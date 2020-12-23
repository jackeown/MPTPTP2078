%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:19 EST 2020

% Result     : Theorem 25.53s
% Output     : CNFRefutation 25.66s
% Verified   : 
% Statistics : Number of formulae       :  208 (1105 expanded)
%              Number of leaves         :   42 ( 405 expanded)
%              Depth                    :   15
%              Number of atoms          :  705 (5474 expanded)
%              Number of equality atoms :  156 (1054 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_209,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_167,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_133,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_58,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_3173,plain,(
    ! [A_433,B_434] :
      ( r1_xboole_0(A_433,B_434)
      | ~ r1_subset_1(A_433,B_434)
      | v1_xboole_0(B_434)
      | v1_xboole_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3566,plain,(
    ! [B_459,A_460] :
      ( r1_xboole_0(B_459,A_460)
      | ~ r1_subset_1(A_460,B_459)
      | v1_xboole_0(B_459)
      | v1_xboole_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_3173,c_6])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_89,plain,(
    ! [C_227,A_228,B_229] :
      ( v1_relat_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_97,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_3098,plain,(
    ! [C_419,A_420,B_421] :
      ( v4_relat_1(C_419,A_420)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3106,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_3098])).

tff(c_3107,plain,(
    ! [B_422,A_423] :
      ( k7_relat_1(B_422,A_423) = B_422
      | ~ v4_relat_1(B_422,A_423)
      | ~ v1_relat_1(B_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3110,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3106,c_3107])).

tff(c_3116,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_3110])).

tff(c_3190,plain,(
    ! [C_435,A_436,B_437] :
      ( k7_relat_1(k7_relat_1(C_435,A_436),B_437) = k1_xboole_0
      | ~ r1_xboole_0(A_436,B_437)
      | ~ v1_relat_1(C_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3208,plain,(
    ! [B_437] :
      ( k7_relat_1('#skF_6',B_437) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_437)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3116,c_3190])).

tff(c_3214,plain,(
    ! [B_437] :
      ( k7_relat_1('#skF_6',B_437) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_3208])).

tff(c_3574,plain,(
    ! [A_460] :
      ( k7_relat_1('#skF_6',A_460) = k1_xboole_0
      | ~ r1_subset_1(A_460,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_3566,c_3214])).

tff(c_3604,plain,(
    ! [A_461] :
      ( k7_relat_1('#skF_6',A_461) = k1_xboole_0
      | ~ r1_subset_1(A_461,'#skF_4')
      | v1_xboole_0(A_461) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3574])).

tff(c_3607,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3604])).

tff(c_3610,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3607])).

tff(c_3137,plain,(
    ! [B_427,A_428] :
      ( r1_xboole_0(k1_relat_1(B_427),A_428)
      | k7_relat_1(B_427,A_428) != k1_xboole_0
      | ~ v1_relat_1(B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_39897,plain,(
    ! [B_1159,A_1160] :
      ( k3_xboole_0(k1_relat_1(B_1159),A_1160) = k1_xboole_0
      | k7_relat_1(B_1159,A_1160) != k1_xboole_0
      | ~ v1_relat_1(B_1159) ) ),
    inference(resolution,[status(thm)],[c_3137,c_2])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,k3_xboole_0(k1_relat_1(B_9),A_8)) = k7_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41783,plain,(
    ! [B_1270,A_1271] :
      ( k7_relat_1(B_1270,k1_xboole_0) = k7_relat_1(B_1270,A_1271)
      | ~ v1_relat_1(B_1270)
      | k7_relat_1(B_1270,A_1271) != k1_xboole_0
      | ~ v1_relat_1(B_1270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39897,c_10])).

tff(c_41785,plain,(
    ! [A_1271] :
      ( k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6',A_1271)
      | k7_relat_1('#skF_6',A_1271) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_97,c_41783])).

tff(c_41794,plain,(
    ! [A_1272] :
      ( k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6',A_1272)
      | k7_relat_1('#skF_6',A_1272) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_41785])).

tff(c_41816,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3610,c_41794])).

tff(c_41846,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_41816])).

tff(c_3950,plain,(
    ! [A_479,B_480] :
      ( k3_xboole_0(A_479,B_480) = k1_xboole_0
      | ~ r1_subset_1(A_479,B_480)
      | v1_xboole_0(B_480)
      | v1_xboole_0(A_479) ) ),
    inference(resolution,[status(thm)],[c_3173,c_2])).

tff(c_3956,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3950])).

tff(c_3962,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_3956])).

tff(c_3516,plain,(
    ! [A_451,B_452,C_453] :
      ( k9_subset_1(A_451,B_452,C_453) = k3_xboole_0(B_452,C_453)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(A_451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3528,plain,(
    ! [B_452] : k9_subset_1('#skF_1',B_452,'#skF_4') = k3_xboole_0(B_452,'#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3516])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_3661,plain,(
    ! [A_463,B_464,C_465,D_466] :
      ( k2_partfun1(A_463,B_464,C_465,D_466) = k7_relat_1(C_465,D_466)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))
      | ~ v1_funct_1(C_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3665,plain,(
    ! [D_466] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_466) = k7_relat_1('#skF_6',D_466)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_3661])).

tff(c_3671,plain,(
    ! [D_466] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_466) = k7_relat_1('#skF_6',D_466) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3665])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_3663,plain,(
    ! [D_466] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_466) = k7_relat_1('#skF_5',D_466)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_3661])).

tff(c_3668,plain,(
    ! [D_466] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_466) = k7_relat_1('#skF_5',D_466) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3663])).

tff(c_148,plain,(
    ! [A_242,B_243] :
      ( r1_xboole_0(A_242,B_243)
      | ~ r1_subset_1(A_242,B_243)
      | v1_xboole_0(B_243)
      | v1_xboole_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_209,plain,(
    ! [B_250,A_251] :
      ( r1_xboole_0(B_250,A_251)
      | ~ r1_subset_1(A_251,B_250)
      | v1_xboole_0(B_250)
      | v1_xboole_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_148,c_6])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r1_subset_1(A_17,B_18)
      | ~ r1_xboole_0(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_226,plain,(
    ! [B_252,A_253] :
      ( r1_subset_1(B_252,A_253)
      | ~ r1_subset_1(A_253,B_252)
      | v1_xboole_0(B_252)
      | v1_xboole_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_209,c_20])).

tff(c_228,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_226])).

tff(c_231,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_228])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | ~ r1_subset_1(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_100,plain,(
    ! [C_232,A_233,B_234] :
      ( v4_relat_1(C_232,A_233)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_108,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_100])).

tff(c_118,plain,(
    ! [B_238,A_239] :
      ( k7_relat_1(B_238,A_239) = B_238
      | ~ v4_relat_1(B_238,A_239)
      | ~ v1_relat_1(B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_108,c_118])).

tff(c_127,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_121])).

tff(c_287,plain,(
    ! [C_261,A_262,B_263] :
      ( k7_relat_1(k7_relat_1(C_261,A_262),B_263) = k1_xboole_0
      | ~ r1_xboole_0(A_262,B_263)
      | ~ v1_relat_1(C_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_305,plain,(
    ! [B_263] :
      ( k7_relat_1('#skF_6',B_263) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_263)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_287])).

tff(c_342,plain,(
    ! [B_265] :
      ( k7_relat_1('#skF_6',B_265) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_305])).

tff(c_354,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_342])).

tff(c_392,plain,(
    ! [B_267] :
      ( k7_relat_1('#skF_6',B_267) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_267)
      | v1_xboole_0(B_267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_354])).

tff(c_395,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_392])).

tff(c_398,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_395])).

tff(c_160,plain,(
    ! [B_244,A_245] :
      ( r1_xboole_0(k1_relat_1(B_244),A_245)
      | k7_relat_1(B_244,A_245) != k1_xboole_0
      | ~ v1_relat_1(B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1030,plain,(
    ! [B_308,A_309] :
      ( k3_xboole_0(k1_relat_1(B_308),A_309) = k1_xboole_0
      | k7_relat_1(B_308,A_309) != k1_xboole_0
      | ~ v1_relat_1(B_308) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_2837,plain,(
    ! [B_409,A_410] :
      ( k7_relat_1(B_409,k1_xboole_0) = k7_relat_1(B_409,A_410)
      | ~ v1_relat_1(B_409)
      | k7_relat_1(B_409,A_410) != k1_xboole_0
      | ~ v1_relat_1(B_409) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_10])).

tff(c_2839,plain,(
    ! [A_410] :
      ( k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6',A_410)
      | k7_relat_1('#skF_6',A_410) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_97,c_2837])).

tff(c_2848,plain,(
    ! [A_411] :
      ( k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6',A_411)
      | k7_relat_1('#skF_6',A_411) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_2839])).

tff(c_2877,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_2848])).

tff(c_2904,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_2877])).

tff(c_944,plain,(
    ! [A_298,B_299] :
      ( k3_xboole_0(A_298,B_299) = k1_xboole_0
      | ~ r1_subset_1(A_298,B_299)
      | v1_xboole_0(B_299)
      | v1_xboole_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_950,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_944])).

tff(c_956,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_950])).

tff(c_662,plain,(
    ! [A_276,B_277,C_278,D_279] :
      ( k2_partfun1(A_276,B_277,C_278,D_279) = k7_relat_1(C_278,D_279)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ v1_funct_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_666,plain,(
    ! [D_279] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_279) = k7_relat_1('#skF_6',D_279)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_662])).

tff(c_672,plain,(
    ! [D_279] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_279) = k7_relat_1('#skF_6',D_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_666])).

tff(c_664,plain,(
    ! [D_279] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_279) = k7_relat_1('#skF_5',D_279)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_662])).

tff(c_669,plain,(
    ! [D_279] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_279) = k7_relat_1('#skF_5',D_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_664])).

tff(c_237,plain,(
    ! [A_254,B_255,C_256] :
      ( k9_subset_1(A_254,B_255,C_256) = k3_xboole_0(B_255,C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(A_254)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_249,plain,(
    ! [B_255] : k9_subset_1('#skF_1',B_255,'#skF_4') = k3_xboole_0(B_255,'#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_237])).

tff(c_44,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_98,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_259,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_249,c_98])).

tff(c_1624,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_956,c_672,c_669,c_259])).

tff(c_2907,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2904,c_1624])).

tff(c_159,plain,(
    ! [B_243,A_242] :
      ( r1_xboole_0(B_243,A_242)
      | ~ r1_subset_1(A_242,B_243)
      | v1_xboole_0(B_243)
      | v1_xboole_0(A_242) ) ),
    inference(resolution,[status(thm)],[c_148,c_6])).

tff(c_96,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_107,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_100])).

tff(c_124,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_107,c_118])).

tff(c_130,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_124])).

tff(c_302,plain,(
    ! [B_263] :
      ( k7_relat_1('#skF_5',B_263) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_263)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_287])).

tff(c_312,plain,(
    ! [B_264] :
      ( k7_relat_1('#skF_5',B_264) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_302])).

tff(c_316,plain,(
    ! [A_242] :
      ( k7_relat_1('#skF_5',A_242) = k1_xboole_0
      | ~ r1_subset_1(A_242,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_242) ) ),
    inference(resolution,[status(thm)],[c_159,c_312])).

tff(c_552,plain,(
    ! [A_273] :
      ( k7_relat_1('#skF_5',A_273) = k1_xboole_0
      | ~ r1_subset_1(A_273,'#skF_3')
      | v1_xboole_0(A_273) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_316])).

tff(c_555,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_231,c_552])).

tff(c_558,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_555])).

tff(c_2841,plain,(
    ! [A_410] :
      ( k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_5',A_410)
      | k7_relat_1('#skF_5',A_410) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_96,c_2837])).

tff(c_3040,plain,(
    ! [A_416] :
      ( k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_5',A_416)
      | k7_relat_1('#skF_5',A_416) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2841])).

tff(c_3062,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_3040])).

tff(c_3092,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_3062])).

tff(c_3094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2907,c_3092])).

tff(c_3096,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_3821,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3671,c_3668,c_3528,c_3528,c_3096])).

tff(c_3963,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3962,c_3962,c_3821])).

tff(c_41854,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41846,c_3963])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_40024,plain,(
    ! [D_1171,F_1167,E_1168,C_1169,A_1172,B_1170] :
      ( v1_funct_1(k1_tmap_1(A_1172,B_1170,C_1169,D_1171,E_1168,F_1167))
      | ~ m1_subset_1(F_1167,k1_zfmisc_1(k2_zfmisc_1(D_1171,B_1170)))
      | ~ v1_funct_2(F_1167,D_1171,B_1170)
      | ~ v1_funct_1(F_1167)
      | ~ m1_subset_1(E_1168,k1_zfmisc_1(k2_zfmisc_1(C_1169,B_1170)))
      | ~ v1_funct_2(E_1168,C_1169,B_1170)
      | ~ v1_funct_1(E_1168)
      | ~ m1_subset_1(D_1171,k1_zfmisc_1(A_1172))
      | v1_xboole_0(D_1171)
      | ~ m1_subset_1(C_1169,k1_zfmisc_1(A_1172))
      | v1_xboole_0(C_1169)
      | v1_xboole_0(B_1170)
      | v1_xboole_0(A_1172) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_40028,plain,(
    ! [A_1172,C_1169,E_1168] :
      ( v1_funct_1(k1_tmap_1(A_1172,'#skF_2',C_1169,'#skF_4',E_1168,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1168,k1_zfmisc_1(k2_zfmisc_1(C_1169,'#skF_2')))
      | ~ v1_funct_2(E_1168,C_1169,'#skF_2')
      | ~ v1_funct_1(E_1168)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1172))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1169,k1_zfmisc_1(A_1172))
      | v1_xboole_0(C_1169)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1172) ) ),
    inference(resolution,[status(thm)],[c_46,c_40024])).

tff(c_40035,plain,(
    ! [A_1172,C_1169,E_1168] :
      ( v1_funct_1(k1_tmap_1(A_1172,'#skF_2',C_1169,'#skF_4',E_1168,'#skF_6'))
      | ~ m1_subset_1(E_1168,k1_zfmisc_1(k2_zfmisc_1(C_1169,'#skF_2')))
      | ~ v1_funct_2(E_1168,C_1169,'#skF_2')
      | ~ v1_funct_1(E_1168)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1172))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1169,k1_zfmisc_1(A_1172))
      | v1_xboole_0(C_1169)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40028])).

tff(c_40412,plain,(
    ! [A_1214,C_1215,E_1216] :
      ( v1_funct_1(k1_tmap_1(A_1214,'#skF_2',C_1215,'#skF_4',E_1216,'#skF_6'))
      | ~ m1_subset_1(E_1216,k1_zfmisc_1(k2_zfmisc_1(C_1215,'#skF_2')))
      | ~ v1_funct_2(E_1216,C_1215,'#skF_2')
      | ~ v1_funct_1(E_1216)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1214))
      | ~ m1_subset_1(C_1215,k1_zfmisc_1(A_1214))
      | v1_xboole_0(C_1215)
      | v1_xboole_0(A_1214) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_40035])).

tff(c_40417,plain,(
    ! [A_1214] :
      ( v1_funct_1(k1_tmap_1(A_1214,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1214))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1214))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1214) ) ),
    inference(resolution,[status(thm)],[c_52,c_40412])).

tff(c_40425,plain,(
    ! [A_1214] :
      ( v1_funct_1(k1_tmap_1(A_1214,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1214))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1214))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40417])).

tff(c_40515,plain,(
    ! [A_1245] :
      ( v1_funct_1(k1_tmap_1(A_1245,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1245))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1245))
      | v1_xboole_0(A_1245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_40425])).

tff(c_40518,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_40515])).

tff(c_40521,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40518])).

tff(c_40522,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_40521])).

tff(c_40,plain,(
    ! [C_158,A_156,D_159,B_157,F_161,E_160] :
      ( v1_funct_2(k1_tmap_1(A_156,B_157,C_158,D_159,E_160,F_161),k4_subset_1(A_156,C_158,D_159),B_157)
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(D_159,B_157)))
      | ~ v1_funct_2(F_161,D_159,B_157)
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(C_158,B_157)))
      | ~ v1_funct_2(E_160,C_158,B_157)
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(A_156))
      | v1_xboole_0(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156))
      | v1_xboole_0(C_158)
      | v1_xboole_0(B_157)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_38,plain,(
    ! [C_158,A_156,D_159,B_157,F_161,E_160] :
      ( m1_subset_1(k1_tmap_1(A_156,B_157,C_158,D_159,E_160,F_161),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_156,C_158,D_159),B_157)))
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(D_159,B_157)))
      | ~ v1_funct_2(F_161,D_159,B_157)
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(C_158,B_157)))
      | ~ v1_funct_2(E_160,C_158,B_157)
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(A_156))
      | v1_xboole_0(D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156))
      | v1_xboole_0(C_158)
      | v1_xboole_0(B_157)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_40405,plain,(
    ! [F_1209,C_1208,D_1210,A_1211,B_1213,E_1212] :
      ( k2_partfun1(k4_subset_1(A_1211,C_1208,D_1210),B_1213,k1_tmap_1(A_1211,B_1213,C_1208,D_1210,E_1212,F_1209),C_1208) = E_1212
      | ~ m1_subset_1(k1_tmap_1(A_1211,B_1213,C_1208,D_1210,E_1212,F_1209),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1211,C_1208,D_1210),B_1213)))
      | ~ v1_funct_2(k1_tmap_1(A_1211,B_1213,C_1208,D_1210,E_1212,F_1209),k4_subset_1(A_1211,C_1208,D_1210),B_1213)
      | ~ v1_funct_1(k1_tmap_1(A_1211,B_1213,C_1208,D_1210,E_1212,F_1209))
      | k2_partfun1(D_1210,B_1213,F_1209,k9_subset_1(A_1211,C_1208,D_1210)) != k2_partfun1(C_1208,B_1213,E_1212,k9_subset_1(A_1211,C_1208,D_1210))
      | ~ m1_subset_1(F_1209,k1_zfmisc_1(k2_zfmisc_1(D_1210,B_1213)))
      | ~ v1_funct_2(F_1209,D_1210,B_1213)
      | ~ v1_funct_1(F_1209)
      | ~ m1_subset_1(E_1212,k1_zfmisc_1(k2_zfmisc_1(C_1208,B_1213)))
      | ~ v1_funct_2(E_1212,C_1208,B_1213)
      | ~ v1_funct_1(E_1212)
      | ~ m1_subset_1(D_1210,k1_zfmisc_1(A_1211))
      | v1_xboole_0(D_1210)
      | ~ m1_subset_1(C_1208,k1_zfmisc_1(A_1211))
      | v1_xboole_0(C_1208)
      | v1_xboole_0(B_1213)
      | v1_xboole_0(A_1211) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_79622,plain,(
    ! [C_1925,A_1928,D_1927,E_1924,F_1923,B_1926] :
      ( k2_partfun1(k4_subset_1(A_1928,C_1925,D_1927),B_1926,k1_tmap_1(A_1928,B_1926,C_1925,D_1927,E_1924,F_1923),C_1925) = E_1924
      | ~ v1_funct_2(k1_tmap_1(A_1928,B_1926,C_1925,D_1927,E_1924,F_1923),k4_subset_1(A_1928,C_1925,D_1927),B_1926)
      | ~ v1_funct_1(k1_tmap_1(A_1928,B_1926,C_1925,D_1927,E_1924,F_1923))
      | k2_partfun1(D_1927,B_1926,F_1923,k9_subset_1(A_1928,C_1925,D_1927)) != k2_partfun1(C_1925,B_1926,E_1924,k9_subset_1(A_1928,C_1925,D_1927))
      | ~ m1_subset_1(F_1923,k1_zfmisc_1(k2_zfmisc_1(D_1927,B_1926)))
      | ~ v1_funct_2(F_1923,D_1927,B_1926)
      | ~ v1_funct_1(F_1923)
      | ~ m1_subset_1(E_1924,k1_zfmisc_1(k2_zfmisc_1(C_1925,B_1926)))
      | ~ v1_funct_2(E_1924,C_1925,B_1926)
      | ~ v1_funct_1(E_1924)
      | ~ m1_subset_1(D_1927,k1_zfmisc_1(A_1928))
      | v1_xboole_0(D_1927)
      | ~ m1_subset_1(C_1925,k1_zfmisc_1(A_1928))
      | v1_xboole_0(C_1925)
      | v1_xboole_0(B_1926)
      | v1_xboole_0(A_1928) ) ),
    inference(resolution,[status(thm)],[c_38,c_40405])).

tff(c_94406,plain,(
    ! [C_2207,D_2209,B_2208,A_2210,E_2206,F_2205] :
      ( k2_partfun1(k4_subset_1(A_2210,C_2207,D_2209),B_2208,k1_tmap_1(A_2210,B_2208,C_2207,D_2209,E_2206,F_2205),C_2207) = E_2206
      | ~ v1_funct_1(k1_tmap_1(A_2210,B_2208,C_2207,D_2209,E_2206,F_2205))
      | k2_partfun1(D_2209,B_2208,F_2205,k9_subset_1(A_2210,C_2207,D_2209)) != k2_partfun1(C_2207,B_2208,E_2206,k9_subset_1(A_2210,C_2207,D_2209))
      | ~ m1_subset_1(F_2205,k1_zfmisc_1(k2_zfmisc_1(D_2209,B_2208)))
      | ~ v1_funct_2(F_2205,D_2209,B_2208)
      | ~ v1_funct_1(F_2205)
      | ~ m1_subset_1(E_2206,k1_zfmisc_1(k2_zfmisc_1(C_2207,B_2208)))
      | ~ v1_funct_2(E_2206,C_2207,B_2208)
      | ~ v1_funct_1(E_2206)
      | ~ m1_subset_1(D_2209,k1_zfmisc_1(A_2210))
      | v1_xboole_0(D_2209)
      | ~ m1_subset_1(C_2207,k1_zfmisc_1(A_2210))
      | v1_xboole_0(C_2207)
      | v1_xboole_0(B_2208)
      | v1_xboole_0(A_2210) ) ),
    inference(resolution,[status(thm)],[c_40,c_79622])).

tff(c_94412,plain,(
    ! [A_2210,C_2207,E_2206] :
      ( k2_partfun1(k4_subset_1(A_2210,C_2207,'#skF_4'),'#skF_2',k1_tmap_1(A_2210,'#skF_2',C_2207,'#skF_4',E_2206,'#skF_6'),C_2207) = E_2206
      | ~ v1_funct_1(k1_tmap_1(A_2210,'#skF_2',C_2207,'#skF_4',E_2206,'#skF_6'))
      | k2_partfun1(C_2207,'#skF_2',E_2206,k9_subset_1(A_2210,C_2207,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_2210,C_2207,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2206,k1_zfmisc_1(k2_zfmisc_1(C_2207,'#skF_2')))
      | ~ v1_funct_2(E_2206,C_2207,'#skF_2')
      | ~ v1_funct_1(E_2206)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2210))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2207,k1_zfmisc_1(A_2210))
      | v1_xboole_0(C_2207)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2210) ) ),
    inference(resolution,[status(thm)],[c_46,c_94406])).

tff(c_94420,plain,(
    ! [A_2210,C_2207,E_2206] :
      ( k2_partfun1(k4_subset_1(A_2210,C_2207,'#skF_4'),'#skF_2',k1_tmap_1(A_2210,'#skF_2',C_2207,'#skF_4',E_2206,'#skF_6'),C_2207) = E_2206
      | ~ v1_funct_1(k1_tmap_1(A_2210,'#skF_2',C_2207,'#skF_4',E_2206,'#skF_6'))
      | k2_partfun1(C_2207,'#skF_2',E_2206,k9_subset_1(A_2210,C_2207,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2210,C_2207,'#skF_4'))
      | ~ m1_subset_1(E_2206,k1_zfmisc_1(k2_zfmisc_1(C_2207,'#skF_2')))
      | ~ v1_funct_2(E_2206,C_2207,'#skF_2')
      | ~ v1_funct_1(E_2206)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2210))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2207,k1_zfmisc_1(A_2210))
      | v1_xboole_0(C_2207)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3671,c_94412])).

tff(c_101055,plain,(
    ! [A_2304,C_2305,E_2306] :
      ( k2_partfun1(k4_subset_1(A_2304,C_2305,'#skF_4'),'#skF_2',k1_tmap_1(A_2304,'#skF_2',C_2305,'#skF_4',E_2306,'#skF_6'),C_2305) = E_2306
      | ~ v1_funct_1(k1_tmap_1(A_2304,'#skF_2',C_2305,'#skF_4',E_2306,'#skF_6'))
      | k2_partfun1(C_2305,'#skF_2',E_2306,k9_subset_1(A_2304,C_2305,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2304,C_2305,'#skF_4'))
      | ~ m1_subset_1(E_2306,k1_zfmisc_1(k2_zfmisc_1(C_2305,'#skF_2')))
      | ~ v1_funct_2(E_2306,C_2305,'#skF_2')
      | ~ v1_funct_1(E_2306)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2304))
      | ~ m1_subset_1(C_2305,k1_zfmisc_1(A_2304))
      | v1_xboole_0(C_2305)
      | v1_xboole_0(A_2304) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_94420])).

tff(c_101060,plain,(
    ! [A_2304] :
      ( k2_partfun1(k4_subset_1(A_2304,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2304,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2304,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2304,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2304,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2304))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2304))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2304) ) ),
    inference(resolution,[status(thm)],[c_52,c_101055])).

tff(c_101068,plain,(
    ! [A_2304] :
      ( k2_partfun1(k4_subset_1(A_2304,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2304,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2304,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2304,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2304,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2304))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2304))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2304) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3668,c_101060])).

tff(c_104682,plain,(
    ! [A_2326] :
      ( k2_partfun1(k4_subset_1(A_2326,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2326,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2326,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2326,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2326,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2326))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2326))
      | v1_xboole_0(A_2326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_101068])).

tff(c_4113,plain,(
    ! [B_492,A_493] :
      ( k3_xboole_0(k1_relat_1(B_492),A_493) = k1_xboole_0
      | k7_relat_1(B_492,A_493) != k1_xboole_0
      | ~ v1_relat_1(B_492) ) ),
    inference(resolution,[status(thm)],[c_3137,c_2])).

tff(c_6015,plain,(
    ! [B_600,A_601] :
      ( k7_relat_1(B_600,k1_xboole_0) = k7_relat_1(B_600,A_601)
      | ~ v1_relat_1(B_600)
      | k7_relat_1(B_600,A_601) != k1_xboole_0
      | ~ v1_relat_1(B_600) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4113,c_10])).

tff(c_6017,plain,(
    ! [A_601] :
      ( k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6',A_601)
      | k7_relat_1('#skF_6',A_601) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_97,c_6015])).

tff(c_6026,plain,(
    ! [A_602] :
      ( k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6',A_602)
      | k7_relat_1('#skF_6',A_602) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_6017])).

tff(c_6048,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3610,c_6026])).

tff(c_6078,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_6048])).

tff(c_6086,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6078,c_3963])).

tff(c_4099,plain,(
    ! [A_489,C_486,D_488,E_485,B_487,F_484] :
      ( v1_funct_1(k1_tmap_1(A_489,B_487,C_486,D_488,E_485,F_484))
      | ~ m1_subset_1(F_484,k1_zfmisc_1(k2_zfmisc_1(D_488,B_487)))
      | ~ v1_funct_2(F_484,D_488,B_487)
      | ~ v1_funct_1(F_484)
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(C_486,B_487)))
      | ~ v1_funct_2(E_485,C_486,B_487)
      | ~ v1_funct_1(E_485)
      | ~ m1_subset_1(D_488,k1_zfmisc_1(A_489))
      | v1_xboole_0(D_488)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_489))
      | v1_xboole_0(C_486)
      | v1_xboole_0(B_487)
      | v1_xboole_0(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4103,plain,(
    ! [A_489,C_486,E_485] :
      ( v1_funct_1(k1_tmap_1(A_489,'#skF_2',C_486,'#skF_4',E_485,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(C_486,'#skF_2')))
      | ~ v1_funct_2(E_485,C_486,'#skF_2')
      | ~ v1_funct_1(E_485)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_489))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_489))
      | v1_xboole_0(C_486)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_489) ) ),
    inference(resolution,[status(thm)],[c_46,c_4099])).

tff(c_4110,plain,(
    ! [A_489,C_486,E_485] :
      ( v1_funct_1(k1_tmap_1(A_489,'#skF_2',C_486,'#skF_4',E_485,'#skF_6'))
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(C_486,'#skF_2')))
      | ~ v1_funct_2(E_485,C_486,'#skF_2')
      | ~ v1_funct_1(E_485)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_489))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_489))
      | v1_xboole_0(C_486)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4103])).

tff(c_4517,plain,(
    ! [A_539,C_540,E_541] :
      ( v1_funct_1(k1_tmap_1(A_539,'#skF_2',C_540,'#skF_4',E_541,'#skF_6'))
      | ~ m1_subset_1(E_541,k1_zfmisc_1(k2_zfmisc_1(C_540,'#skF_2')))
      | ~ v1_funct_2(E_541,C_540,'#skF_2')
      | ~ v1_funct_1(E_541)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_539))
      | ~ m1_subset_1(C_540,k1_zfmisc_1(A_539))
      | v1_xboole_0(C_540)
      | v1_xboole_0(A_539) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_4110])).

tff(c_4522,plain,(
    ! [A_539] :
      ( v1_funct_1(k1_tmap_1(A_539,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_539))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_539))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_539) ) ),
    inference(resolution,[status(thm)],[c_52,c_4517])).

tff(c_4530,plain,(
    ! [A_539] :
      ( v1_funct_1(k1_tmap_1(A_539,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_539))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_539))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4522])).

tff(c_4712,plain,(
    ! [A_572] :
      ( v1_funct_1(k1_tmap_1(A_572,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_572))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_572))
      | v1_xboole_0(A_572) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4530])).

tff(c_4715,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_4712])).

tff(c_4718,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4715])).

tff(c_4719,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4718])).

tff(c_4634,plain,(
    ! [B_549,C_544,E_548,A_547,D_546,F_545] :
      ( k2_partfun1(k4_subset_1(A_547,C_544,D_546),B_549,k1_tmap_1(A_547,B_549,C_544,D_546,E_548,F_545),D_546) = F_545
      | ~ m1_subset_1(k1_tmap_1(A_547,B_549,C_544,D_546,E_548,F_545),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_547,C_544,D_546),B_549)))
      | ~ v1_funct_2(k1_tmap_1(A_547,B_549,C_544,D_546,E_548,F_545),k4_subset_1(A_547,C_544,D_546),B_549)
      | ~ v1_funct_1(k1_tmap_1(A_547,B_549,C_544,D_546,E_548,F_545))
      | k2_partfun1(D_546,B_549,F_545,k9_subset_1(A_547,C_544,D_546)) != k2_partfun1(C_544,B_549,E_548,k9_subset_1(A_547,C_544,D_546))
      | ~ m1_subset_1(F_545,k1_zfmisc_1(k2_zfmisc_1(D_546,B_549)))
      | ~ v1_funct_2(F_545,D_546,B_549)
      | ~ v1_funct_1(F_545)
      | ~ m1_subset_1(E_548,k1_zfmisc_1(k2_zfmisc_1(C_544,B_549)))
      | ~ v1_funct_2(E_548,C_544,B_549)
      | ~ v1_funct_1(E_548)
      | ~ m1_subset_1(D_546,k1_zfmisc_1(A_547))
      | v1_xboole_0(D_546)
      | ~ m1_subset_1(C_544,k1_zfmisc_1(A_547))
      | v1_xboole_0(C_544)
      | v1_xboole_0(B_549)
      | v1_xboole_0(A_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_9041,plain,(
    ! [D_697,C_695,B_696,E_694,A_698,F_693] :
      ( k2_partfun1(k4_subset_1(A_698,C_695,D_697),B_696,k1_tmap_1(A_698,B_696,C_695,D_697,E_694,F_693),D_697) = F_693
      | ~ v1_funct_2(k1_tmap_1(A_698,B_696,C_695,D_697,E_694,F_693),k4_subset_1(A_698,C_695,D_697),B_696)
      | ~ v1_funct_1(k1_tmap_1(A_698,B_696,C_695,D_697,E_694,F_693))
      | k2_partfun1(D_697,B_696,F_693,k9_subset_1(A_698,C_695,D_697)) != k2_partfun1(C_695,B_696,E_694,k9_subset_1(A_698,C_695,D_697))
      | ~ m1_subset_1(F_693,k1_zfmisc_1(k2_zfmisc_1(D_697,B_696)))
      | ~ v1_funct_2(F_693,D_697,B_696)
      | ~ v1_funct_1(F_693)
      | ~ m1_subset_1(E_694,k1_zfmisc_1(k2_zfmisc_1(C_695,B_696)))
      | ~ v1_funct_2(E_694,C_695,B_696)
      | ~ v1_funct_1(E_694)
      | ~ m1_subset_1(D_697,k1_zfmisc_1(A_698))
      | v1_xboole_0(D_697)
      | ~ m1_subset_1(C_695,k1_zfmisc_1(A_698))
      | v1_xboole_0(C_695)
      | v1_xboole_0(B_696)
      | v1_xboole_0(A_698) ) ),
    inference(resolution,[status(thm)],[c_38,c_4634])).

tff(c_24392,plain,(
    ! [C_982,F_980,E_981,D_984,B_983,A_985] :
      ( k2_partfun1(k4_subset_1(A_985,C_982,D_984),B_983,k1_tmap_1(A_985,B_983,C_982,D_984,E_981,F_980),D_984) = F_980
      | ~ v1_funct_1(k1_tmap_1(A_985,B_983,C_982,D_984,E_981,F_980))
      | k2_partfun1(D_984,B_983,F_980,k9_subset_1(A_985,C_982,D_984)) != k2_partfun1(C_982,B_983,E_981,k9_subset_1(A_985,C_982,D_984))
      | ~ m1_subset_1(F_980,k1_zfmisc_1(k2_zfmisc_1(D_984,B_983)))
      | ~ v1_funct_2(F_980,D_984,B_983)
      | ~ v1_funct_1(F_980)
      | ~ m1_subset_1(E_981,k1_zfmisc_1(k2_zfmisc_1(C_982,B_983)))
      | ~ v1_funct_2(E_981,C_982,B_983)
      | ~ v1_funct_1(E_981)
      | ~ m1_subset_1(D_984,k1_zfmisc_1(A_985))
      | v1_xboole_0(D_984)
      | ~ m1_subset_1(C_982,k1_zfmisc_1(A_985))
      | v1_xboole_0(C_982)
      | v1_xboole_0(B_983)
      | v1_xboole_0(A_985) ) ),
    inference(resolution,[status(thm)],[c_40,c_9041])).

tff(c_24398,plain,(
    ! [A_985,C_982,E_981] :
      ( k2_partfun1(k4_subset_1(A_985,C_982,'#skF_4'),'#skF_2',k1_tmap_1(A_985,'#skF_2',C_982,'#skF_4',E_981,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_985,'#skF_2',C_982,'#skF_4',E_981,'#skF_6'))
      | k2_partfun1(C_982,'#skF_2',E_981,k9_subset_1(A_985,C_982,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_985,C_982,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_981,k1_zfmisc_1(k2_zfmisc_1(C_982,'#skF_2')))
      | ~ v1_funct_2(E_981,C_982,'#skF_2')
      | ~ v1_funct_1(E_981)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_985))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_982,k1_zfmisc_1(A_985))
      | v1_xboole_0(C_982)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_985) ) ),
    inference(resolution,[status(thm)],[c_46,c_24392])).

tff(c_24406,plain,(
    ! [A_985,C_982,E_981] :
      ( k2_partfun1(k4_subset_1(A_985,C_982,'#skF_4'),'#skF_2',k1_tmap_1(A_985,'#skF_2',C_982,'#skF_4',E_981,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_985,'#skF_2',C_982,'#skF_4',E_981,'#skF_6'))
      | k2_partfun1(C_982,'#skF_2',E_981,k9_subset_1(A_985,C_982,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_985,C_982,'#skF_4'))
      | ~ m1_subset_1(E_981,k1_zfmisc_1(k2_zfmisc_1(C_982,'#skF_2')))
      | ~ v1_funct_2(E_981,C_982,'#skF_2')
      | ~ v1_funct_1(E_981)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_985))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_982,k1_zfmisc_1(A_985))
      | v1_xboole_0(C_982)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_985) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_3671,c_24398])).

tff(c_38715,plain,(
    ! [A_1139,C_1140,E_1141] :
      ( k2_partfun1(k4_subset_1(A_1139,C_1140,'#skF_4'),'#skF_2',k1_tmap_1(A_1139,'#skF_2',C_1140,'#skF_4',E_1141,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1139,'#skF_2',C_1140,'#skF_4',E_1141,'#skF_6'))
      | k2_partfun1(C_1140,'#skF_2',E_1141,k9_subset_1(A_1139,C_1140,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1139,C_1140,'#skF_4'))
      | ~ m1_subset_1(E_1141,k1_zfmisc_1(k2_zfmisc_1(C_1140,'#skF_2')))
      | ~ v1_funct_2(E_1141,C_1140,'#skF_2')
      | ~ v1_funct_1(E_1141)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1139))
      | ~ m1_subset_1(C_1140,k1_zfmisc_1(A_1139))
      | v1_xboole_0(C_1140)
      | v1_xboole_0(A_1139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_24406])).

tff(c_38720,plain,(
    ! [A_1139] :
      ( k2_partfun1(k4_subset_1(A_1139,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1139,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1139,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1139,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1139,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1139))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1139))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1139) ) ),
    inference(resolution,[status(thm)],[c_52,c_38715])).

tff(c_38728,plain,(
    ! [A_1139] :
      ( k2_partfun1(k4_subset_1(A_1139,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1139,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1139,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1139,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1139,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1139))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1139))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3668,c_38720])).

tff(c_39765,plain,(
    ! [A_1153] :
      ( k2_partfun1(k4_subset_1(A_1153,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1153,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1153,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1153,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1153,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1153))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1153))
      | v1_xboole_0(A_1153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_38728])).

tff(c_3095,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4001,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3095])).

tff(c_39776,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39765,c_4001])).

tff(c_39790,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_6086,c_6078,c_3962,c_3962,c_3528,c_3528,c_4719,c_39776])).

tff(c_39792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_39790])).

tff(c_39793,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3095])).

tff(c_104694,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_104682,c_39793])).

tff(c_104708,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_41846,c_3962,c_3528,c_41854,c_3962,c_3528,c_40522,c_104694])).

tff(c_104710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_104708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.53/16.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.66/16.43  
% 25.66/16.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.66/16.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 25.66/16.43  
% 25.66/16.43  %Foreground sorts:
% 25.66/16.43  
% 25.66/16.43  
% 25.66/16.43  %Background operators:
% 25.66/16.43  
% 25.66/16.43  
% 25.66/16.43  %Foreground operators:
% 25.66/16.43  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 25.66/16.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 25.66/16.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.66/16.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 25.66/16.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.66/16.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 25.66/16.43  tff('#skF_5', type, '#skF_5': $i).
% 25.66/16.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 25.66/16.43  tff('#skF_6', type, '#skF_6': $i).
% 25.66/16.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 25.66/16.43  tff('#skF_2', type, '#skF_2': $i).
% 25.66/16.43  tff('#skF_3', type, '#skF_3': $i).
% 25.66/16.43  tff('#skF_1', type, '#skF_1': $i).
% 25.66/16.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 25.66/16.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.66/16.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.66/16.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.66/16.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.66/16.43  tff('#skF_4', type, '#skF_4': $i).
% 25.66/16.43  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 25.66/16.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.66/16.43  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 25.66/16.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 25.66/16.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.66/16.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.66/16.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.66/16.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 25.66/16.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.66/16.43  
% 25.66/16.46  tff(f_209, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 25.66/16.46  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 25.66/16.46  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 25.66/16.46  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 25.66/16.46  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 25.66/16.46  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 25.66/16.46  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 25.66/16.46  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 25.66/16.46  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 25.66/16.46  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 25.66/16.46  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 25.66/16.46  tff(f_85, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 25.66/16.46  tff(f_167, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 25.66/16.46  tff(f_133, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 25.66/16.46  tff(c_70, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.46  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.46  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.46  tff(c_66, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.46  tff(c_58, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.46  tff(c_62, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.46  tff(c_3173, plain, (![A_433, B_434]: (r1_xboole_0(A_433, B_434) | ~r1_subset_1(A_433, B_434) | v1_xboole_0(B_434) | v1_xboole_0(A_433))), inference(cnfTransformation, [status(thm)], [f_69])).
% 25.66/16.46  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.66/16.46  tff(c_3566, plain, (![B_459, A_460]: (r1_xboole_0(B_459, A_460) | ~r1_subset_1(A_460, B_459) | v1_xboole_0(B_459) | v1_xboole_0(A_460))), inference(resolution, [status(thm)], [c_3173, c_6])).
% 25.66/16.46  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.46  tff(c_89, plain, (![C_227, A_228, B_229]: (v1_relat_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 25.66/16.46  tff(c_97, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_89])).
% 25.66/16.46  tff(c_3098, plain, (![C_419, A_420, B_421]: (v4_relat_1(C_419, A_420) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 25.66/16.46  tff(c_3106, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_3098])).
% 25.66/16.46  tff(c_3107, plain, (![B_422, A_423]: (k7_relat_1(B_422, A_423)=B_422 | ~v4_relat_1(B_422, A_423) | ~v1_relat_1(B_422))), inference(cnfTransformation, [status(thm)], [f_53])).
% 25.66/16.46  tff(c_3110, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3106, c_3107])).
% 25.66/16.46  tff(c_3116, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_3110])).
% 25.66/16.46  tff(c_3190, plain, (![C_435, A_436, B_437]: (k7_relat_1(k7_relat_1(C_435, A_436), B_437)=k1_xboole_0 | ~r1_xboole_0(A_436, B_437) | ~v1_relat_1(C_435))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.66/16.46  tff(c_3208, plain, (![B_437]: (k7_relat_1('#skF_6', B_437)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_437) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3116, c_3190])).
% 25.66/16.46  tff(c_3214, plain, (![B_437]: (k7_relat_1('#skF_6', B_437)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_437))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_3208])).
% 25.66/16.46  tff(c_3574, plain, (![A_460]: (k7_relat_1('#skF_6', A_460)=k1_xboole_0 | ~r1_subset_1(A_460, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_460))), inference(resolution, [status(thm)], [c_3566, c_3214])).
% 25.66/16.46  tff(c_3604, plain, (![A_461]: (k7_relat_1('#skF_6', A_461)=k1_xboole_0 | ~r1_subset_1(A_461, '#skF_4') | v1_xboole_0(A_461))), inference(negUnitSimplification, [status(thm)], [c_62, c_3574])).
% 25.66/16.46  tff(c_3607, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3604])).
% 25.66/16.46  tff(c_3610, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_3607])).
% 25.66/16.46  tff(c_3137, plain, (![B_427, A_428]: (r1_xboole_0(k1_relat_1(B_427), A_428) | k7_relat_1(B_427, A_428)!=k1_xboole_0 | ~v1_relat_1(B_427))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.66/16.46  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.66/16.47  tff(c_39897, plain, (![B_1159, A_1160]: (k3_xboole_0(k1_relat_1(B_1159), A_1160)=k1_xboole_0 | k7_relat_1(B_1159, A_1160)!=k1_xboole_0 | ~v1_relat_1(B_1159))), inference(resolution, [status(thm)], [c_3137, c_2])).
% 25.66/16.47  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, k3_xboole_0(k1_relat_1(B_9), A_8))=k7_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.66/16.47  tff(c_41783, plain, (![B_1270, A_1271]: (k7_relat_1(B_1270, k1_xboole_0)=k7_relat_1(B_1270, A_1271) | ~v1_relat_1(B_1270) | k7_relat_1(B_1270, A_1271)!=k1_xboole_0 | ~v1_relat_1(B_1270))), inference(superposition, [status(thm), theory('equality')], [c_39897, c_10])).
% 25.66/16.47  tff(c_41785, plain, (![A_1271]: (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', A_1271) | k7_relat_1('#skF_6', A_1271)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_97, c_41783])).
% 25.66/16.47  tff(c_41794, plain, (![A_1272]: (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', A_1272) | k7_relat_1('#skF_6', A_1272)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_41785])).
% 25.66/16.47  tff(c_41816, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3610, c_41794])).
% 25.66/16.47  tff(c_41846, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3610, c_41816])).
% 25.66/16.47  tff(c_3950, plain, (![A_479, B_480]: (k3_xboole_0(A_479, B_480)=k1_xboole_0 | ~r1_subset_1(A_479, B_480) | v1_xboole_0(B_480) | v1_xboole_0(A_479))), inference(resolution, [status(thm)], [c_3173, c_2])).
% 25.66/16.47  tff(c_3956, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3950])).
% 25.66/16.47  tff(c_3962, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_3956])).
% 25.66/16.47  tff(c_3516, plain, (![A_451, B_452, C_453]: (k9_subset_1(A_451, B_452, C_453)=k3_xboole_0(B_452, C_453) | ~m1_subset_1(C_453, k1_zfmisc_1(A_451)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.66/16.47  tff(c_3528, plain, (![B_452]: (k9_subset_1('#skF_1', B_452, '#skF_4')=k3_xboole_0(B_452, '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_3516])).
% 25.66/16.47  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.47  tff(c_3661, plain, (![A_463, B_464, C_465, D_466]: (k2_partfun1(A_463, B_464, C_465, D_466)=k7_relat_1(C_465, D_466) | ~m1_subset_1(C_465, k1_zfmisc_1(k2_zfmisc_1(A_463, B_464))) | ~v1_funct_1(C_465))), inference(cnfTransformation, [status(thm)], [f_85])).
% 25.66/16.47  tff(c_3665, plain, (![D_466]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_466)=k7_relat_1('#skF_6', D_466) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_3661])).
% 25.66/16.47  tff(c_3671, plain, (![D_466]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_466)=k7_relat_1('#skF_6', D_466))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3665])).
% 25.66/16.47  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.47  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.47  tff(c_3663, plain, (![D_466]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_466)=k7_relat_1('#skF_5', D_466) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_3661])).
% 25.66/16.47  tff(c_3668, plain, (![D_466]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_466)=k7_relat_1('#skF_5', D_466))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3663])).
% 25.66/16.47  tff(c_148, plain, (![A_242, B_243]: (r1_xboole_0(A_242, B_243) | ~r1_subset_1(A_242, B_243) | v1_xboole_0(B_243) | v1_xboole_0(A_242))), inference(cnfTransformation, [status(thm)], [f_69])).
% 25.66/16.47  tff(c_209, plain, (![B_250, A_251]: (r1_xboole_0(B_250, A_251) | ~r1_subset_1(A_251, B_250) | v1_xboole_0(B_250) | v1_xboole_0(A_251))), inference(resolution, [status(thm)], [c_148, c_6])).
% 25.66/16.47  tff(c_20, plain, (![A_17, B_18]: (r1_subset_1(A_17, B_18) | ~r1_xboole_0(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 25.66/16.47  tff(c_226, plain, (![B_252, A_253]: (r1_subset_1(B_252, A_253) | ~r1_subset_1(A_253, B_252) | v1_xboole_0(B_252) | v1_xboole_0(A_253))), inference(resolution, [status(thm)], [c_209, c_20])).
% 25.66/16.47  tff(c_228, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_226])).
% 25.66/16.47  tff(c_231, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_228])).
% 25.66/16.47  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | ~r1_subset_1(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 25.66/16.47  tff(c_100, plain, (![C_232, A_233, B_234]: (v4_relat_1(C_232, A_233) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 25.66/16.47  tff(c_108, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_100])).
% 25.66/16.47  tff(c_118, plain, (![B_238, A_239]: (k7_relat_1(B_238, A_239)=B_238 | ~v4_relat_1(B_238, A_239) | ~v1_relat_1(B_238))), inference(cnfTransformation, [status(thm)], [f_53])).
% 25.66/16.47  tff(c_121, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_108, c_118])).
% 25.66/16.47  tff(c_127, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_121])).
% 25.66/16.47  tff(c_287, plain, (![C_261, A_262, B_263]: (k7_relat_1(k7_relat_1(C_261, A_262), B_263)=k1_xboole_0 | ~r1_xboole_0(A_262, B_263) | ~v1_relat_1(C_261))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.66/16.47  tff(c_305, plain, (![B_263]: (k7_relat_1('#skF_6', B_263)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_263) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_287])).
% 25.66/16.47  tff(c_342, plain, (![B_265]: (k7_relat_1('#skF_6', B_265)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_265))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_305])).
% 25.66/16.47  tff(c_354, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_342])).
% 25.66/16.47  tff(c_392, plain, (![B_267]: (k7_relat_1('#skF_6', B_267)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_267) | v1_xboole_0(B_267))), inference(negUnitSimplification, [status(thm)], [c_62, c_354])).
% 25.66/16.47  tff(c_395, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_231, c_392])).
% 25.66/16.47  tff(c_398, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_395])).
% 25.66/16.47  tff(c_160, plain, (![B_244, A_245]: (r1_xboole_0(k1_relat_1(B_244), A_245) | k7_relat_1(B_244, A_245)!=k1_xboole_0 | ~v1_relat_1(B_244))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.66/16.47  tff(c_1030, plain, (![B_308, A_309]: (k3_xboole_0(k1_relat_1(B_308), A_309)=k1_xboole_0 | k7_relat_1(B_308, A_309)!=k1_xboole_0 | ~v1_relat_1(B_308))), inference(resolution, [status(thm)], [c_160, c_2])).
% 25.66/16.47  tff(c_2837, plain, (![B_409, A_410]: (k7_relat_1(B_409, k1_xboole_0)=k7_relat_1(B_409, A_410) | ~v1_relat_1(B_409) | k7_relat_1(B_409, A_410)!=k1_xboole_0 | ~v1_relat_1(B_409))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_10])).
% 25.66/16.47  tff(c_2839, plain, (![A_410]: (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', A_410) | k7_relat_1('#skF_6', A_410)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_97, c_2837])).
% 25.66/16.47  tff(c_2848, plain, (![A_411]: (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', A_411) | k7_relat_1('#skF_6', A_411)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_2839])).
% 25.66/16.47  tff(c_2877, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_398, c_2848])).
% 25.66/16.47  tff(c_2904, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_398, c_2877])).
% 25.66/16.47  tff(c_944, plain, (![A_298, B_299]: (k3_xboole_0(A_298, B_299)=k1_xboole_0 | ~r1_subset_1(A_298, B_299) | v1_xboole_0(B_299) | v1_xboole_0(A_298))), inference(resolution, [status(thm)], [c_148, c_2])).
% 25.66/16.47  tff(c_950, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_944])).
% 25.66/16.47  tff(c_956, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_950])).
% 25.66/16.47  tff(c_662, plain, (![A_276, B_277, C_278, D_279]: (k2_partfun1(A_276, B_277, C_278, D_279)=k7_relat_1(C_278, D_279) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~v1_funct_1(C_278))), inference(cnfTransformation, [status(thm)], [f_85])).
% 25.66/16.47  tff(c_666, plain, (![D_279]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_279)=k7_relat_1('#skF_6', D_279) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_662])).
% 25.66/16.47  tff(c_672, plain, (![D_279]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_279)=k7_relat_1('#skF_6', D_279))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_666])).
% 25.66/16.47  tff(c_664, plain, (![D_279]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_279)=k7_relat_1('#skF_5', D_279) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_662])).
% 25.66/16.47  tff(c_669, plain, (![D_279]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_279)=k7_relat_1('#skF_5', D_279))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_664])).
% 25.66/16.47  tff(c_237, plain, (![A_254, B_255, C_256]: (k9_subset_1(A_254, B_255, C_256)=k3_xboole_0(B_255, C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(A_254)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.66/16.47  tff(c_249, plain, (![B_255]: (k9_subset_1('#skF_1', B_255, '#skF_4')=k3_xboole_0(B_255, '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_237])).
% 25.66/16.47  tff(c_44, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.47  tff(c_98, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 25.66/16.47  tff(c_259, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_249, c_98])).
% 25.66/16.47  tff(c_1624, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_956, c_956, c_672, c_669, c_259])).
% 25.66/16.47  tff(c_2907, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2904, c_1624])).
% 25.66/16.47  tff(c_159, plain, (![B_243, A_242]: (r1_xboole_0(B_243, A_242) | ~r1_subset_1(A_242, B_243) | v1_xboole_0(B_243) | v1_xboole_0(A_242))), inference(resolution, [status(thm)], [c_148, c_6])).
% 25.66/16.47  tff(c_96, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_89])).
% 25.66/16.47  tff(c_107, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_100])).
% 25.66/16.47  tff(c_124, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_107, c_118])).
% 25.66/16.47  tff(c_130, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_124])).
% 25.66/16.47  tff(c_302, plain, (![B_263]: (k7_relat_1('#skF_5', B_263)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_263) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_287])).
% 25.66/16.47  tff(c_312, plain, (![B_264]: (k7_relat_1('#skF_5', B_264)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_264))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_302])).
% 25.66/16.47  tff(c_316, plain, (![A_242]: (k7_relat_1('#skF_5', A_242)=k1_xboole_0 | ~r1_subset_1(A_242, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_242))), inference(resolution, [status(thm)], [c_159, c_312])).
% 25.66/16.47  tff(c_552, plain, (![A_273]: (k7_relat_1('#skF_5', A_273)=k1_xboole_0 | ~r1_subset_1(A_273, '#skF_3') | v1_xboole_0(A_273))), inference(negUnitSimplification, [status(thm)], [c_66, c_316])).
% 25.66/16.47  tff(c_555, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_231, c_552])).
% 25.66/16.47  tff(c_558, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_555])).
% 25.66/16.47  tff(c_2841, plain, (![A_410]: (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_5', A_410) | k7_relat_1('#skF_5', A_410)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_96, c_2837])).
% 25.66/16.47  tff(c_3040, plain, (![A_416]: (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_5', A_416) | k7_relat_1('#skF_5', A_416)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2841])).
% 25.66/16.47  tff(c_3062, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_558, c_3040])).
% 25.66/16.47  tff(c_3092, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_558, c_3062])).
% 25.66/16.47  tff(c_3094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2907, c_3092])).
% 25.66/16.47  tff(c_3096, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 25.66/16.47  tff(c_3821, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3671, c_3668, c_3528, c_3528, c_3096])).
% 25.66/16.47  tff(c_3963, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3962, c_3962, c_3821])).
% 25.66/16.47  tff(c_41854, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_41846, c_3963])).
% 25.66/16.47  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.47  tff(c_68, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.47  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 25.66/16.47  tff(c_40024, plain, (![D_1171, F_1167, E_1168, C_1169, A_1172, B_1170]: (v1_funct_1(k1_tmap_1(A_1172, B_1170, C_1169, D_1171, E_1168, F_1167)) | ~m1_subset_1(F_1167, k1_zfmisc_1(k2_zfmisc_1(D_1171, B_1170))) | ~v1_funct_2(F_1167, D_1171, B_1170) | ~v1_funct_1(F_1167) | ~m1_subset_1(E_1168, k1_zfmisc_1(k2_zfmisc_1(C_1169, B_1170))) | ~v1_funct_2(E_1168, C_1169, B_1170) | ~v1_funct_1(E_1168) | ~m1_subset_1(D_1171, k1_zfmisc_1(A_1172)) | v1_xboole_0(D_1171) | ~m1_subset_1(C_1169, k1_zfmisc_1(A_1172)) | v1_xboole_0(C_1169) | v1_xboole_0(B_1170) | v1_xboole_0(A_1172))), inference(cnfTransformation, [status(thm)], [f_167])).
% 25.66/16.47  tff(c_40028, plain, (![A_1172, C_1169, E_1168]: (v1_funct_1(k1_tmap_1(A_1172, '#skF_2', C_1169, '#skF_4', E_1168, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1168, k1_zfmisc_1(k2_zfmisc_1(C_1169, '#skF_2'))) | ~v1_funct_2(E_1168, C_1169, '#skF_2') | ~v1_funct_1(E_1168) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1172)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1169, k1_zfmisc_1(A_1172)) | v1_xboole_0(C_1169) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1172))), inference(resolution, [status(thm)], [c_46, c_40024])).
% 25.66/16.47  tff(c_40035, plain, (![A_1172, C_1169, E_1168]: (v1_funct_1(k1_tmap_1(A_1172, '#skF_2', C_1169, '#skF_4', E_1168, '#skF_6')) | ~m1_subset_1(E_1168, k1_zfmisc_1(k2_zfmisc_1(C_1169, '#skF_2'))) | ~v1_funct_2(E_1168, C_1169, '#skF_2') | ~v1_funct_1(E_1168) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1172)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1169, k1_zfmisc_1(A_1172)) | v1_xboole_0(C_1169) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1172))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40028])).
% 25.66/16.47  tff(c_40412, plain, (![A_1214, C_1215, E_1216]: (v1_funct_1(k1_tmap_1(A_1214, '#skF_2', C_1215, '#skF_4', E_1216, '#skF_6')) | ~m1_subset_1(E_1216, k1_zfmisc_1(k2_zfmisc_1(C_1215, '#skF_2'))) | ~v1_funct_2(E_1216, C_1215, '#skF_2') | ~v1_funct_1(E_1216) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1214)) | ~m1_subset_1(C_1215, k1_zfmisc_1(A_1214)) | v1_xboole_0(C_1215) | v1_xboole_0(A_1214))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_40035])).
% 25.66/16.47  tff(c_40417, plain, (![A_1214]: (v1_funct_1(k1_tmap_1(A_1214, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1214)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1214)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1214))), inference(resolution, [status(thm)], [c_52, c_40412])).
% 25.66/16.47  tff(c_40425, plain, (![A_1214]: (v1_funct_1(k1_tmap_1(A_1214, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1214)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1214)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1214))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40417])).
% 25.66/16.47  tff(c_40515, plain, (![A_1245]: (v1_funct_1(k1_tmap_1(A_1245, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1245)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1245)) | v1_xboole_0(A_1245))), inference(negUnitSimplification, [status(thm)], [c_66, c_40425])).
% 25.66/16.47  tff(c_40518, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_40515])).
% 25.66/16.47  tff(c_40521, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40518])).
% 25.66/16.47  tff(c_40522, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_40521])).
% 25.66/16.47  tff(c_40, plain, (![C_158, A_156, D_159, B_157, F_161, E_160]: (v1_funct_2(k1_tmap_1(A_156, B_157, C_158, D_159, E_160, F_161), k4_subset_1(A_156, C_158, D_159), B_157) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(D_159, B_157))) | ~v1_funct_2(F_161, D_159, B_157) | ~v1_funct_1(F_161) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(C_158, B_157))) | ~v1_funct_2(E_160, C_158, B_157) | ~v1_funct_1(E_160) | ~m1_subset_1(D_159, k1_zfmisc_1(A_156)) | v1_xboole_0(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)) | v1_xboole_0(C_158) | v1_xboole_0(B_157) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_167])).
% 25.66/16.47  tff(c_38, plain, (![C_158, A_156, D_159, B_157, F_161, E_160]: (m1_subset_1(k1_tmap_1(A_156, B_157, C_158, D_159, E_160, F_161), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_156, C_158, D_159), B_157))) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(D_159, B_157))) | ~v1_funct_2(F_161, D_159, B_157) | ~v1_funct_1(F_161) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(C_158, B_157))) | ~v1_funct_2(E_160, C_158, B_157) | ~v1_funct_1(E_160) | ~m1_subset_1(D_159, k1_zfmisc_1(A_156)) | v1_xboole_0(D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)) | v1_xboole_0(C_158) | v1_xboole_0(B_157) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_167])).
% 25.66/16.47  tff(c_40405, plain, (![F_1209, C_1208, D_1210, A_1211, B_1213, E_1212]: (k2_partfun1(k4_subset_1(A_1211, C_1208, D_1210), B_1213, k1_tmap_1(A_1211, B_1213, C_1208, D_1210, E_1212, F_1209), C_1208)=E_1212 | ~m1_subset_1(k1_tmap_1(A_1211, B_1213, C_1208, D_1210, E_1212, F_1209), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1211, C_1208, D_1210), B_1213))) | ~v1_funct_2(k1_tmap_1(A_1211, B_1213, C_1208, D_1210, E_1212, F_1209), k4_subset_1(A_1211, C_1208, D_1210), B_1213) | ~v1_funct_1(k1_tmap_1(A_1211, B_1213, C_1208, D_1210, E_1212, F_1209)) | k2_partfun1(D_1210, B_1213, F_1209, k9_subset_1(A_1211, C_1208, D_1210))!=k2_partfun1(C_1208, B_1213, E_1212, k9_subset_1(A_1211, C_1208, D_1210)) | ~m1_subset_1(F_1209, k1_zfmisc_1(k2_zfmisc_1(D_1210, B_1213))) | ~v1_funct_2(F_1209, D_1210, B_1213) | ~v1_funct_1(F_1209) | ~m1_subset_1(E_1212, k1_zfmisc_1(k2_zfmisc_1(C_1208, B_1213))) | ~v1_funct_2(E_1212, C_1208, B_1213) | ~v1_funct_1(E_1212) | ~m1_subset_1(D_1210, k1_zfmisc_1(A_1211)) | v1_xboole_0(D_1210) | ~m1_subset_1(C_1208, k1_zfmisc_1(A_1211)) | v1_xboole_0(C_1208) | v1_xboole_0(B_1213) | v1_xboole_0(A_1211))), inference(cnfTransformation, [status(thm)], [f_133])).
% 25.66/16.47  tff(c_79622, plain, (![C_1925, A_1928, D_1927, E_1924, F_1923, B_1926]: (k2_partfun1(k4_subset_1(A_1928, C_1925, D_1927), B_1926, k1_tmap_1(A_1928, B_1926, C_1925, D_1927, E_1924, F_1923), C_1925)=E_1924 | ~v1_funct_2(k1_tmap_1(A_1928, B_1926, C_1925, D_1927, E_1924, F_1923), k4_subset_1(A_1928, C_1925, D_1927), B_1926) | ~v1_funct_1(k1_tmap_1(A_1928, B_1926, C_1925, D_1927, E_1924, F_1923)) | k2_partfun1(D_1927, B_1926, F_1923, k9_subset_1(A_1928, C_1925, D_1927))!=k2_partfun1(C_1925, B_1926, E_1924, k9_subset_1(A_1928, C_1925, D_1927)) | ~m1_subset_1(F_1923, k1_zfmisc_1(k2_zfmisc_1(D_1927, B_1926))) | ~v1_funct_2(F_1923, D_1927, B_1926) | ~v1_funct_1(F_1923) | ~m1_subset_1(E_1924, k1_zfmisc_1(k2_zfmisc_1(C_1925, B_1926))) | ~v1_funct_2(E_1924, C_1925, B_1926) | ~v1_funct_1(E_1924) | ~m1_subset_1(D_1927, k1_zfmisc_1(A_1928)) | v1_xboole_0(D_1927) | ~m1_subset_1(C_1925, k1_zfmisc_1(A_1928)) | v1_xboole_0(C_1925) | v1_xboole_0(B_1926) | v1_xboole_0(A_1928))), inference(resolution, [status(thm)], [c_38, c_40405])).
% 25.66/16.47  tff(c_94406, plain, (![C_2207, D_2209, B_2208, A_2210, E_2206, F_2205]: (k2_partfun1(k4_subset_1(A_2210, C_2207, D_2209), B_2208, k1_tmap_1(A_2210, B_2208, C_2207, D_2209, E_2206, F_2205), C_2207)=E_2206 | ~v1_funct_1(k1_tmap_1(A_2210, B_2208, C_2207, D_2209, E_2206, F_2205)) | k2_partfun1(D_2209, B_2208, F_2205, k9_subset_1(A_2210, C_2207, D_2209))!=k2_partfun1(C_2207, B_2208, E_2206, k9_subset_1(A_2210, C_2207, D_2209)) | ~m1_subset_1(F_2205, k1_zfmisc_1(k2_zfmisc_1(D_2209, B_2208))) | ~v1_funct_2(F_2205, D_2209, B_2208) | ~v1_funct_1(F_2205) | ~m1_subset_1(E_2206, k1_zfmisc_1(k2_zfmisc_1(C_2207, B_2208))) | ~v1_funct_2(E_2206, C_2207, B_2208) | ~v1_funct_1(E_2206) | ~m1_subset_1(D_2209, k1_zfmisc_1(A_2210)) | v1_xboole_0(D_2209) | ~m1_subset_1(C_2207, k1_zfmisc_1(A_2210)) | v1_xboole_0(C_2207) | v1_xboole_0(B_2208) | v1_xboole_0(A_2210))), inference(resolution, [status(thm)], [c_40, c_79622])).
% 25.66/16.47  tff(c_94412, plain, (![A_2210, C_2207, E_2206]: (k2_partfun1(k4_subset_1(A_2210, C_2207, '#skF_4'), '#skF_2', k1_tmap_1(A_2210, '#skF_2', C_2207, '#skF_4', E_2206, '#skF_6'), C_2207)=E_2206 | ~v1_funct_1(k1_tmap_1(A_2210, '#skF_2', C_2207, '#skF_4', E_2206, '#skF_6')) | k2_partfun1(C_2207, '#skF_2', E_2206, k9_subset_1(A_2210, C_2207, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_2210, C_2207, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2206, k1_zfmisc_1(k2_zfmisc_1(C_2207, '#skF_2'))) | ~v1_funct_2(E_2206, C_2207, '#skF_2') | ~v1_funct_1(E_2206) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2210)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2207, k1_zfmisc_1(A_2210)) | v1_xboole_0(C_2207) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2210))), inference(resolution, [status(thm)], [c_46, c_94406])).
% 25.66/16.47  tff(c_94420, plain, (![A_2210, C_2207, E_2206]: (k2_partfun1(k4_subset_1(A_2210, C_2207, '#skF_4'), '#skF_2', k1_tmap_1(A_2210, '#skF_2', C_2207, '#skF_4', E_2206, '#skF_6'), C_2207)=E_2206 | ~v1_funct_1(k1_tmap_1(A_2210, '#skF_2', C_2207, '#skF_4', E_2206, '#skF_6')) | k2_partfun1(C_2207, '#skF_2', E_2206, k9_subset_1(A_2210, C_2207, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2210, C_2207, '#skF_4')) | ~m1_subset_1(E_2206, k1_zfmisc_1(k2_zfmisc_1(C_2207, '#skF_2'))) | ~v1_funct_2(E_2206, C_2207, '#skF_2') | ~v1_funct_1(E_2206) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2210)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2207, k1_zfmisc_1(A_2210)) | v1_xboole_0(C_2207) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2210))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3671, c_94412])).
% 25.66/16.47  tff(c_101055, plain, (![A_2304, C_2305, E_2306]: (k2_partfun1(k4_subset_1(A_2304, C_2305, '#skF_4'), '#skF_2', k1_tmap_1(A_2304, '#skF_2', C_2305, '#skF_4', E_2306, '#skF_6'), C_2305)=E_2306 | ~v1_funct_1(k1_tmap_1(A_2304, '#skF_2', C_2305, '#skF_4', E_2306, '#skF_6')) | k2_partfun1(C_2305, '#skF_2', E_2306, k9_subset_1(A_2304, C_2305, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2304, C_2305, '#skF_4')) | ~m1_subset_1(E_2306, k1_zfmisc_1(k2_zfmisc_1(C_2305, '#skF_2'))) | ~v1_funct_2(E_2306, C_2305, '#skF_2') | ~v1_funct_1(E_2306) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2304)) | ~m1_subset_1(C_2305, k1_zfmisc_1(A_2304)) | v1_xboole_0(C_2305) | v1_xboole_0(A_2304))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_94420])).
% 25.66/16.47  tff(c_101060, plain, (![A_2304]: (k2_partfun1(k4_subset_1(A_2304, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2304, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2304, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2304, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2304, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2304)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2304)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2304))), inference(resolution, [status(thm)], [c_52, c_101055])).
% 25.66/16.47  tff(c_101068, plain, (![A_2304]: (k2_partfun1(k4_subset_1(A_2304, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2304, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2304, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2304, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2304, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2304)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2304)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2304))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3668, c_101060])).
% 25.66/16.47  tff(c_104682, plain, (![A_2326]: (k2_partfun1(k4_subset_1(A_2326, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2326, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2326, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2326, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2326, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2326)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2326)) | v1_xboole_0(A_2326))), inference(negUnitSimplification, [status(thm)], [c_66, c_101068])).
% 25.66/16.47  tff(c_4113, plain, (![B_492, A_493]: (k3_xboole_0(k1_relat_1(B_492), A_493)=k1_xboole_0 | k7_relat_1(B_492, A_493)!=k1_xboole_0 | ~v1_relat_1(B_492))), inference(resolution, [status(thm)], [c_3137, c_2])).
% 25.66/16.47  tff(c_6015, plain, (![B_600, A_601]: (k7_relat_1(B_600, k1_xboole_0)=k7_relat_1(B_600, A_601) | ~v1_relat_1(B_600) | k7_relat_1(B_600, A_601)!=k1_xboole_0 | ~v1_relat_1(B_600))), inference(superposition, [status(thm), theory('equality')], [c_4113, c_10])).
% 25.66/16.47  tff(c_6017, plain, (![A_601]: (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', A_601) | k7_relat_1('#skF_6', A_601)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_97, c_6015])).
% 25.66/16.47  tff(c_6026, plain, (![A_602]: (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', A_602) | k7_relat_1('#skF_6', A_602)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_6017])).
% 25.66/16.47  tff(c_6048, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3610, c_6026])).
% 25.66/16.47  tff(c_6078, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3610, c_6048])).
% 25.66/16.47  tff(c_6086, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6078, c_3963])).
% 25.66/16.47  tff(c_4099, plain, (![A_489, C_486, D_488, E_485, B_487, F_484]: (v1_funct_1(k1_tmap_1(A_489, B_487, C_486, D_488, E_485, F_484)) | ~m1_subset_1(F_484, k1_zfmisc_1(k2_zfmisc_1(D_488, B_487))) | ~v1_funct_2(F_484, D_488, B_487) | ~v1_funct_1(F_484) | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(C_486, B_487))) | ~v1_funct_2(E_485, C_486, B_487) | ~v1_funct_1(E_485) | ~m1_subset_1(D_488, k1_zfmisc_1(A_489)) | v1_xboole_0(D_488) | ~m1_subset_1(C_486, k1_zfmisc_1(A_489)) | v1_xboole_0(C_486) | v1_xboole_0(B_487) | v1_xboole_0(A_489))), inference(cnfTransformation, [status(thm)], [f_167])).
% 25.66/16.47  tff(c_4103, plain, (![A_489, C_486, E_485]: (v1_funct_1(k1_tmap_1(A_489, '#skF_2', C_486, '#skF_4', E_485, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(C_486, '#skF_2'))) | ~v1_funct_2(E_485, C_486, '#skF_2') | ~v1_funct_1(E_485) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_489)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_486, k1_zfmisc_1(A_489)) | v1_xboole_0(C_486) | v1_xboole_0('#skF_2') | v1_xboole_0(A_489))), inference(resolution, [status(thm)], [c_46, c_4099])).
% 25.66/16.47  tff(c_4110, plain, (![A_489, C_486, E_485]: (v1_funct_1(k1_tmap_1(A_489, '#skF_2', C_486, '#skF_4', E_485, '#skF_6')) | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(C_486, '#skF_2'))) | ~v1_funct_2(E_485, C_486, '#skF_2') | ~v1_funct_1(E_485) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_489)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_486, k1_zfmisc_1(A_489)) | v1_xboole_0(C_486) | v1_xboole_0('#skF_2') | v1_xboole_0(A_489))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4103])).
% 25.66/16.47  tff(c_4517, plain, (![A_539, C_540, E_541]: (v1_funct_1(k1_tmap_1(A_539, '#skF_2', C_540, '#skF_4', E_541, '#skF_6')) | ~m1_subset_1(E_541, k1_zfmisc_1(k2_zfmisc_1(C_540, '#skF_2'))) | ~v1_funct_2(E_541, C_540, '#skF_2') | ~v1_funct_1(E_541) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_539)) | ~m1_subset_1(C_540, k1_zfmisc_1(A_539)) | v1_xboole_0(C_540) | v1_xboole_0(A_539))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_4110])).
% 25.66/16.47  tff(c_4522, plain, (![A_539]: (v1_funct_1(k1_tmap_1(A_539, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_539)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_539)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_539))), inference(resolution, [status(thm)], [c_52, c_4517])).
% 25.66/16.47  tff(c_4530, plain, (![A_539]: (v1_funct_1(k1_tmap_1(A_539, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_539)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_539)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_539))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4522])).
% 25.66/16.47  tff(c_4712, plain, (![A_572]: (v1_funct_1(k1_tmap_1(A_572, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_572)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_572)) | v1_xboole_0(A_572))), inference(negUnitSimplification, [status(thm)], [c_66, c_4530])).
% 25.66/16.47  tff(c_4715, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_4712])).
% 25.66/16.47  tff(c_4718, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4715])).
% 25.66/16.47  tff(c_4719, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_4718])).
% 25.66/16.47  tff(c_4634, plain, (![B_549, C_544, E_548, A_547, D_546, F_545]: (k2_partfun1(k4_subset_1(A_547, C_544, D_546), B_549, k1_tmap_1(A_547, B_549, C_544, D_546, E_548, F_545), D_546)=F_545 | ~m1_subset_1(k1_tmap_1(A_547, B_549, C_544, D_546, E_548, F_545), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_547, C_544, D_546), B_549))) | ~v1_funct_2(k1_tmap_1(A_547, B_549, C_544, D_546, E_548, F_545), k4_subset_1(A_547, C_544, D_546), B_549) | ~v1_funct_1(k1_tmap_1(A_547, B_549, C_544, D_546, E_548, F_545)) | k2_partfun1(D_546, B_549, F_545, k9_subset_1(A_547, C_544, D_546))!=k2_partfun1(C_544, B_549, E_548, k9_subset_1(A_547, C_544, D_546)) | ~m1_subset_1(F_545, k1_zfmisc_1(k2_zfmisc_1(D_546, B_549))) | ~v1_funct_2(F_545, D_546, B_549) | ~v1_funct_1(F_545) | ~m1_subset_1(E_548, k1_zfmisc_1(k2_zfmisc_1(C_544, B_549))) | ~v1_funct_2(E_548, C_544, B_549) | ~v1_funct_1(E_548) | ~m1_subset_1(D_546, k1_zfmisc_1(A_547)) | v1_xboole_0(D_546) | ~m1_subset_1(C_544, k1_zfmisc_1(A_547)) | v1_xboole_0(C_544) | v1_xboole_0(B_549) | v1_xboole_0(A_547))), inference(cnfTransformation, [status(thm)], [f_133])).
% 25.66/16.47  tff(c_9041, plain, (![D_697, C_695, B_696, E_694, A_698, F_693]: (k2_partfun1(k4_subset_1(A_698, C_695, D_697), B_696, k1_tmap_1(A_698, B_696, C_695, D_697, E_694, F_693), D_697)=F_693 | ~v1_funct_2(k1_tmap_1(A_698, B_696, C_695, D_697, E_694, F_693), k4_subset_1(A_698, C_695, D_697), B_696) | ~v1_funct_1(k1_tmap_1(A_698, B_696, C_695, D_697, E_694, F_693)) | k2_partfun1(D_697, B_696, F_693, k9_subset_1(A_698, C_695, D_697))!=k2_partfun1(C_695, B_696, E_694, k9_subset_1(A_698, C_695, D_697)) | ~m1_subset_1(F_693, k1_zfmisc_1(k2_zfmisc_1(D_697, B_696))) | ~v1_funct_2(F_693, D_697, B_696) | ~v1_funct_1(F_693) | ~m1_subset_1(E_694, k1_zfmisc_1(k2_zfmisc_1(C_695, B_696))) | ~v1_funct_2(E_694, C_695, B_696) | ~v1_funct_1(E_694) | ~m1_subset_1(D_697, k1_zfmisc_1(A_698)) | v1_xboole_0(D_697) | ~m1_subset_1(C_695, k1_zfmisc_1(A_698)) | v1_xboole_0(C_695) | v1_xboole_0(B_696) | v1_xboole_0(A_698))), inference(resolution, [status(thm)], [c_38, c_4634])).
% 25.66/16.47  tff(c_24392, plain, (![C_982, F_980, E_981, D_984, B_983, A_985]: (k2_partfun1(k4_subset_1(A_985, C_982, D_984), B_983, k1_tmap_1(A_985, B_983, C_982, D_984, E_981, F_980), D_984)=F_980 | ~v1_funct_1(k1_tmap_1(A_985, B_983, C_982, D_984, E_981, F_980)) | k2_partfun1(D_984, B_983, F_980, k9_subset_1(A_985, C_982, D_984))!=k2_partfun1(C_982, B_983, E_981, k9_subset_1(A_985, C_982, D_984)) | ~m1_subset_1(F_980, k1_zfmisc_1(k2_zfmisc_1(D_984, B_983))) | ~v1_funct_2(F_980, D_984, B_983) | ~v1_funct_1(F_980) | ~m1_subset_1(E_981, k1_zfmisc_1(k2_zfmisc_1(C_982, B_983))) | ~v1_funct_2(E_981, C_982, B_983) | ~v1_funct_1(E_981) | ~m1_subset_1(D_984, k1_zfmisc_1(A_985)) | v1_xboole_0(D_984) | ~m1_subset_1(C_982, k1_zfmisc_1(A_985)) | v1_xboole_0(C_982) | v1_xboole_0(B_983) | v1_xboole_0(A_985))), inference(resolution, [status(thm)], [c_40, c_9041])).
% 25.66/16.47  tff(c_24398, plain, (![A_985, C_982, E_981]: (k2_partfun1(k4_subset_1(A_985, C_982, '#skF_4'), '#skF_2', k1_tmap_1(A_985, '#skF_2', C_982, '#skF_4', E_981, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_985, '#skF_2', C_982, '#skF_4', E_981, '#skF_6')) | k2_partfun1(C_982, '#skF_2', E_981, k9_subset_1(A_985, C_982, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_985, C_982, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_981, k1_zfmisc_1(k2_zfmisc_1(C_982, '#skF_2'))) | ~v1_funct_2(E_981, C_982, '#skF_2') | ~v1_funct_1(E_981) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_985)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_982, k1_zfmisc_1(A_985)) | v1_xboole_0(C_982) | v1_xboole_0('#skF_2') | v1_xboole_0(A_985))), inference(resolution, [status(thm)], [c_46, c_24392])).
% 25.66/16.47  tff(c_24406, plain, (![A_985, C_982, E_981]: (k2_partfun1(k4_subset_1(A_985, C_982, '#skF_4'), '#skF_2', k1_tmap_1(A_985, '#skF_2', C_982, '#skF_4', E_981, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_985, '#skF_2', C_982, '#skF_4', E_981, '#skF_6')) | k2_partfun1(C_982, '#skF_2', E_981, k9_subset_1(A_985, C_982, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_985, C_982, '#skF_4')) | ~m1_subset_1(E_981, k1_zfmisc_1(k2_zfmisc_1(C_982, '#skF_2'))) | ~v1_funct_2(E_981, C_982, '#skF_2') | ~v1_funct_1(E_981) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_985)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_982, k1_zfmisc_1(A_985)) | v1_xboole_0(C_982) | v1_xboole_0('#skF_2') | v1_xboole_0(A_985))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_3671, c_24398])).
% 25.66/16.47  tff(c_38715, plain, (![A_1139, C_1140, E_1141]: (k2_partfun1(k4_subset_1(A_1139, C_1140, '#skF_4'), '#skF_2', k1_tmap_1(A_1139, '#skF_2', C_1140, '#skF_4', E_1141, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1139, '#skF_2', C_1140, '#skF_4', E_1141, '#skF_6')) | k2_partfun1(C_1140, '#skF_2', E_1141, k9_subset_1(A_1139, C_1140, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1139, C_1140, '#skF_4')) | ~m1_subset_1(E_1141, k1_zfmisc_1(k2_zfmisc_1(C_1140, '#skF_2'))) | ~v1_funct_2(E_1141, C_1140, '#skF_2') | ~v1_funct_1(E_1141) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1139)) | ~m1_subset_1(C_1140, k1_zfmisc_1(A_1139)) | v1_xboole_0(C_1140) | v1_xboole_0(A_1139))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_24406])).
% 25.66/16.47  tff(c_38720, plain, (![A_1139]: (k2_partfun1(k4_subset_1(A_1139, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1139, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1139, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1139, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1139, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1139)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1139)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1139))), inference(resolution, [status(thm)], [c_52, c_38715])).
% 25.66/16.47  tff(c_38728, plain, (![A_1139]: (k2_partfun1(k4_subset_1(A_1139, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1139, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1139, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1139, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1139, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1139)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1139)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1139))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3668, c_38720])).
% 25.66/16.47  tff(c_39765, plain, (![A_1153]: (k2_partfun1(k4_subset_1(A_1153, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1153, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1153, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1153, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1153, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1153)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1153)) | v1_xboole_0(A_1153))), inference(negUnitSimplification, [status(thm)], [c_66, c_38728])).
% 25.66/16.47  tff(c_3095, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 25.66/16.47  tff(c_4001, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_3095])).
% 25.66/16.47  tff(c_39776, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_39765, c_4001])).
% 25.66/16.47  tff(c_39790, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_6086, c_6078, c_3962, c_3962, c_3528, c_3528, c_4719, c_39776])).
% 25.66/16.47  tff(c_39792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_39790])).
% 25.66/16.47  tff(c_39793, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_3095])).
% 25.66/16.47  tff(c_104694, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_104682, c_39793])).
% 25.66/16.47  tff(c_104708, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_41846, c_3962, c_3528, c_41854, c_3962, c_3528, c_40522, c_104694])).
% 25.66/16.47  tff(c_104710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_104708])).
% 25.66/16.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.66/16.47  
% 25.66/16.47  Inference rules
% 25.66/16.47  ----------------------
% 25.66/16.47  #Ref     : 0
% 25.66/16.47  #Sup     : 24492
% 25.66/16.47  #Fact    : 0
% 25.66/16.47  #Define  : 0
% 25.66/16.47  #Split   : 89
% 25.66/16.47  #Chain   : 0
% 25.66/16.47  #Close   : 0
% 25.66/16.47  
% 25.66/16.47  Ordering : KBO
% 25.66/16.47  
% 25.66/16.47  Simplification rules
% 25.66/16.47  ----------------------
% 25.66/16.47  #Subsume      : 12204
% 25.66/16.47  #Demod        : 18024
% 25.66/16.47  #Tautology    : 6381
% 25.66/16.47  #SimpNegUnit  : 750
% 25.66/16.47  #BackRed      : 7
% 25.66/16.47  
% 25.66/16.47  #Partial instantiations: 0
% 25.66/16.47  #Strategies tried      : 1
% 25.66/16.47  
% 25.66/16.47  Timing (in seconds)
% 25.66/16.47  ----------------------
% 25.66/16.47  Preprocessing        : 0.42
% 25.66/16.47  Parsing              : 0.21
% 25.66/16.47  CNF conversion       : 0.06
% 25.66/16.47  Main loop            : 15.17
% 25.66/16.47  Inferencing          : 2.38
% 25.66/16.47  Reduction            : 5.10
% 25.66/16.47  Demodulation         : 3.85
% 25.66/16.47  BG Simplification    : 0.24
% 25.66/16.47  Subsumption          : 6.95
% 25.66/16.47  Abstraction          : 0.37
% 25.66/16.47  MUC search           : 0.00
% 25.66/16.47  Cooper               : 0.00
% 25.66/16.47  Total                : 15.66
% 25.66/16.47  Index Insertion      : 0.00
% 25.66/16.47  Index Deletion       : 0.00
% 25.66/16.47  Index Matching       : 0.00
% 25.66/16.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
