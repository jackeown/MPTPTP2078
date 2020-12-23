%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:17 EST 2020

% Result     : Theorem 16.02s
% Output     : CNFRefutation 16.29s
% Verified   : 
% Statistics : Number of formulae       :  263 (3202 expanded)
%              Number of leaves         :   48 (1061 expanded)
%              Depth                    :   16
%              Number of atoms          :  781 (12494 expanded)
%              Number of equality atoms :  177 (2540 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_238,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_196,axiom,(
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

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_162,axiom,(
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

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [C_236,A_237,B_238] :
      ( v1_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_2214,plain,(
    ! [C_436,A_437,B_438] :
      ( v4_relat_1(C_436,A_437)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_437,B_438))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2256,plain,(
    ! [A_442] : v4_relat_1(k1_xboole_0,A_442) ),
    inference(resolution,[status(thm)],[c_8,c_2214])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2259,plain,(
    ! [A_442] :
      ( k7_relat_1(k1_xboole_0,A_442) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2256,c_16])).

tff(c_2262,plain,(
    ! [A_442] : k7_relat_1(k1_xboole_0,A_442) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2259])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_110,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_99])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2225,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2214])).

tff(c_2374,plain,(
    ! [B_466,A_467] :
      ( k1_relat_1(B_466) = A_467
      | ~ v1_partfun1(B_466,A_467)
      | ~ v4_relat_1(B_466,A_467)
      | ~ v1_relat_1(B_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2383,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2225,c_2374])).

tff(c_2392,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2383])).

tff(c_2785,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2392])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2939,plain,(
    ! [C_523,A_524,B_525] :
      ( v1_partfun1(C_523,A_524)
      | ~ v1_funct_2(C_523,A_524,B_525)
      | ~ v1_funct_1(C_523)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_524,B_525)))
      | v1_xboole_0(B_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2942,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2939])).

tff(c_2952,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2942])).

tff(c_2954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2785,c_2952])).

tff(c_2955,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2392])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r1_xboole_0(k1_relat_1(B_20),A_19)
      | k7_relat_1(B_20,A_19) != k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2966,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_3',A_19)
      | k7_relat_1('#skF_5',A_19) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2955,c_22])).

tff(c_2980,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_3',A_19)
      | k7_relat_1('#skF_5',A_19) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2966])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_111,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_99])).

tff(c_2226,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2214])).

tff(c_2380,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2226,c_2374])).

tff(c_2389,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2380])).

tff(c_2399,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2389])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2724,plain,(
    ! [C_505,A_506,B_507] :
      ( v1_partfun1(C_505,A_506)
      | ~ v1_funct_2(C_505,A_506,B_507)
      | ~ v1_funct_1(C_505)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(A_506,B_507)))
      | v1_xboole_0(B_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2730,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2724])).

tff(c_2741,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2730])).

tff(c_2743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2399,c_2741])).

tff(c_2744,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2389])).

tff(c_14,plain,(
    ! [A_12,B_14] :
      ( k7_relat_1(A_12,B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,k1_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2752,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_6',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2744,c_14])).

tff(c_3192,plain,(
    ! [B_541] :
      ( k7_relat_1('#skF_6',B_541) = k1_xboole_0
      | ~ r1_xboole_0(B_541,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2752])).

tff(c_3215,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2980,c_3192])).

tff(c_3260,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3215])).

tff(c_70,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | ~ r1_subset_1(A_21,B_22)
      | v1_xboole_0(B_22)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2960,plain,(
    ! [A_19] :
      ( k7_relat_1('#skF_5',A_19) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_19)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2955,c_20])).

tff(c_3006,plain,(
    ! [A_529] :
      ( k7_relat_1('#skF_5',A_529) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2960])).

tff(c_3010,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_22)
      | v1_xboole_0(B_22)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_3006])).

tff(c_3302,plain,(
    ! [B_550] :
      ( k7_relat_1('#skF_5',B_550) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_550)
      | v1_xboole_0(B_550) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3010])).

tff(c_3305,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3302])).

tff(c_3309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3260,c_3305])).

tff(c_3310,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3215])).

tff(c_2755,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_4',A_19)
      | k7_relat_1('#skF_6',A_19) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2744,c_22])).

tff(c_3125,plain,(
    ! [A_538] :
      ( r1_xboole_0('#skF_4',A_538)
      | k7_relat_1('#skF_6',A_538) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2755])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3334,plain,(
    ! [A_551] :
      ( k3_xboole_0('#skF_4',A_551) = k1_xboole_0
      | k7_relat_1('#skF_6',A_551) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3125,c_2])).

tff(c_3341,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3310,c_3334])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(k1_relat_1(B_18),A_17) = k1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2758,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_17)) = k3_xboole_0('#skF_4',A_17)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2744,c_18])).

tff(c_2771,plain,(
    ! [A_17] : k1_relat_1(k7_relat_1('#skF_6',A_17)) = k3_xboole_0('#skF_4',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2758])).

tff(c_3315,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3310,c_2771])).

tff(c_21701,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3341,c_3315])).

tff(c_21718,plain,(
    ! [A_19] :
      ( r1_xboole_0(k1_xboole_0,A_19)
      | k7_relat_1(k1_xboole_0,A_19) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21701,c_22])).

tff(c_21738,plain,(
    ! [A_1037] : r1_xboole_0(k1_xboole_0,A_1037) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2262,c_21718])).

tff(c_2963,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_5',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2955,c_14])).

tff(c_2978,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_5',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2963])).

tff(c_21758,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21738,c_2978])).

tff(c_2767,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_6',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2752])).

tff(c_21757,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21738,c_2767])).

tff(c_3311,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3215])).

tff(c_2969,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_17)) = k3_xboole_0('#skF_3',A_17)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2955,c_18])).

tff(c_2982,plain,(
    ! [A_17] : k1_relat_1(k7_relat_1('#skF_5',A_17)) = k3_xboole_0('#skF_3',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2969])).

tff(c_3322,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3311,c_2982])).

tff(c_21706,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21701,c_3322])).

tff(c_2358,plain,(
    ! [A_463,B_464,C_465] :
      ( k9_subset_1(A_463,B_464,C_465) = k3_xboole_0(B_464,C_465)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(A_463)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2371,plain,(
    ! [B_464] : k9_subset_1('#skF_1',B_464,'#skF_4') = k3_xboole_0(B_464,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2358])).

tff(c_21899,plain,(
    ! [C_1047,F_1045,B_1044,D_1046,A_1049,E_1048] :
      ( v1_funct_1(k1_tmap_1(A_1049,B_1044,C_1047,D_1046,E_1048,F_1045))
      | ~ m1_subset_1(F_1045,k1_zfmisc_1(k2_zfmisc_1(D_1046,B_1044)))
      | ~ v1_funct_2(F_1045,D_1046,B_1044)
      | ~ v1_funct_1(F_1045)
      | ~ m1_subset_1(E_1048,k1_zfmisc_1(k2_zfmisc_1(C_1047,B_1044)))
      | ~ v1_funct_2(E_1048,C_1047,B_1044)
      | ~ v1_funct_1(E_1048)
      | ~ m1_subset_1(D_1046,k1_zfmisc_1(A_1049))
      | v1_xboole_0(D_1046)
      | ~ m1_subset_1(C_1047,k1_zfmisc_1(A_1049))
      | v1_xboole_0(C_1047)
      | v1_xboole_0(B_1044)
      | v1_xboole_0(A_1049) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_21903,plain,(
    ! [A_1049,C_1047,E_1048] :
      ( v1_funct_1(k1_tmap_1(A_1049,'#skF_2',C_1047,'#skF_4',E_1048,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1048,k1_zfmisc_1(k2_zfmisc_1(C_1047,'#skF_2')))
      | ~ v1_funct_2(E_1048,C_1047,'#skF_2')
      | ~ v1_funct_1(E_1048)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1049))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1047,k1_zfmisc_1(A_1049))
      | v1_xboole_0(C_1047)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1049) ) ),
    inference(resolution,[status(thm)],[c_58,c_21899])).

tff(c_21913,plain,(
    ! [A_1049,C_1047,E_1048] :
      ( v1_funct_1(k1_tmap_1(A_1049,'#skF_2',C_1047,'#skF_4',E_1048,'#skF_6'))
      | ~ m1_subset_1(E_1048,k1_zfmisc_1(k2_zfmisc_1(C_1047,'#skF_2')))
      | ~ v1_funct_2(E_1048,C_1047,'#skF_2')
      | ~ v1_funct_1(E_1048)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1049))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1047,k1_zfmisc_1(A_1049))
      | v1_xboole_0(C_1047)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1049) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_21903])).

tff(c_22266,plain,(
    ! [A_1077,C_1078,E_1079] :
      ( v1_funct_1(k1_tmap_1(A_1077,'#skF_2',C_1078,'#skF_4',E_1079,'#skF_6'))
      | ~ m1_subset_1(E_1079,k1_zfmisc_1(k2_zfmisc_1(C_1078,'#skF_2')))
      | ~ v1_funct_2(E_1079,C_1078,'#skF_2')
      | ~ v1_funct_1(E_1079)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1077))
      | ~ m1_subset_1(C_1078,k1_zfmisc_1(A_1077))
      | v1_xboole_0(C_1078)
      | v1_xboole_0(A_1077) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_21913])).

tff(c_22271,plain,(
    ! [A_1077] :
      ( v1_funct_1(k1_tmap_1(A_1077,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1077))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1077))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1077) ) ),
    inference(resolution,[status(thm)],[c_64,c_22266])).

tff(c_22282,plain,(
    ! [A_1077] :
      ( v1_funct_1(k1_tmap_1(A_1077,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1077))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1077))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1077) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_22271])).

tff(c_22702,plain,(
    ! [A_1106] :
      ( v1_funct_1(k1_tmap_1(A_1106,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1106))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1106))
      | v1_xboole_0(A_1106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_22282])).

tff(c_22705,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_22702])).

tff(c_22708,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22705])).

tff(c_22709,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_22708])).

tff(c_3072,plain,(
    ! [A_532,B_533,C_534,D_535] :
      ( k2_partfun1(A_532,B_533,C_534,D_535) = k7_relat_1(C_534,D_535)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(A_532,B_533)))
      | ~ v1_funct_1(C_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3074,plain,(
    ! [D_535] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_535) = k7_relat_1('#skF_5',D_535)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_3072])).

tff(c_3082,plain,(
    ! [D_535] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_535) = k7_relat_1('#skF_5',D_535) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3074])).

tff(c_3076,plain,(
    ! [D_535] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_535) = k7_relat_1('#skF_6',D_535)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_3072])).

tff(c_3085,plain,(
    ! [D_535] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_535) = k7_relat_1('#skF_6',D_535) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3076])).

tff(c_52,plain,(
    ! [D_169,E_170,A_166,B_167,C_168,F_171] :
      ( v1_funct_2(k1_tmap_1(A_166,B_167,C_168,D_169,E_170,F_171),k4_subset_1(A_166,C_168,D_169),B_167)
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(D_169,B_167)))
      | ~ v1_funct_2(F_171,D_169,B_167)
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(C_168,B_167)))
      | ~ v1_funct_2(E_170,C_168,B_167)
      | ~ v1_funct_1(E_170)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(A_166))
      | v1_xboole_0(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | v1_xboole_0(C_168)
      | v1_xboole_0(B_167)
      | v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_50,plain,(
    ! [D_169,E_170,A_166,B_167,C_168,F_171] :
      ( m1_subset_1(k1_tmap_1(A_166,B_167,C_168,D_169,E_170,F_171),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_166,C_168,D_169),B_167)))
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(D_169,B_167)))
      | ~ v1_funct_2(F_171,D_169,B_167)
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(C_168,B_167)))
      | ~ v1_funct_2(E_170,C_168,B_167)
      | ~ v1_funct_1(E_170)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(A_166))
      | v1_xboole_0(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | v1_xboole_0(C_168)
      | v1_xboole_0(B_167)
      | v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_22655,plain,(
    ! [E_1101,B_1104,D_1100,A_1099,C_1103,F_1102] :
      ( k2_partfun1(k4_subset_1(A_1099,C_1103,D_1100),B_1104,k1_tmap_1(A_1099,B_1104,C_1103,D_1100,E_1101,F_1102),C_1103) = E_1101
      | ~ m1_subset_1(k1_tmap_1(A_1099,B_1104,C_1103,D_1100,E_1101,F_1102),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1099,C_1103,D_1100),B_1104)))
      | ~ v1_funct_2(k1_tmap_1(A_1099,B_1104,C_1103,D_1100,E_1101,F_1102),k4_subset_1(A_1099,C_1103,D_1100),B_1104)
      | ~ v1_funct_1(k1_tmap_1(A_1099,B_1104,C_1103,D_1100,E_1101,F_1102))
      | k2_partfun1(D_1100,B_1104,F_1102,k9_subset_1(A_1099,C_1103,D_1100)) != k2_partfun1(C_1103,B_1104,E_1101,k9_subset_1(A_1099,C_1103,D_1100))
      | ~ m1_subset_1(F_1102,k1_zfmisc_1(k2_zfmisc_1(D_1100,B_1104)))
      | ~ v1_funct_2(F_1102,D_1100,B_1104)
      | ~ v1_funct_1(F_1102)
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(C_1103,B_1104)))
      | ~ v1_funct_2(E_1101,C_1103,B_1104)
      | ~ v1_funct_1(E_1101)
      | ~ m1_subset_1(D_1100,k1_zfmisc_1(A_1099))
      | v1_xboole_0(D_1100)
      | ~ m1_subset_1(C_1103,k1_zfmisc_1(A_1099))
      | v1_xboole_0(C_1103)
      | v1_xboole_0(B_1104)
      | v1_xboole_0(A_1099) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_27839,plain,(
    ! [D_1289,E_1291,A_1292,B_1287,C_1290,F_1288] :
      ( k2_partfun1(k4_subset_1(A_1292,C_1290,D_1289),B_1287,k1_tmap_1(A_1292,B_1287,C_1290,D_1289,E_1291,F_1288),C_1290) = E_1291
      | ~ v1_funct_2(k1_tmap_1(A_1292,B_1287,C_1290,D_1289,E_1291,F_1288),k4_subset_1(A_1292,C_1290,D_1289),B_1287)
      | ~ v1_funct_1(k1_tmap_1(A_1292,B_1287,C_1290,D_1289,E_1291,F_1288))
      | k2_partfun1(D_1289,B_1287,F_1288,k9_subset_1(A_1292,C_1290,D_1289)) != k2_partfun1(C_1290,B_1287,E_1291,k9_subset_1(A_1292,C_1290,D_1289))
      | ~ m1_subset_1(F_1288,k1_zfmisc_1(k2_zfmisc_1(D_1289,B_1287)))
      | ~ v1_funct_2(F_1288,D_1289,B_1287)
      | ~ v1_funct_1(F_1288)
      | ~ m1_subset_1(E_1291,k1_zfmisc_1(k2_zfmisc_1(C_1290,B_1287)))
      | ~ v1_funct_2(E_1291,C_1290,B_1287)
      | ~ v1_funct_1(E_1291)
      | ~ m1_subset_1(D_1289,k1_zfmisc_1(A_1292))
      | v1_xboole_0(D_1289)
      | ~ m1_subset_1(C_1290,k1_zfmisc_1(A_1292))
      | v1_xboole_0(C_1290)
      | v1_xboole_0(B_1287)
      | v1_xboole_0(A_1292) ) ),
    inference(resolution,[status(thm)],[c_50,c_22655])).

tff(c_32848,plain,(
    ! [A_1393,F_1389,B_1388,C_1391,D_1390,E_1392] :
      ( k2_partfun1(k4_subset_1(A_1393,C_1391,D_1390),B_1388,k1_tmap_1(A_1393,B_1388,C_1391,D_1390,E_1392,F_1389),C_1391) = E_1392
      | ~ v1_funct_1(k1_tmap_1(A_1393,B_1388,C_1391,D_1390,E_1392,F_1389))
      | k2_partfun1(D_1390,B_1388,F_1389,k9_subset_1(A_1393,C_1391,D_1390)) != k2_partfun1(C_1391,B_1388,E_1392,k9_subset_1(A_1393,C_1391,D_1390))
      | ~ m1_subset_1(F_1389,k1_zfmisc_1(k2_zfmisc_1(D_1390,B_1388)))
      | ~ v1_funct_2(F_1389,D_1390,B_1388)
      | ~ v1_funct_1(F_1389)
      | ~ m1_subset_1(E_1392,k1_zfmisc_1(k2_zfmisc_1(C_1391,B_1388)))
      | ~ v1_funct_2(E_1392,C_1391,B_1388)
      | ~ v1_funct_1(E_1392)
      | ~ m1_subset_1(D_1390,k1_zfmisc_1(A_1393))
      | v1_xboole_0(D_1390)
      | ~ m1_subset_1(C_1391,k1_zfmisc_1(A_1393))
      | v1_xboole_0(C_1391)
      | v1_xboole_0(B_1388)
      | v1_xboole_0(A_1393) ) ),
    inference(resolution,[status(thm)],[c_52,c_27839])).

tff(c_32854,plain,(
    ! [A_1393,C_1391,E_1392] :
      ( k2_partfun1(k4_subset_1(A_1393,C_1391,'#skF_4'),'#skF_2',k1_tmap_1(A_1393,'#skF_2',C_1391,'#skF_4',E_1392,'#skF_6'),C_1391) = E_1392
      | ~ v1_funct_1(k1_tmap_1(A_1393,'#skF_2',C_1391,'#skF_4',E_1392,'#skF_6'))
      | k2_partfun1(C_1391,'#skF_2',E_1392,k9_subset_1(A_1393,C_1391,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1393,C_1391,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1392,k1_zfmisc_1(k2_zfmisc_1(C_1391,'#skF_2')))
      | ~ v1_funct_2(E_1392,C_1391,'#skF_2')
      | ~ v1_funct_1(E_1392)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1393))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1391,k1_zfmisc_1(A_1393))
      | v1_xboole_0(C_1391)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1393) ) ),
    inference(resolution,[status(thm)],[c_58,c_32848])).

tff(c_32865,plain,(
    ! [A_1393,C_1391,E_1392] :
      ( k2_partfun1(k4_subset_1(A_1393,C_1391,'#skF_4'),'#skF_2',k1_tmap_1(A_1393,'#skF_2',C_1391,'#skF_4',E_1392,'#skF_6'),C_1391) = E_1392
      | ~ v1_funct_1(k1_tmap_1(A_1393,'#skF_2',C_1391,'#skF_4',E_1392,'#skF_6'))
      | k2_partfun1(C_1391,'#skF_2',E_1392,k9_subset_1(A_1393,C_1391,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1393,C_1391,'#skF_4'))
      | ~ m1_subset_1(E_1392,k1_zfmisc_1(k2_zfmisc_1(C_1391,'#skF_2')))
      | ~ v1_funct_2(E_1392,C_1391,'#skF_2')
      | ~ v1_funct_1(E_1392)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1393))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1391,k1_zfmisc_1(A_1393))
      | v1_xboole_0(C_1391)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3085,c_32854])).

tff(c_40184,plain,(
    ! [A_1519,C_1520,E_1521] :
      ( k2_partfun1(k4_subset_1(A_1519,C_1520,'#skF_4'),'#skF_2',k1_tmap_1(A_1519,'#skF_2',C_1520,'#skF_4',E_1521,'#skF_6'),C_1520) = E_1521
      | ~ v1_funct_1(k1_tmap_1(A_1519,'#skF_2',C_1520,'#skF_4',E_1521,'#skF_6'))
      | k2_partfun1(C_1520,'#skF_2',E_1521,k9_subset_1(A_1519,C_1520,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1519,C_1520,'#skF_4'))
      | ~ m1_subset_1(E_1521,k1_zfmisc_1(k2_zfmisc_1(C_1520,'#skF_2')))
      | ~ v1_funct_2(E_1521,C_1520,'#skF_2')
      | ~ v1_funct_1(E_1521)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1519))
      | ~ m1_subset_1(C_1520,k1_zfmisc_1(A_1519))
      | v1_xboole_0(C_1520)
      | v1_xboole_0(A_1519) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_32865])).

tff(c_40189,plain,(
    ! [A_1519] :
      ( k2_partfun1(k4_subset_1(A_1519,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1519,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1519,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1519,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1519,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1519))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1519))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1519) ) ),
    inference(resolution,[status(thm)],[c_64,c_40184])).

tff(c_40200,plain,(
    ! [A_1519] :
      ( k2_partfun1(k4_subset_1(A_1519,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1519,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1519,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1519,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1519,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1519))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1519))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1519) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3082,c_40189])).

tff(c_49645,plain,(
    ! [A_1675] :
      ( k2_partfun1(k4_subset_1(A_1675,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1675,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1675,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1675,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1675,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1675))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1675))
      | v1_xboole_0(A_1675) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_40200])).

tff(c_3344,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3341,c_3315])).

tff(c_3361,plain,(
    ! [A_19] :
      ( r1_xboole_0(k1_xboole_0,A_19)
      | k7_relat_1(k1_xboole_0,A_19) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3344,c_22])).

tff(c_3390,plain,(
    ! [A_553] : r1_xboole_0(k1_xboole_0,A_553) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2262,c_3361])).

tff(c_3409,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3390,c_2767])).

tff(c_3410,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3390,c_2978])).

tff(c_3349,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3344,c_3322])).

tff(c_3470,plain,(
    ! [A_562,B_557,E_561,F_558,D_559,C_560] :
      ( v1_funct_1(k1_tmap_1(A_562,B_557,C_560,D_559,E_561,F_558))
      | ~ m1_subset_1(F_558,k1_zfmisc_1(k2_zfmisc_1(D_559,B_557)))
      | ~ v1_funct_2(F_558,D_559,B_557)
      | ~ v1_funct_1(F_558)
      | ~ m1_subset_1(E_561,k1_zfmisc_1(k2_zfmisc_1(C_560,B_557)))
      | ~ v1_funct_2(E_561,C_560,B_557)
      | ~ v1_funct_1(E_561)
      | ~ m1_subset_1(D_559,k1_zfmisc_1(A_562))
      | v1_xboole_0(D_559)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(A_562))
      | v1_xboole_0(C_560)
      | v1_xboole_0(B_557)
      | v1_xboole_0(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_3474,plain,(
    ! [A_562,C_560,E_561] :
      ( v1_funct_1(k1_tmap_1(A_562,'#skF_2',C_560,'#skF_4',E_561,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_561,k1_zfmisc_1(k2_zfmisc_1(C_560,'#skF_2')))
      | ~ v1_funct_2(E_561,C_560,'#skF_2')
      | ~ v1_funct_1(E_561)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_562))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_560,k1_zfmisc_1(A_562))
      | v1_xboole_0(C_560)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_562) ) ),
    inference(resolution,[status(thm)],[c_58,c_3470])).

tff(c_3484,plain,(
    ! [A_562,C_560,E_561] :
      ( v1_funct_1(k1_tmap_1(A_562,'#skF_2',C_560,'#skF_4',E_561,'#skF_6'))
      | ~ m1_subset_1(E_561,k1_zfmisc_1(k2_zfmisc_1(C_560,'#skF_2')))
      | ~ v1_funct_2(E_561,C_560,'#skF_2')
      | ~ v1_funct_1(E_561)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_562))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_560,k1_zfmisc_1(A_562))
      | v1_xboole_0(C_560)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3474])).

tff(c_4953,plain,(
    ! [A_642,C_643,E_644] :
      ( v1_funct_1(k1_tmap_1(A_642,'#skF_2',C_643,'#skF_4',E_644,'#skF_6'))
      | ~ m1_subset_1(E_644,k1_zfmisc_1(k2_zfmisc_1(C_643,'#skF_2')))
      | ~ v1_funct_2(E_644,C_643,'#skF_2')
      | ~ v1_funct_1(E_644)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_642))
      | ~ m1_subset_1(C_643,k1_zfmisc_1(A_642))
      | v1_xboole_0(C_643)
      | v1_xboole_0(A_642) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_3484])).

tff(c_4958,plain,(
    ! [A_642] :
      ( v1_funct_1(k1_tmap_1(A_642,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_642))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_642))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_642) ) ),
    inference(resolution,[status(thm)],[c_64,c_4953])).

tff(c_4969,plain,(
    ! [A_642] :
      ( v1_funct_1(k1_tmap_1(A_642,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_642))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_642))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_642) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_4958])).

tff(c_5423,plain,(
    ! [A_662] :
      ( v1_funct_1(k1_tmap_1(A_662,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_662))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_662))
      | v1_xboole_0(A_662) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4969])).

tff(c_5426,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_5423])).

tff(c_5429,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5426])).

tff(c_5430,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5429])).

tff(c_3949,plain,(
    ! [C_598,F_597,A_594,E_596,D_595,B_599] :
      ( k2_partfun1(k4_subset_1(A_594,C_598,D_595),B_599,k1_tmap_1(A_594,B_599,C_598,D_595,E_596,F_597),D_595) = F_597
      | ~ m1_subset_1(k1_tmap_1(A_594,B_599,C_598,D_595,E_596,F_597),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_594,C_598,D_595),B_599)))
      | ~ v1_funct_2(k1_tmap_1(A_594,B_599,C_598,D_595,E_596,F_597),k4_subset_1(A_594,C_598,D_595),B_599)
      | ~ v1_funct_1(k1_tmap_1(A_594,B_599,C_598,D_595,E_596,F_597))
      | k2_partfun1(D_595,B_599,F_597,k9_subset_1(A_594,C_598,D_595)) != k2_partfun1(C_598,B_599,E_596,k9_subset_1(A_594,C_598,D_595))
      | ~ m1_subset_1(F_597,k1_zfmisc_1(k2_zfmisc_1(D_595,B_599)))
      | ~ v1_funct_2(F_597,D_595,B_599)
      | ~ v1_funct_1(F_597)
      | ~ m1_subset_1(E_596,k1_zfmisc_1(k2_zfmisc_1(C_598,B_599)))
      | ~ v1_funct_2(E_596,C_598,B_599)
      | ~ v1_funct_1(E_596)
      | ~ m1_subset_1(D_595,k1_zfmisc_1(A_594))
      | v1_xboole_0(D_595)
      | ~ m1_subset_1(C_598,k1_zfmisc_1(A_594))
      | v1_xboole_0(C_598)
      | v1_xboole_0(B_599)
      | v1_xboole_0(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_8898,plain,(
    ! [F_795,C_797,A_799,D_796,B_794,E_798] :
      ( k2_partfun1(k4_subset_1(A_799,C_797,D_796),B_794,k1_tmap_1(A_799,B_794,C_797,D_796,E_798,F_795),D_796) = F_795
      | ~ v1_funct_2(k1_tmap_1(A_799,B_794,C_797,D_796,E_798,F_795),k4_subset_1(A_799,C_797,D_796),B_794)
      | ~ v1_funct_1(k1_tmap_1(A_799,B_794,C_797,D_796,E_798,F_795))
      | k2_partfun1(D_796,B_794,F_795,k9_subset_1(A_799,C_797,D_796)) != k2_partfun1(C_797,B_794,E_798,k9_subset_1(A_799,C_797,D_796))
      | ~ m1_subset_1(F_795,k1_zfmisc_1(k2_zfmisc_1(D_796,B_794)))
      | ~ v1_funct_2(F_795,D_796,B_794)
      | ~ v1_funct_1(F_795)
      | ~ m1_subset_1(E_798,k1_zfmisc_1(k2_zfmisc_1(C_797,B_794)))
      | ~ v1_funct_2(E_798,C_797,B_794)
      | ~ v1_funct_1(E_798)
      | ~ m1_subset_1(D_796,k1_zfmisc_1(A_799))
      | v1_xboole_0(D_796)
      | ~ m1_subset_1(C_797,k1_zfmisc_1(A_799))
      | v1_xboole_0(C_797)
      | v1_xboole_0(B_794)
      | v1_xboole_0(A_799) ) ),
    inference(resolution,[status(thm)],[c_50,c_3949])).

tff(c_13460,plain,(
    ! [E_891,D_889,B_887,A_892,C_890,F_888] :
      ( k2_partfun1(k4_subset_1(A_892,C_890,D_889),B_887,k1_tmap_1(A_892,B_887,C_890,D_889,E_891,F_888),D_889) = F_888
      | ~ v1_funct_1(k1_tmap_1(A_892,B_887,C_890,D_889,E_891,F_888))
      | k2_partfun1(D_889,B_887,F_888,k9_subset_1(A_892,C_890,D_889)) != k2_partfun1(C_890,B_887,E_891,k9_subset_1(A_892,C_890,D_889))
      | ~ m1_subset_1(F_888,k1_zfmisc_1(k2_zfmisc_1(D_889,B_887)))
      | ~ v1_funct_2(F_888,D_889,B_887)
      | ~ v1_funct_1(F_888)
      | ~ m1_subset_1(E_891,k1_zfmisc_1(k2_zfmisc_1(C_890,B_887)))
      | ~ v1_funct_2(E_891,C_890,B_887)
      | ~ v1_funct_1(E_891)
      | ~ m1_subset_1(D_889,k1_zfmisc_1(A_892))
      | v1_xboole_0(D_889)
      | ~ m1_subset_1(C_890,k1_zfmisc_1(A_892))
      | v1_xboole_0(C_890)
      | v1_xboole_0(B_887)
      | v1_xboole_0(A_892) ) ),
    inference(resolution,[status(thm)],[c_52,c_8898])).

tff(c_13466,plain,(
    ! [A_892,C_890,E_891] :
      ( k2_partfun1(k4_subset_1(A_892,C_890,'#skF_4'),'#skF_2',k1_tmap_1(A_892,'#skF_2',C_890,'#skF_4',E_891,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_892,'#skF_2',C_890,'#skF_4',E_891,'#skF_6'))
      | k2_partfun1(C_890,'#skF_2',E_891,k9_subset_1(A_892,C_890,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_892,C_890,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_891,k1_zfmisc_1(k2_zfmisc_1(C_890,'#skF_2')))
      | ~ v1_funct_2(E_891,C_890,'#skF_2')
      | ~ v1_funct_1(E_891)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_892))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_890,k1_zfmisc_1(A_892))
      | v1_xboole_0(C_890)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_892) ) ),
    inference(resolution,[status(thm)],[c_58,c_13460])).

tff(c_13477,plain,(
    ! [A_892,C_890,E_891] :
      ( k2_partfun1(k4_subset_1(A_892,C_890,'#skF_4'),'#skF_2',k1_tmap_1(A_892,'#skF_2',C_890,'#skF_4',E_891,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_892,'#skF_2',C_890,'#skF_4',E_891,'#skF_6'))
      | k2_partfun1(C_890,'#skF_2',E_891,k9_subset_1(A_892,C_890,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_892,C_890,'#skF_4'))
      | ~ m1_subset_1(E_891,k1_zfmisc_1(k2_zfmisc_1(C_890,'#skF_2')))
      | ~ v1_funct_2(E_891,C_890,'#skF_2')
      | ~ v1_funct_1(E_891)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_892))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_890,k1_zfmisc_1(A_892))
      | v1_xboole_0(C_890)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_892) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3085,c_13466])).

tff(c_20113,plain,(
    ! [A_1022,C_1023,E_1024] :
      ( k2_partfun1(k4_subset_1(A_1022,C_1023,'#skF_4'),'#skF_2',k1_tmap_1(A_1022,'#skF_2',C_1023,'#skF_4',E_1024,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1022,'#skF_2',C_1023,'#skF_4',E_1024,'#skF_6'))
      | k2_partfun1(C_1023,'#skF_2',E_1024,k9_subset_1(A_1022,C_1023,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1022,C_1023,'#skF_4'))
      | ~ m1_subset_1(E_1024,k1_zfmisc_1(k2_zfmisc_1(C_1023,'#skF_2')))
      | ~ v1_funct_2(E_1024,C_1023,'#skF_2')
      | ~ v1_funct_1(E_1024)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1022))
      | ~ m1_subset_1(C_1023,k1_zfmisc_1(A_1022))
      | v1_xboole_0(C_1023)
      | v1_xboole_0(A_1022) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_13477])).

tff(c_20118,plain,(
    ! [A_1022] :
      ( k2_partfun1(k4_subset_1(A_1022,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1022,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1022,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1022,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1022,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1022))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1022))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1022) ) ),
    inference(resolution,[status(thm)],[c_64,c_20113])).

tff(c_20129,plain,(
    ! [A_1022] :
      ( k2_partfun1(k4_subset_1(A_1022,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1022,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1022,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1022,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1022,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1022))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1022))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1022) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3082,c_20118])).

tff(c_21671,plain,(
    ! [A_1036] :
      ( k2_partfun1(k4_subset_1(A_1036,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1036,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1036,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1036,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1036,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1036))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1036))
      | v1_xboole_0(A_1036) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_20129])).

tff(c_115,plain,(
    ! [C_241,A_242,B_243] :
      ( v4_relat_1(C_241,A_242)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_155,plain,(
    ! [A_247] : v4_relat_1(k1_xboole_0,A_247) ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_158,plain,(
    ! [A_247] :
      ( k7_relat_1(k1_xboole_0,A_247) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_155,c_16])).

tff(c_161,plain,(
    ! [A_247] : k7_relat_1(k1_xboole_0,A_247) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_158])).

tff(c_127,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_115])).

tff(c_332,plain,(
    ! [B_281,A_282] :
      ( k1_relat_1(B_281) = A_282
      | ~ v1_partfun1(B_281,A_282)
      | ~ v4_relat_1(B_281,A_282)
      | ~ v1_relat_1(B_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_338,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_127,c_332])).

tff(c_347,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_338])).

tff(c_357,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_671,plain,(
    ! [C_314,A_315,B_316] :
      ( v1_partfun1(C_314,A_315)
      | ~ v1_funct_2(C_314,A_315,B_316)
      | ~ v1_funct_1(C_314)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316)))
      | v1_xboole_0(B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_677,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_671])).

tff(c_688,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_677])).

tff(c_690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_357,c_688])).

tff(c_691,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_702,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_4',A_19)
      | k7_relat_1('#skF_6',A_19) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_22])).

tff(c_716,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_4',A_19)
      | k7_relat_1('#skF_6',A_19) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_702])).

tff(c_126,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_341,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_332])).

tff(c_350,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_341])).

tff(c_723,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_872,plain,(
    ! [C_329,A_330,B_331] :
      ( v1_partfun1(C_329,A_330)
      | ~ v1_funct_2(C_329,A_330,B_331)
      | ~ v1_funct_1(C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | v1_xboole_0(B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_875,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_872])).

tff(c_885,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_875])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_723,c_885])).

tff(c_888,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_902,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_5',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_14])).

tff(c_936,plain,(
    ! [B_333] :
      ( k7_relat_1('#skF_5',B_333) = k1_xboole_0
      | ~ r1_xboole_0(B_333,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_902])).

tff(c_953,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_716,c_936])).

tff(c_1193,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_953])).

tff(c_899,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_3',A_19)
      | k7_relat_1('#skF_5',A_19) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_22])).

tff(c_913,plain,(
    ! [A_19] :
      ( r1_xboole_0('#skF_3',A_19)
      | k7_relat_1('#skF_5',A_19) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_899])).

tff(c_705,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_6',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_14])).

tff(c_1098,plain,(
    ! [B_344] :
      ( k7_relat_1('#skF_6',B_344) = k1_xboole_0
      | ~ r1_xboole_0(B_344,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_705])).

tff(c_1119,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_913,c_1098])).

tff(c_1194,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1193,c_1119])).

tff(c_893,plain,(
    ! [A_19] :
      ( k7_relat_1('#skF_5',A_19) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_19)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_20])).

tff(c_1014,plain,(
    ! [A_336] :
      ( k7_relat_1('#skF_5',A_336) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_893])).

tff(c_1021,plain,(
    ! [B_22] :
      ( k7_relat_1('#skF_5',B_22) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_22)
      | v1_xboole_0(B_22)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_1014])).

tff(c_1241,plain,(
    ! [B_359] :
      ( k7_relat_1('#skF_5',B_359) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_359)
      | v1_xboole_0(B_359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1021])).

tff(c_1244,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1241])).

tff(c_1248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1194,c_1244])).

tff(c_1250,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_920,plain,(
    ! [A_332] :
      ( r1_xboole_0('#skF_4',A_332)
      | k7_relat_1('#skF_6',A_332) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_702])).

tff(c_1300,plain,(
    ! [A_366] :
      ( k3_xboole_0('#skF_4',A_366) = k1_xboole_0
      | k7_relat_1('#skF_6',A_366) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_920,c_2])).

tff(c_1307,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_1300])).

tff(c_708,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_17)) = k3_xboole_0('#skF_4',A_17)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_691,c_18])).

tff(c_720,plain,(
    ! [A_17] : k1_relat_1(k7_relat_1('#skF_6',A_17)) = k3_xboole_0('#skF_4',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_708])).

tff(c_1269,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_720])).

tff(c_1309,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_1269])).

tff(c_1326,plain,(
    ! [A_19] :
      ( r1_xboole_0(k1_xboole_0,A_19)
      | k7_relat_1(k1_xboole_0,A_19) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1309,c_22])).

tff(c_1354,plain,(
    ! [A_368] : r1_xboole_0(k1_xboole_0,A_368) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_161,c_1326])).

tff(c_718,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_6',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_705])).

tff(c_1373,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1354,c_718])).

tff(c_915,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_5',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_902])).

tff(c_1374,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1354,c_915])).

tff(c_1249,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_905,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_17)) = k3_xboole_0('#skF_3',A_17)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_18])).

tff(c_917,plain,(
    ! [A_17] : k1_relat_1(k7_relat_1('#skF_5',A_17)) = k3_xboole_0('#skF_3',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_905])).

tff(c_1257,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_917])).

tff(c_1314,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_1257])).

tff(c_1031,plain,(
    ! [A_337,B_338,C_339,D_340] :
      ( k2_partfun1(A_337,B_338,C_339,D_340) = k7_relat_1(C_339,D_340)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338)))
      | ~ v1_funct_1(C_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1033,plain,(
    ! [D_340] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_340) = k7_relat_1('#skF_5',D_340)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_1031])).

tff(c_1041,plain,(
    ! [D_340] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_340) = k7_relat_1('#skF_5',D_340) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1033])).

tff(c_1035,plain,(
    ! [D_340] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_340) = k7_relat_1('#skF_6',D_340)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_1031])).

tff(c_1044,plain,(
    ! [D_340] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_340) = k7_relat_1('#skF_6',D_340) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1035])).

tff(c_270,plain,(
    ! [A_272,B_273,C_274] :
      ( k9_subset_1(A_272,B_273,C_274) = k3_xboole_0(B_273,C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(A_272)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_283,plain,(
    ! [B_273] : k9_subset_1('#skF_1',B_273,'#skF_4') = k3_xboole_0(B_273,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_270])).

tff(c_56,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_113,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_286,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_283,c_113])).

tff(c_1127,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_286])).

tff(c_2195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_1374,c_1314,c_1314,c_1041,c_1127])).

tff(c_2196,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3343,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2196])).

tff(c_21682,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_21671,c_3343])).

tff(c_21696,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_3409,c_3410,c_3349,c_3349,c_2371,c_2371,c_5430,c_21682])).

tff(c_21698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_21696])).

tff(c_21699,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2196])).

tff(c_49654,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_49645,c_21699])).

tff(c_49665,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_21758,c_21757,c_21706,c_21706,c_2371,c_2371,c_22709,c_49654])).

tff(c_49667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_49665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.02/8.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.19/8.33  
% 16.19/8.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.19/8.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.19/8.33  
% 16.19/8.33  %Foreground sorts:
% 16.19/8.33  
% 16.19/8.33  
% 16.19/8.33  %Background operators:
% 16.19/8.33  
% 16.19/8.33  
% 16.19/8.33  %Foreground operators:
% 16.19/8.33  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 16.19/8.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.19/8.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.19/8.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.19/8.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.19/8.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.19/8.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.19/8.33  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.19/8.33  tff('#skF_5', type, '#skF_5': $i).
% 16.19/8.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.19/8.33  tff('#skF_6', type, '#skF_6': $i).
% 16.19/8.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.19/8.33  tff('#skF_2', type, '#skF_2': $i).
% 16.19/8.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 16.19/8.33  tff('#skF_3', type, '#skF_3': $i).
% 16.19/8.33  tff('#skF_1', type, '#skF_1': $i).
% 16.19/8.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.19/8.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.19/8.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.19/8.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.19/8.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.19/8.33  tff('#skF_4', type, '#skF_4': $i).
% 16.19/8.33  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.19/8.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.19/8.33  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 16.19/8.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.19/8.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.19/8.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.19/8.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.19/8.33  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.19/8.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.19/8.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.19/8.33  
% 16.29/8.37  tff(f_238, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 16.29/8.37  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 16.29/8.37  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.29/8.37  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.29/8.37  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 16.29/8.37  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 16.29/8.37  tff(f_100, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 16.29/8.37  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 16.29/8.37  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 16.29/8.37  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 16.29/8.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 16.29/8.37  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 16.29/8.37  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 16.29/8.37  tff(f_196, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 16.29/8.37  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 16.29/8.37  tff(f_162, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 16.29/8.37  tff(c_82, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.29/8.37  tff(c_99, plain, (![C_236, A_237, B_238]: (v1_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 16.29/8.37  tff(c_112, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_99])).
% 16.29/8.37  tff(c_2214, plain, (![C_436, A_437, B_438]: (v4_relat_1(C_436, A_437) | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_437, B_438))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.29/8.37  tff(c_2256, plain, (![A_442]: (v4_relat_1(k1_xboole_0, A_442))), inference(resolution, [status(thm)], [c_8, c_2214])).
% 16.29/8.37  tff(c_16, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.29/8.37  tff(c_2259, plain, (![A_442]: (k7_relat_1(k1_xboole_0, A_442)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2256, c_16])).
% 16.29/8.37  tff(c_2262, plain, (![A_442]: (k7_relat_1(k1_xboole_0, A_442)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2259])).
% 16.29/8.37  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_110, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_99])).
% 16.29/8.37  tff(c_80, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_2225, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_2214])).
% 16.29/8.37  tff(c_2374, plain, (![B_466, A_467]: (k1_relat_1(B_466)=A_467 | ~v1_partfun1(B_466, A_467) | ~v4_relat_1(B_466, A_467) | ~v1_relat_1(B_466))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.29/8.37  tff(c_2383, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2225, c_2374])).
% 16.29/8.37  tff(c_2392, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2383])).
% 16.29/8.37  tff(c_2785, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_2392])).
% 16.29/8.37  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_2939, plain, (![C_523, A_524, B_525]: (v1_partfun1(C_523, A_524) | ~v1_funct_2(C_523, A_524, B_525) | ~v1_funct_1(C_523) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_524, B_525))) | v1_xboole_0(B_525))), inference(cnfTransformation, [status(thm)], [f_100])).
% 16.29/8.37  tff(c_2942, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2939])).
% 16.29/8.37  tff(c_2952, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2942])).
% 16.29/8.37  tff(c_2954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2785, c_2952])).
% 16.29/8.37  tff(c_2955, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_2392])).
% 16.29/8.37  tff(c_22, plain, (![B_20, A_19]: (r1_xboole_0(k1_relat_1(B_20), A_19) | k7_relat_1(B_20, A_19)!=k1_xboole_0 | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 16.29/8.37  tff(c_2966, plain, (![A_19]: (r1_xboole_0('#skF_3', A_19) | k7_relat_1('#skF_5', A_19)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2955, c_22])).
% 16.29/8.37  tff(c_2980, plain, (![A_19]: (r1_xboole_0('#skF_3', A_19) | k7_relat_1('#skF_5', A_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2966])).
% 16.29/8.37  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_111, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_99])).
% 16.29/8.37  tff(c_2226, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_2214])).
% 16.29/8.37  tff(c_2380, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2226, c_2374])).
% 16.29/8.37  tff(c_2389, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2380])).
% 16.29/8.37  tff(c_2399, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2389])).
% 16.29/8.37  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_2724, plain, (![C_505, A_506, B_507]: (v1_partfun1(C_505, A_506) | ~v1_funct_2(C_505, A_506, B_507) | ~v1_funct_1(C_505) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(A_506, B_507))) | v1_xboole_0(B_507))), inference(cnfTransformation, [status(thm)], [f_100])).
% 16.29/8.37  tff(c_2730, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_2724])).
% 16.29/8.37  tff(c_2741, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2730])).
% 16.29/8.37  tff(c_2743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2399, c_2741])).
% 16.29/8.37  tff(c_2744, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_2389])).
% 16.29/8.37  tff(c_14, plain, (![A_12, B_14]: (k7_relat_1(A_12, B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, k1_relat_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.29/8.37  tff(c_2752, plain, (![B_14]: (k7_relat_1('#skF_6', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2744, c_14])).
% 16.29/8.37  tff(c_3192, plain, (![B_541]: (k7_relat_1('#skF_6', B_541)=k1_xboole_0 | ~r1_xboole_0(B_541, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2752])).
% 16.29/8.37  tff(c_3215, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2980, c_3192])).
% 16.29/8.37  tff(c_3260, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3215])).
% 16.29/8.37  tff(c_70, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_78, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | ~r1_subset_1(A_21, B_22) | v1_xboole_0(B_22) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 16.29/8.37  tff(c_20, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 16.29/8.37  tff(c_2960, plain, (![A_19]: (k7_relat_1('#skF_5', A_19)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_19) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2955, c_20])).
% 16.29/8.37  tff(c_3006, plain, (![A_529]: (k7_relat_1('#skF_5', A_529)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_529))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2960])).
% 16.29/8.37  tff(c_3010, plain, (![B_22]: (k7_relat_1('#skF_5', B_22)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_22) | v1_xboole_0(B_22) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_3006])).
% 16.29/8.37  tff(c_3302, plain, (![B_550]: (k7_relat_1('#skF_5', B_550)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_550) | v1_xboole_0(B_550))), inference(negUnitSimplification, [status(thm)], [c_78, c_3010])).
% 16.29/8.37  tff(c_3305, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3302])).
% 16.29/8.37  tff(c_3309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3260, c_3305])).
% 16.29/8.37  tff(c_3310, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3215])).
% 16.29/8.37  tff(c_2755, plain, (![A_19]: (r1_xboole_0('#skF_4', A_19) | k7_relat_1('#skF_6', A_19)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2744, c_22])).
% 16.29/8.37  tff(c_3125, plain, (![A_538]: (r1_xboole_0('#skF_4', A_538) | k7_relat_1('#skF_6', A_538)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2755])).
% 16.29/8.37  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.29/8.37  tff(c_3334, plain, (![A_551]: (k3_xboole_0('#skF_4', A_551)=k1_xboole_0 | k7_relat_1('#skF_6', A_551)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3125, c_2])).
% 16.29/8.37  tff(c_3341, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3310, c_3334])).
% 16.29/8.37  tff(c_18, plain, (![B_18, A_17]: (k3_xboole_0(k1_relat_1(B_18), A_17)=k1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.29/8.37  tff(c_2758, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_6', A_17))=k3_xboole_0('#skF_4', A_17) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2744, c_18])).
% 16.29/8.37  tff(c_2771, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_6', A_17))=k3_xboole_0('#skF_4', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2758])).
% 16.29/8.37  tff(c_3315, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3310, c_2771])).
% 16.29/8.37  tff(c_21701, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3341, c_3315])).
% 16.29/8.37  tff(c_21718, plain, (![A_19]: (r1_xboole_0(k1_xboole_0, A_19) | k7_relat_1(k1_xboole_0, A_19)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_21701, c_22])).
% 16.29/8.37  tff(c_21738, plain, (![A_1037]: (r1_xboole_0(k1_xboole_0, A_1037))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2262, c_21718])).
% 16.29/8.37  tff(c_2963, plain, (![B_14]: (k7_relat_1('#skF_5', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2955, c_14])).
% 16.29/8.37  tff(c_2978, plain, (![B_14]: (k7_relat_1('#skF_5', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2963])).
% 16.29/8.37  tff(c_21758, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_21738, c_2978])).
% 16.29/8.37  tff(c_2767, plain, (![B_14]: (k7_relat_1('#skF_6', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2752])).
% 16.29/8.37  tff(c_21757, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_21738, c_2767])).
% 16.29/8.37  tff(c_3311, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3215])).
% 16.29/8.37  tff(c_2969, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_5', A_17))=k3_xboole_0('#skF_3', A_17) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2955, c_18])).
% 16.29/8.37  tff(c_2982, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_5', A_17))=k3_xboole_0('#skF_3', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2969])).
% 16.29/8.37  tff(c_3322, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3311, c_2982])).
% 16.29/8.37  tff(c_21706, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_21701, c_3322])).
% 16.29/8.37  tff(c_2358, plain, (![A_463, B_464, C_465]: (k9_subset_1(A_463, B_464, C_465)=k3_xboole_0(B_464, C_465) | ~m1_subset_1(C_465, k1_zfmisc_1(A_463)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.29/8.37  tff(c_2371, plain, (![B_464]: (k9_subset_1('#skF_1', B_464, '#skF_4')=k3_xboole_0(B_464, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_2358])).
% 16.29/8.37  tff(c_21899, plain, (![C_1047, F_1045, B_1044, D_1046, A_1049, E_1048]: (v1_funct_1(k1_tmap_1(A_1049, B_1044, C_1047, D_1046, E_1048, F_1045)) | ~m1_subset_1(F_1045, k1_zfmisc_1(k2_zfmisc_1(D_1046, B_1044))) | ~v1_funct_2(F_1045, D_1046, B_1044) | ~v1_funct_1(F_1045) | ~m1_subset_1(E_1048, k1_zfmisc_1(k2_zfmisc_1(C_1047, B_1044))) | ~v1_funct_2(E_1048, C_1047, B_1044) | ~v1_funct_1(E_1048) | ~m1_subset_1(D_1046, k1_zfmisc_1(A_1049)) | v1_xboole_0(D_1046) | ~m1_subset_1(C_1047, k1_zfmisc_1(A_1049)) | v1_xboole_0(C_1047) | v1_xboole_0(B_1044) | v1_xboole_0(A_1049))), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.29/8.37  tff(c_21903, plain, (![A_1049, C_1047, E_1048]: (v1_funct_1(k1_tmap_1(A_1049, '#skF_2', C_1047, '#skF_4', E_1048, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1048, k1_zfmisc_1(k2_zfmisc_1(C_1047, '#skF_2'))) | ~v1_funct_2(E_1048, C_1047, '#skF_2') | ~v1_funct_1(E_1048) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1049)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1047, k1_zfmisc_1(A_1049)) | v1_xboole_0(C_1047) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1049))), inference(resolution, [status(thm)], [c_58, c_21899])).
% 16.29/8.37  tff(c_21913, plain, (![A_1049, C_1047, E_1048]: (v1_funct_1(k1_tmap_1(A_1049, '#skF_2', C_1047, '#skF_4', E_1048, '#skF_6')) | ~m1_subset_1(E_1048, k1_zfmisc_1(k2_zfmisc_1(C_1047, '#skF_2'))) | ~v1_funct_2(E_1048, C_1047, '#skF_2') | ~v1_funct_1(E_1048) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1049)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1047, k1_zfmisc_1(A_1049)) | v1_xboole_0(C_1047) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1049))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_21903])).
% 16.29/8.37  tff(c_22266, plain, (![A_1077, C_1078, E_1079]: (v1_funct_1(k1_tmap_1(A_1077, '#skF_2', C_1078, '#skF_4', E_1079, '#skF_6')) | ~m1_subset_1(E_1079, k1_zfmisc_1(k2_zfmisc_1(C_1078, '#skF_2'))) | ~v1_funct_2(E_1079, C_1078, '#skF_2') | ~v1_funct_1(E_1079) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1077)) | ~m1_subset_1(C_1078, k1_zfmisc_1(A_1077)) | v1_xboole_0(C_1078) | v1_xboole_0(A_1077))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_21913])).
% 16.29/8.37  tff(c_22271, plain, (![A_1077]: (v1_funct_1(k1_tmap_1(A_1077, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1077)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1077)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1077))), inference(resolution, [status(thm)], [c_64, c_22266])).
% 16.29/8.37  tff(c_22282, plain, (![A_1077]: (v1_funct_1(k1_tmap_1(A_1077, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1077)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1077)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1077))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_22271])).
% 16.29/8.37  tff(c_22702, plain, (![A_1106]: (v1_funct_1(k1_tmap_1(A_1106, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1106)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1106)) | v1_xboole_0(A_1106))), inference(negUnitSimplification, [status(thm)], [c_78, c_22282])).
% 16.29/8.37  tff(c_22705, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_22702])).
% 16.29/8.37  tff(c_22708, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22705])).
% 16.29/8.37  tff(c_22709, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_22708])).
% 16.29/8.37  tff(c_3072, plain, (![A_532, B_533, C_534, D_535]: (k2_partfun1(A_532, B_533, C_534, D_535)=k7_relat_1(C_534, D_535) | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(A_532, B_533))) | ~v1_funct_1(C_534))), inference(cnfTransformation, [status(thm)], [f_114])).
% 16.29/8.37  tff(c_3074, plain, (![D_535]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_535)=k7_relat_1('#skF_5', D_535) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_3072])).
% 16.29/8.37  tff(c_3082, plain, (![D_535]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_535)=k7_relat_1('#skF_5', D_535))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3074])).
% 16.29/8.37  tff(c_3076, plain, (![D_535]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_535)=k7_relat_1('#skF_6', D_535) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_3072])).
% 16.29/8.37  tff(c_3085, plain, (![D_535]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_535)=k7_relat_1('#skF_6', D_535))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3076])).
% 16.29/8.37  tff(c_52, plain, (![D_169, E_170, A_166, B_167, C_168, F_171]: (v1_funct_2(k1_tmap_1(A_166, B_167, C_168, D_169, E_170, F_171), k4_subset_1(A_166, C_168, D_169), B_167) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(D_169, B_167))) | ~v1_funct_2(F_171, D_169, B_167) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_168, B_167))) | ~v1_funct_2(E_170, C_168, B_167) | ~v1_funct_1(E_170) | ~m1_subset_1(D_169, k1_zfmisc_1(A_166)) | v1_xboole_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | v1_xboole_0(C_168) | v1_xboole_0(B_167) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.29/8.37  tff(c_50, plain, (![D_169, E_170, A_166, B_167, C_168, F_171]: (m1_subset_1(k1_tmap_1(A_166, B_167, C_168, D_169, E_170, F_171), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_166, C_168, D_169), B_167))) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(D_169, B_167))) | ~v1_funct_2(F_171, D_169, B_167) | ~v1_funct_1(F_171) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(C_168, B_167))) | ~v1_funct_2(E_170, C_168, B_167) | ~v1_funct_1(E_170) | ~m1_subset_1(D_169, k1_zfmisc_1(A_166)) | v1_xboole_0(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | v1_xboole_0(C_168) | v1_xboole_0(B_167) | v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.29/8.37  tff(c_22655, plain, (![E_1101, B_1104, D_1100, A_1099, C_1103, F_1102]: (k2_partfun1(k4_subset_1(A_1099, C_1103, D_1100), B_1104, k1_tmap_1(A_1099, B_1104, C_1103, D_1100, E_1101, F_1102), C_1103)=E_1101 | ~m1_subset_1(k1_tmap_1(A_1099, B_1104, C_1103, D_1100, E_1101, F_1102), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1099, C_1103, D_1100), B_1104))) | ~v1_funct_2(k1_tmap_1(A_1099, B_1104, C_1103, D_1100, E_1101, F_1102), k4_subset_1(A_1099, C_1103, D_1100), B_1104) | ~v1_funct_1(k1_tmap_1(A_1099, B_1104, C_1103, D_1100, E_1101, F_1102)) | k2_partfun1(D_1100, B_1104, F_1102, k9_subset_1(A_1099, C_1103, D_1100))!=k2_partfun1(C_1103, B_1104, E_1101, k9_subset_1(A_1099, C_1103, D_1100)) | ~m1_subset_1(F_1102, k1_zfmisc_1(k2_zfmisc_1(D_1100, B_1104))) | ~v1_funct_2(F_1102, D_1100, B_1104) | ~v1_funct_1(F_1102) | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(C_1103, B_1104))) | ~v1_funct_2(E_1101, C_1103, B_1104) | ~v1_funct_1(E_1101) | ~m1_subset_1(D_1100, k1_zfmisc_1(A_1099)) | v1_xboole_0(D_1100) | ~m1_subset_1(C_1103, k1_zfmisc_1(A_1099)) | v1_xboole_0(C_1103) | v1_xboole_0(B_1104) | v1_xboole_0(A_1099))), inference(cnfTransformation, [status(thm)], [f_162])).
% 16.29/8.37  tff(c_27839, plain, (![D_1289, E_1291, A_1292, B_1287, C_1290, F_1288]: (k2_partfun1(k4_subset_1(A_1292, C_1290, D_1289), B_1287, k1_tmap_1(A_1292, B_1287, C_1290, D_1289, E_1291, F_1288), C_1290)=E_1291 | ~v1_funct_2(k1_tmap_1(A_1292, B_1287, C_1290, D_1289, E_1291, F_1288), k4_subset_1(A_1292, C_1290, D_1289), B_1287) | ~v1_funct_1(k1_tmap_1(A_1292, B_1287, C_1290, D_1289, E_1291, F_1288)) | k2_partfun1(D_1289, B_1287, F_1288, k9_subset_1(A_1292, C_1290, D_1289))!=k2_partfun1(C_1290, B_1287, E_1291, k9_subset_1(A_1292, C_1290, D_1289)) | ~m1_subset_1(F_1288, k1_zfmisc_1(k2_zfmisc_1(D_1289, B_1287))) | ~v1_funct_2(F_1288, D_1289, B_1287) | ~v1_funct_1(F_1288) | ~m1_subset_1(E_1291, k1_zfmisc_1(k2_zfmisc_1(C_1290, B_1287))) | ~v1_funct_2(E_1291, C_1290, B_1287) | ~v1_funct_1(E_1291) | ~m1_subset_1(D_1289, k1_zfmisc_1(A_1292)) | v1_xboole_0(D_1289) | ~m1_subset_1(C_1290, k1_zfmisc_1(A_1292)) | v1_xboole_0(C_1290) | v1_xboole_0(B_1287) | v1_xboole_0(A_1292))), inference(resolution, [status(thm)], [c_50, c_22655])).
% 16.29/8.37  tff(c_32848, plain, (![A_1393, F_1389, B_1388, C_1391, D_1390, E_1392]: (k2_partfun1(k4_subset_1(A_1393, C_1391, D_1390), B_1388, k1_tmap_1(A_1393, B_1388, C_1391, D_1390, E_1392, F_1389), C_1391)=E_1392 | ~v1_funct_1(k1_tmap_1(A_1393, B_1388, C_1391, D_1390, E_1392, F_1389)) | k2_partfun1(D_1390, B_1388, F_1389, k9_subset_1(A_1393, C_1391, D_1390))!=k2_partfun1(C_1391, B_1388, E_1392, k9_subset_1(A_1393, C_1391, D_1390)) | ~m1_subset_1(F_1389, k1_zfmisc_1(k2_zfmisc_1(D_1390, B_1388))) | ~v1_funct_2(F_1389, D_1390, B_1388) | ~v1_funct_1(F_1389) | ~m1_subset_1(E_1392, k1_zfmisc_1(k2_zfmisc_1(C_1391, B_1388))) | ~v1_funct_2(E_1392, C_1391, B_1388) | ~v1_funct_1(E_1392) | ~m1_subset_1(D_1390, k1_zfmisc_1(A_1393)) | v1_xboole_0(D_1390) | ~m1_subset_1(C_1391, k1_zfmisc_1(A_1393)) | v1_xboole_0(C_1391) | v1_xboole_0(B_1388) | v1_xboole_0(A_1393))), inference(resolution, [status(thm)], [c_52, c_27839])).
% 16.29/8.37  tff(c_32854, plain, (![A_1393, C_1391, E_1392]: (k2_partfun1(k4_subset_1(A_1393, C_1391, '#skF_4'), '#skF_2', k1_tmap_1(A_1393, '#skF_2', C_1391, '#skF_4', E_1392, '#skF_6'), C_1391)=E_1392 | ~v1_funct_1(k1_tmap_1(A_1393, '#skF_2', C_1391, '#skF_4', E_1392, '#skF_6')) | k2_partfun1(C_1391, '#skF_2', E_1392, k9_subset_1(A_1393, C_1391, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1393, C_1391, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1392, k1_zfmisc_1(k2_zfmisc_1(C_1391, '#skF_2'))) | ~v1_funct_2(E_1392, C_1391, '#skF_2') | ~v1_funct_1(E_1392) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1393)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1391, k1_zfmisc_1(A_1393)) | v1_xboole_0(C_1391) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1393))), inference(resolution, [status(thm)], [c_58, c_32848])).
% 16.29/8.37  tff(c_32865, plain, (![A_1393, C_1391, E_1392]: (k2_partfun1(k4_subset_1(A_1393, C_1391, '#skF_4'), '#skF_2', k1_tmap_1(A_1393, '#skF_2', C_1391, '#skF_4', E_1392, '#skF_6'), C_1391)=E_1392 | ~v1_funct_1(k1_tmap_1(A_1393, '#skF_2', C_1391, '#skF_4', E_1392, '#skF_6')) | k2_partfun1(C_1391, '#skF_2', E_1392, k9_subset_1(A_1393, C_1391, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1393, C_1391, '#skF_4')) | ~m1_subset_1(E_1392, k1_zfmisc_1(k2_zfmisc_1(C_1391, '#skF_2'))) | ~v1_funct_2(E_1392, C_1391, '#skF_2') | ~v1_funct_1(E_1392) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1393)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1391, k1_zfmisc_1(A_1393)) | v1_xboole_0(C_1391) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1393))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3085, c_32854])).
% 16.29/8.37  tff(c_40184, plain, (![A_1519, C_1520, E_1521]: (k2_partfun1(k4_subset_1(A_1519, C_1520, '#skF_4'), '#skF_2', k1_tmap_1(A_1519, '#skF_2', C_1520, '#skF_4', E_1521, '#skF_6'), C_1520)=E_1521 | ~v1_funct_1(k1_tmap_1(A_1519, '#skF_2', C_1520, '#skF_4', E_1521, '#skF_6')) | k2_partfun1(C_1520, '#skF_2', E_1521, k9_subset_1(A_1519, C_1520, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1519, C_1520, '#skF_4')) | ~m1_subset_1(E_1521, k1_zfmisc_1(k2_zfmisc_1(C_1520, '#skF_2'))) | ~v1_funct_2(E_1521, C_1520, '#skF_2') | ~v1_funct_1(E_1521) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1519)) | ~m1_subset_1(C_1520, k1_zfmisc_1(A_1519)) | v1_xboole_0(C_1520) | v1_xboole_0(A_1519))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_32865])).
% 16.29/8.37  tff(c_40189, plain, (![A_1519]: (k2_partfun1(k4_subset_1(A_1519, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1519, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1519, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1519, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1519, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1519)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1519)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1519))), inference(resolution, [status(thm)], [c_64, c_40184])).
% 16.29/8.37  tff(c_40200, plain, (![A_1519]: (k2_partfun1(k4_subset_1(A_1519, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1519, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1519, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1519, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1519, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1519)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1519)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1519))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3082, c_40189])).
% 16.29/8.37  tff(c_49645, plain, (![A_1675]: (k2_partfun1(k4_subset_1(A_1675, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1675, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1675, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1675, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1675, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1675)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1675)) | v1_xboole_0(A_1675))), inference(negUnitSimplification, [status(thm)], [c_78, c_40200])).
% 16.29/8.37  tff(c_3344, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3341, c_3315])).
% 16.29/8.37  tff(c_3361, plain, (![A_19]: (r1_xboole_0(k1_xboole_0, A_19) | k7_relat_1(k1_xboole_0, A_19)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3344, c_22])).
% 16.29/8.37  tff(c_3390, plain, (![A_553]: (r1_xboole_0(k1_xboole_0, A_553))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2262, c_3361])).
% 16.29/8.37  tff(c_3409, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3390, c_2767])).
% 16.29/8.37  tff(c_3410, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_3390, c_2978])).
% 16.29/8.37  tff(c_3349, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3344, c_3322])).
% 16.29/8.37  tff(c_3470, plain, (![A_562, B_557, E_561, F_558, D_559, C_560]: (v1_funct_1(k1_tmap_1(A_562, B_557, C_560, D_559, E_561, F_558)) | ~m1_subset_1(F_558, k1_zfmisc_1(k2_zfmisc_1(D_559, B_557))) | ~v1_funct_2(F_558, D_559, B_557) | ~v1_funct_1(F_558) | ~m1_subset_1(E_561, k1_zfmisc_1(k2_zfmisc_1(C_560, B_557))) | ~v1_funct_2(E_561, C_560, B_557) | ~v1_funct_1(E_561) | ~m1_subset_1(D_559, k1_zfmisc_1(A_562)) | v1_xboole_0(D_559) | ~m1_subset_1(C_560, k1_zfmisc_1(A_562)) | v1_xboole_0(C_560) | v1_xboole_0(B_557) | v1_xboole_0(A_562))), inference(cnfTransformation, [status(thm)], [f_196])).
% 16.29/8.37  tff(c_3474, plain, (![A_562, C_560, E_561]: (v1_funct_1(k1_tmap_1(A_562, '#skF_2', C_560, '#skF_4', E_561, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_561, k1_zfmisc_1(k2_zfmisc_1(C_560, '#skF_2'))) | ~v1_funct_2(E_561, C_560, '#skF_2') | ~v1_funct_1(E_561) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_562)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_560, k1_zfmisc_1(A_562)) | v1_xboole_0(C_560) | v1_xboole_0('#skF_2') | v1_xboole_0(A_562))), inference(resolution, [status(thm)], [c_58, c_3470])).
% 16.29/8.37  tff(c_3484, plain, (![A_562, C_560, E_561]: (v1_funct_1(k1_tmap_1(A_562, '#skF_2', C_560, '#skF_4', E_561, '#skF_6')) | ~m1_subset_1(E_561, k1_zfmisc_1(k2_zfmisc_1(C_560, '#skF_2'))) | ~v1_funct_2(E_561, C_560, '#skF_2') | ~v1_funct_1(E_561) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_562)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_560, k1_zfmisc_1(A_562)) | v1_xboole_0(C_560) | v1_xboole_0('#skF_2') | v1_xboole_0(A_562))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3474])).
% 16.29/8.37  tff(c_4953, plain, (![A_642, C_643, E_644]: (v1_funct_1(k1_tmap_1(A_642, '#skF_2', C_643, '#skF_4', E_644, '#skF_6')) | ~m1_subset_1(E_644, k1_zfmisc_1(k2_zfmisc_1(C_643, '#skF_2'))) | ~v1_funct_2(E_644, C_643, '#skF_2') | ~v1_funct_1(E_644) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_642)) | ~m1_subset_1(C_643, k1_zfmisc_1(A_642)) | v1_xboole_0(C_643) | v1_xboole_0(A_642))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_3484])).
% 16.29/8.37  tff(c_4958, plain, (![A_642]: (v1_funct_1(k1_tmap_1(A_642, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_642)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_642)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_642))), inference(resolution, [status(thm)], [c_64, c_4953])).
% 16.29/8.37  tff(c_4969, plain, (![A_642]: (v1_funct_1(k1_tmap_1(A_642, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_642)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_642)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_642))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_4958])).
% 16.29/8.37  tff(c_5423, plain, (![A_662]: (v1_funct_1(k1_tmap_1(A_662, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_662)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_662)) | v1_xboole_0(A_662))), inference(negUnitSimplification, [status(thm)], [c_78, c_4969])).
% 16.29/8.37  tff(c_5426, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_5423])).
% 16.29/8.37  tff(c_5429, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5426])).
% 16.29/8.37  tff(c_5430, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_5429])).
% 16.29/8.37  tff(c_3949, plain, (![C_598, F_597, A_594, E_596, D_595, B_599]: (k2_partfun1(k4_subset_1(A_594, C_598, D_595), B_599, k1_tmap_1(A_594, B_599, C_598, D_595, E_596, F_597), D_595)=F_597 | ~m1_subset_1(k1_tmap_1(A_594, B_599, C_598, D_595, E_596, F_597), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_594, C_598, D_595), B_599))) | ~v1_funct_2(k1_tmap_1(A_594, B_599, C_598, D_595, E_596, F_597), k4_subset_1(A_594, C_598, D_595), B_599) | ~v1_funct_1(k1_tmap_1(A_594, B_599, C_598, D_595, E_596, F_597)) | k2_partfun1(D_595, B_599, F_597, k9_subset_1(A_594, C_598, D_595))!=k2_partfun1(C_598, B_599, E_596, k9_subset_1(A_594, C_598, D_595)) | ~m1_subset_1(F_597, k1_zfmisc_1(k2_zfmisc_1(D_595, B_599))) | ~v1_funct_2(F_597, D_595, B_599) | ~v1_funct_1(F_597) | ~m1_subset_1(E_596, k1_zfmisc_1(k2_zfmisc_1(C_598, B_599))) | ~v1_funct_2(E_596, C_598, B_599) | ~v1_funct_1(E_596) | ~m1_subset_1(D_595, k1_zfmisc_1(A_594)) | v1_xboole_0(D_595) | ~m1_subset_1(C_598, k1_zfmisc_1(A_594)) | v1_xboole_0(C_598) | v1_xboole_0(B_599) | v1_xboole_0(A_594))), inference(cnfTransformation, [status(thm)], [f_162])).
% 16.29/8.37  tff(c_8898, plain, (![F_795, C_797, A_799, D_796, B_794, E_798]: (k2_partfun1(k4_subset_1(A_799, C_797, D_796), B_794, k1_tmap_1(A_799, B_794, C_797, D_796, E_798, F_795), D_796)=F_795 | ~v1_funct_2(k1_tmap_1(A_799, B_794, C_797, D_796, E_798, F_795), k4_subset_1(A_799, C_797, D_796), B_794) | ~v1_funct_1(k1_tmap_1(A_799, B_794, C_797, D_796, E_798, F_795)) | k2_partfun1(D_796, B_794, F_795, k9_subset_1(A_799, C_797, D_796))!=k2_partfun1(C_797, B_794, E_798, k9_subset_1(A_799, C_797, D_796)) | ~m1_subset_1(F_795, k1_zfmisc_1(k2_zfmisc_1(D_796, B_794))) | ~v1_funct_2(F_795, D_796, B_794) | ~v1_funct_1(F_795) | ~m1_subset_1(E_798, k1_zfmisc_1(k2_zfmisc_1(C_797, B_794))) | ~v1_funct_2(E_798, C_797, B_794) | ~v1_funct_1(E_798) | ~m1_subset_1(D_796, k1_zfmisc_1(A_799)) | v1_xboole_0(D_796) | ~m1_subset_1(C_797, k1_zfmisc_1(A_799)) | v1_xboole_0(C_797) | v1_xboole_0(B_794) | v1_xboole_0(A_799))), inference(resolution, [status(thm)], [c_50, c_3949])).
% 16.29/8.37  tff(c_13460, plain, (![E_891, D_889, B_887, A_892, C_890, F_888]: (k2_partfun1(k4_subset_1(A_892, C_890, D_889), B_887, k1_tmap_1(A_892, B_887, C_890, D_889, E_891, F_888), D_889)=F_888 | ~v1_funct_1(k1_tmap_1(A_892, B_887, C_890, D_889, E_891, F_888)) | k2_partfun1(D_889, B_887, F_888, k9_subset_1(A_892, C_890, D_889))!=k2_partfun1(C_890, B_887, E_891, k9_subset_1(A_892, C_890, D_889)) | ~m1_subset_1(F_888, k1_zfmisc_1(k2_zfmisc_1(D_889, B_887))) | ~v1_funct_2(F_888, D_889, B_887) | ~v1_funct_1(F_888) | ~m1_subset_1(E_891, k1_zfmisc_1(k2_zfmisc_1(C_890, B_887))) | ~v1_funct_2(E_891, C_890, B_887) | ~v1_funct_1(E_891) | ~m1_subset_1(D_889, k1_zfmisc_1(A_892)) | v1_xboole_0(D_889) | ~m1_subset_1(C_890, k1_zfmisc_1(A_892)) | v1_xboole_0(C_890) | v1_xboole_0(B_887) | v1_xboole_0(A_892))), inference(resolution, [status(thm)], [c_52, c_8898])).
% 16.29/8.37  tff(c_13466, plain, (![A_892, C_890, E_891]: (k2_partfun1(k4_subset_1(A_892, C_890, '#skF_4'), '#skF_2', k1_tmap_1(A_892, '#skF_2', C_890, '#skF_4', E_891, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_892, '#skF_2', C_890, '#skF_4', E_891, '#skF_6')) | k2_partfun1(C_890, '#skF_2', E_891, k9_subset_1(A_892, C_890, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_892, C_890, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_891, k1_zfmisc_1(k2_zfmisc_1(C_890, '#skF_2'))) | ~v1_funct_2(E_891, C_890, '#skF_2') | ~v1_funct_1(E_891) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_892)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_890, k1_zfmisc_1(A_892)) | v1_xboole_0(C_890) | v1_xboole_0('#skF_2') | v1_xboole_0(A_892))), inference(resolution, [status(thm)], [c_58, c_13460])).
% 16.29/8.37  tff(c_13477, plain, (![A_892, C_890, E_891]: (k2_partfun1(k4_subset_1(A_892, C_890, '#skF_4'), '#skF_2', k1_tmap_1(A_892, '#skF_2', C_890, '#skF_4', E_891, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_892, '#skF_2', C_890, '#skF_4', E_891, '#skF_6')) | k2_partfun1(C_890, '#skF_2', E_891, k9_subset_1(A_892, C_890, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_892, C_890, '#skF_4')) | ~m1_subset_1(E_891, k1_zfmisc_1(k2_zfmisc_1(C_890, '#skF_2'))) | ~v1_funct_2(E_891, C_890, '#skF_2') | ~v1_funct_1(E_891) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_892)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_890, k1_zfmisc_1(A_892)) | v1_xboole_0(C_890) | v1_xboole_0('#skF_2') | v1_xboole_0(A_892))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3085, c_13466])).
% 16.29/8.37  tff(c_20113, plain, (![A_1022, C_1023, E_1024]: (k2_partfun1(k4_subset_1(A_1022, C_1023, '#skF_4'), '#skF_2', k1_tmap_1(A_1022, '#skF_2', C_1023, '#skF_4', E_1024, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1022, '#skF_2', C_1023, '#skF_4', E_1024, '#skF_6')) | k2_partfun1(C_1023, '#skF_2', E_1024, k9_subset_1(A_1022, C_1023, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1022, C_1023, '#skF_4')) | ~m1_subset_1(E_1024, k1_zfmisc_1(k2_zfmisc_1(C_1023, '#skF_2'))) | ~v1_funct_2(E_1024, C_1023, '#skF_2') | ~v1_funct_1(E_1024) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1022)) | ~m1_subset_1(C_1023, k1_zfmisc_1(A_1022)) | v1_xboole_0(C_1023) | v1_xboole_0(A_1022))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_13477])).
% 16.29/8.37  tff(c_20118, plain, (![A_1022]: (k2_partfun1(k4_subset_1(A_1022, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1022, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1022, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1022, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1022, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1022)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1022)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1022))), inference(resolution, [status(thm)], [c_64, c_20113])).
% 16.29/8.37  tff(c_20129, plain, (![A_1022]: (k2_partfun1(k4_subset_1(A_1022, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1022, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1022, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1022, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1022, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1022)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1022)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1022))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3082, c_20118])).
% 16.29/8.37  tff(c_21671, plain, (![A_1036]: (k2_partfun1(k4_subset_1(A_1036, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1036, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1036, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1036, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1036, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1036)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1036)) | v1_xboole_0(A_1036))), inference(negUnitSimplification, [status(thm)], [c_78, c_20129])).
% 16.29/8.37  tff(c_115, plain, (![C_241, A_242, B_243]: (v4_relat_1(C_241, A_242) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.29/8.37  tff(c_155, plain, (![A_247]: (v4_relat_1(k1_xboole_0, A_247))), inference(resolution, [status(thm)], [c_8, c_115])).
% 16.29/8.37  tff(c_158, plain, (![A_247]: (k7_relat_1(k1_xboole_0, A_247)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_155, c_16])).
% 16.29/8.37  tff(c_161, plain, (![A_247]: (k7_relat_1(k1_xboole_0, A_247)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_158])).
% 16.29/8.37  tff(c_127, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_115])).
% 16.29/8.37  tff(c_332, plain, (![B_281, A_282]: (k1_relat_1(B_281)=A_282 | ~v1_partfun1(B_281, A_282) | ~v4_relat_1(B_281, A_282) | ~v1_relat_1(B_281))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.29/8.37  tff(c_338, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_127, c_332])).
% 16.29/8.37  tff(c_347, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_338])).
% 16.29/8.37  tff(c_357, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_347])).
% 16.29/8.37  tff(c_671, plain, (![C_314, A_315, B_316]: (v1_partfun1(C_314, A_315) | ~v1_funct_2(C_314, A_315, B_316) | ~v1_funct_1(C_314) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))) | v1_xboole_0(B_316))), inference(cnfTransformation, [status(thm)], [f_100])).
% 16.29/8.37  tff(c_677, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_671])).
% 16.29/8.37  tff(c_688, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_677])).
% 16.29/8.37  tff(c_690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_357, c_688])).
% 16.29/8.37  tff(c_691, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_347])).
% 16.29/8.37  tff(c_702, plain, (![A_19]: (r1_xboole_0('#skF_4', A_19) | k7_relat_1('#skF_6', A_19)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_691, c_22])).
% 16.29/8.37  tff(c_716, plain, (![A_19]: (r1_xboole_0('#skF_4', A_19) | k7_relat_1('#skF_6', A_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_702])).
% 16.29/8.37  tff(c_126, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_115])).
% 16.29/8.37  tff(c_341, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_126, c_332])).
% 16.29/8.37  tff(c_350, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_341])).
% 16.29/8.37  tff(c_723, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_350])).
% 16.29/8.37  tff(c_872, plain, (![C_329, A_330, B_331]: (v1_partfun1(C_329, A_330) | ~v1_funct_2(C_329, A_330, B_331) | ~v1_funct_1(C_329) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | v1_xboole_0(B_331))), inference(cnfTransformation, [status(thm)], [f_100])).
% 16.29/8.37  tff(c_875, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_872])).
% 16.29/8.37  tff(c_885, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_875])).
% 16.29/8.37  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_723, c_885])).
% 16.29/8.37  tff(c_888, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_350])).
% 16.29/8.37  tff(c_902, plain, (![B_14]: (k7_relat_1('#skF_5', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_888, c_14])).
% 16.29/8.37  tff(c_936, plain, (![B_333]: (k7_relat_1('#skF_5', B_333)=k1_xboole_0 | ~r1_xboole_0(B_333, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_902])).
% 16.29/8.37  tff(c_953, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_716, c_936])).
% 16.29/8.37  tff(c_1193, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_953])).
% 16.29/8.37  tff(c_899, plain, (![A_19]: (r1_xboole_0('#skF_3', A_19) | k7_relat_1('#skF_5', A_19)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_888, c_22])).
% 16.29/8.37  tff(c_913, plain, (![A_19]: (r1_xboole_0('#skF_3', A_19) | k7_relat_1('#skF_5', A_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_899])).
% 16.29/8.37  tff(c_705, plain, (![B_14]: (k7_relat_1('#skF_6', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_691, c_14])).
% 16.29/8.37  tff(c_1098, plain, (![B_344]: (k7_relat_1('#skF_6', B_344)=k1_xboole_0 | ~r1_xboole_0(B_344, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_705])).
% 16.29/8.37  tff(c_1119, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_913, c_1098])).
% 16.29/8.37  tff(c_1194, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1193, c_1119])).
% 16.29/8.37  tff(c_893, plain, (![A_19]: (k7_relat_1('#skF_5', A_19)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_19) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_888, c_20])).
% 16.29/8.37  tff(c_1014, plain, (![A_336]: (k7_relat_1('#skF_5', A_336)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_336))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_893])).
% 16.29/8.37  tff(c_1021, plain, (![B_22]: (k7_relat_1('#skF_5', B_22)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_22) | v1_xboole_0(B_22) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_1014])).
% 16.29/8.37  tff(c_1241, plain, (![B_359]: (k7_relat_1('#skF_5', B_359)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_359) | v1_xboole_0(B_359))), inference(negUnitSimplification, [status(thm)], [c_78, c_1021])).
% 16.29/8.37  tff(c_1244, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_1241])).
% 16.29/8.37  tff(c_1248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1194, c_1244])).
% 16.29/8.37  tff(c_1250, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_953])).
% 16.29/8.37  tff(c_920, plain, (![A_332]: (r1_xboole_0('#skF_4', A_332) | k7_relat_1('#skF_6', A_332)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_702])).
% 16.29/8.37  tff(c_1300, plain, (![A_366]: (k3_xboole_0('#skF_4', A_366)=k1_xboole_0 | k7_relat_1('#skF_6', A_366)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_920, c_2])).
% 16.29/8.37  tff(c_1307, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1250, c_1300])).
% 16.29/8.37  tff(c_708, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_6', A_17))=k3_xboole_0('#skF_4', A_17) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_691, c_18])).
% 16.29/8.37  tff(c_720, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_6', A_17))=k3_xboole_0('#skF_4', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_708])).
% 16.29/8.37  tff(c_1269, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1250, c_720])).
% 16.29/8.37  tff(c_1309, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1307, c_1269])).
% 16.29/8.37  tff(c_1326, plain, (![A_19]: (r1_xboole_0(k1_xboole_0, A_19) | k7_relat_1(k1_xboole_0, A_19)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1309, c_22])).
% 16.29/8.37  tff(c_1354, plain, (![A_368]: (r1_xboole_0(k1_xboole_0, A_368))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_161, c_1326])).
% 16.29/8.37  tff(c_718, plain, (![B_14]: (k7_relat_1('#skF_6', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_705])).
% 16.29/8.37  tff(c_1373, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1354, c_718])).
% 16.29/8.37  tff(c_915, plain, (![B_14]: (k7_relat_1('#skF_5', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_902])).
% 16.29/8.37  tff(c_1374, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1354, c_915])).
% 16.29/8.37  tff(c_1249, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_953])).
% 16.29/8.37  tff(c_905, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_5', A_17))=k3_xboole_0('#skF_3', A_17) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_888, c_18])).
% 16.29/8.37  tff(c_917, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_5', A_17))=k3_xboole_0('#skF_3', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_905])).
% 16.29/8.37  tff(c_1257, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1249, c_917])).
% 16.29/8.37  tff(c_1314, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1309, c_1257])).
% 16.29/8.37  tff(c_1031, plain, (![A_337, B_338, C_339, D_340]: (k2_partfun1(A_337, B_338, C_339, D_340)=k7_relat_1(C_339, D_340) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))) | ~v1_funct_1(C_339))), inference(cnfTransformation, [status(thm)], [f_114])).
% 16.29/8.37  tff(c_1033, plain, (![D_340]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_340)=k7_relat_1('#skF_5', D_340) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1031])).
% 16.29/8.37  tff(c_1041, plain, (![D_340]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_340)=k7_relat_1('#skF_5', D_340))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1033])).
% 16.29/8.37  tff(c_1035, plain, (![D_340]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_340)=k7_relat_1('#skF_6', D_340) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_1031])).
% 16.29/8.37  tff(c_1044, plain, (![D_340]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_340)=k7_relat_1('#skF_6', D_340))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1035])).
% 16.29/8.37  tff(c_270, plain, (![A_272, B_273, C_274]: (k9_subset_1(A_272, B_273, C_274)=k3_xboole_0(B_273, C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(A_272)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.29/8.37  tff(c_283, plain, (![B_273]: (k9_subset_1('#skF_1', B_273, '#skF_4')=k3_xboole_0(B_273, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_270])).
% 16.29/8.37  tff(c_56, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 16.29/8.37  tff(c_113, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 16.29/8.37  tff(c_286, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_283, c_113])).
% 16.29/8.37  tff(c_1127, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_286])).
% 16.29/8.37  tff(c_2195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1373, c_1374, c_1314, c_1314, c_1041, c_1127])).
% 16.29/8.37  tff(c_2196, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_56])).
% 16.29/8.37  tff(c_3343, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_2196])).
% 16.29/8.37  tff(c_21682, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_21671, c_3343])).
% 16.29/8.37  tff(c_21696, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_3409, c_3410, c_3349, c_3349, c_2371, c_2371, c_5430, c_21682])).
% 16.29/8.37  tff(c_21698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_21696])).
% 16.29/8.37  tff(c_21699, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_2196])).
% 16.29/8.37  tff(c_49654, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_49645, c_21699])).
% 16.29/8.37  tff(c_49665, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_21758, c_21757, c_21706, c_21706, c_2371, c_2371, c_22709, c_49654])).
% 16.29/8.37  tff(c_49667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_49665])).
% 16.29/8.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.29/8.37  
% 16.29/8.37  Inference rules
% 16.29/8.37  ----------------------
% 16.29/8.37  #Ref     : 0
% 16.29/8.37  #Sup     : 10843
% 16.29/8.37  #Fact    : 0
% 16.29/8.37  #Define  : 0
% 16.29/8.37  #Split   : 42
% 16.29/8.37  #Chain   : 0
% 16.29/8.37  #Close   : 0
% 16.29/8.37  
% 16.29/8.37  Ordering : KBO
% 16.29/8.37  
% 16.29/8.37  Simplification rules
% 16.29/8.37  ----------------------
% 16.29/8.37  #Subsume      : 1815
% 16.29/8.37  #Demod        : 12764
% 16.29/8.37  #Tautology    : 5483
% 16.29/8.37  #SimpNegUnit  : 442
% 16.29/8.37  #BackRed      : 25
% 16.29/8.37  
% 16.29/8.37  #Partial instantiations: 0
% 16.29/8.37  #Strategies tried      : 1
% 16.29/8.37  
% 16.29/8.37  Timing (in seconds)
% 16.29/8.37  ----------------------
% 16.29/8.37  Preprocessing        : 0.41
% 16.29/8.37  Parsing              : 0.21
% 16.29/8.37  CNF conversion       : 0.06
% 16.29/8.37  Main loop            : 7.15
% 16.29/8.37  Inferencing          : 1.61
% 16.29/8.37  Reduction            : 2.74
% 16.29/8.37  Demodulation         : 2.18
% 16.29/8.37  BG Simplification    : 0.15
% 16.29/8.37  Subsumption          : 2.33
% 16.29/8.37  Abstraction          : 0.21
% 16.29/8.37  MUC search           : 0.00
% 16.29/8.37  Cooper               : 0.00
% 16.29/8.37  Total                : 7.64
% 16.29/8.37  Index Insertion      : 0.00
% 16.29/8.37  Index Deletion       : 0.00
% 16.29/8.37  Index Matching       : 0.00
% 16.29/8.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
