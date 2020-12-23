%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:12 EST 2020

% Result     : Theorem 23.91s
% Output     : CNFRefutation 24.36s
% Verified   : 
% Statistics : Number of formulae       :  460 (3525 expanded)
%              Number of leaves         :   54 (1172 expanded)
%              Depth                    :   17
%              Number of atoms          : 1187 (13367 expanded)
%              Number of equality atoms :  384 (3061 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_259,negated_conjecture,(
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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_217,axiom,(
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

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_183,axiom,(
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

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_58327,plain,(
    ! [C_2657,A_2658,B_2659] :
      ( v1_relat_1(C_2657)
      | ~ m1_subset_1(C_2657,k1_zfmisc_1(k2_zfmisc_1(A_2658,B_2659))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58338,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_58327])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_58346,plain,(
    ! [C_2660,A_2661,B_2662] :
      ( v4_relat_1(C_2660,A_2661)
      | ~ m1_subset_1(C_2660,k1_zfmisc_1(k2_zfmisc_1(A_2661,B_2662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_58357,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_58346])).

tff(c_78888,plain,(
    ! [B_3409,A_3410] :
      ( k1_relat_1(B_3409) = A_3410
      | ~ v1_partfun1(B_3409,A_3410)
      | ~ v4_relat_1(B_3409,A_3410)
      | ~ v1_relat_1(B_3409) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_78897,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58357,c_78888])).

tff(c_78906,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_78897])).

tff(c_79833,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_78906])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_80277,plain,(
    ! [C_3512,A_3513,B_3514] :
      ( v1_partfun1(C_3512,A_3513)
      | ~ v1_funct_2(C_3512,A_3513,B_3514)
      | ~ v1_funct_1(C_3512)
      | ~ m1_subset_1(C_3512,k1_zfmisc_1(k2_zfmisc_1(A_3513,B_3514)))
      | v1_xboole_0(B_3514) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_80280,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_80277])).

tff(c_80290,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_80280])).

tff(c_80292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_79833,c_80290])).

tff(c_80293,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_78906])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_xboole_0(k1_relat_1(B_17),A_16)
      | k9_relat_1(B_17,A_16) != k1_xboole_0
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80310,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_4',A_16)
      | k9_relat_1('#skF_6',A_16) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80293,c_20])).

tff(c_80502,plain,(
    ! [A_3528] :
      ( r1_xboole_0('#skF_4',A_3528)
      | k9_relat_1('#skF_6',A_3528) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_80310])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10385,plain,(
    ! [A_989] :
      ( k9_relat_1(A_989,k1_relat_1(A_989)) = k2_relat_1(A_989)
      | ~ v1_relat_1(A_989) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10394,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10385])).

tff(c_10397,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10394])).

tff(c_10398,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10397])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10403,plain,(
    ! [C_990,A_991,B_992] :
      ( v1_relat_1(C_990)
      | ~ m1_subset_1(C_990,k1_zfmisc_1(k2_zfmisc_1(A_991,B_992))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10413,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_10403])).

tff(c_10419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10398,c_10413])).

tff(c_10421,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10397])).

tff(c_58397,plain,(
    ! [A_2677,B_2678] :
      ( k7_relat_1(A_2677,B_2678) = k1_xboole_0
      | ~ r1_xboole_0(B_2678,k1_relat_1(A_2677))
      | ~ v1_relat_1(A_2677) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58404,plain,(
    ! [B_2678] :
      ( k7_relat_1(k1_xboole_0,B_2678) = k1_xboole_0
      | ~ r1_xboole_0(B_2678,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_58397])).

tff(c_58407,plain,(
    ! [B_2678] :
      ( k7_relat_1(k1_xboole_0,B_2678) = k1_xboole_0
      | ~ r1_xboole_0(B_2678,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10421,c_58404])).

tff(c_80534,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80502,c_58407])).

tff(c_83093,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_80534])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k9_relat_1(B_17,A_16) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80298,plain,(
    ! [A_16] :
      ( k9_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_16)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80293,c_18])).

tff(c_80419,plain,(
    ! [A_3518] :
      ( k9_relat_1('#skF_6',A_3518) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_3518) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_80298])).

tff(c_81014,plain,(
    ! [B_3567] :
      ( k9_relat_1('#skF_6',B_3567) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_3567) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_80419])).

tff(c_80328,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_4',A_16)
      | k9_relat_1('#skF_6',A_16) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_80310])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_58339,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_58327])).

tff(c_58358,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_58346])).

tff(c_78894,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58358,c_78888])).

tff(c_78903,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_78894])).

tff(c_78913,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_78903])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_78,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_79771,plain,(
    ! [C_3478,A_3479,B_3480] :
      ( v1_partfun1(C_3478,A_3479)
      | ~ v1_funct_2(C_3478,A_3479,B_3480)
      | ~ v1_funct_1(C_3478)
      | ~ m1_subset_1(C_3478,k1_zfmisc_1(k2_zfmisc_1(A_3479,B_3480)))
      | v1_xboole_0(B_3480) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_79777,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_79771])).

tff(c_79788,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_79777])).

tff(c_79790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_78913,c_79788])).

tff(c_79791,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_78903])).

tff(c_24,plain,(
    ! [A_23,B_25] :
      ( k7_relat_1(A_23,B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,k1_relat_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_79811,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_5',B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79791,c_24])).

tff(c_80550,plain,(
    ! [B_3530] :
      ( k7_relat_1('#skF_5',B_3530) = k1_xboole_0
      | ~ r1_xboole_0(B_3530,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_79811])).

tff(c_80583,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80328,c_80550])).

tff(c_80836,plain,(
    k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_80583])).

tff(c_81039,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_81014,c_80836])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_34,plain,(
    ! [B_29,A_28] :
      ( r1_xboole_0(k1_relat_1(B_29),A_28)
      | k7_relat_1(B_29,A_28) != k1_xboole_0
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_79805,plain,(
    ! [A_28] :
      ( r1_xboole_0('#skF_3',A_28)
      | k7_relat_1('#skF_5',A_28) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79791,c_34])).

tff(c_80668,plain,(
    ! [A_3535] :
      ( r1_xboole_0('#skF_3',A_3535)
      | k7_relat_1('#skF_5',A_3535) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_79805])).

tff(c_80313,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_6',B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80293,c_24])).

tff(c_80330,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_6',B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_80313])).

tff(c_80700,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80668,c_80330])).

tff(c_80885,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_80700])).

tff(c_82,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | ~ r1_subset_1(A_30,B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [B_29,A_28] :
      ( k7_relat_1(B_29,A_28) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_79802,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_28)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79791,c_32])).

tff(c_80489,plain,(
    ! [A_3527] :
      ( k7_relat_1('#skF_5',A_3527) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_3527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_79802])).

tff(c_80493,plain,(
    ! [B_31] :
      ( k7_relat_1('#skF_5',B_31) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_80489])).

tff(c_80942,plain,(
    ! [B_3560] :
      ( k7_relat_1('#skF_5',B_3560) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_3560)
      | v1_xboole_0(B_3560) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80493])).

tff(c_80945,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_80942])).

tff(c_80949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80885,c_80945])).

tff(c_80950,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80700])).

tff(c_80307,plain,(
    ! [A_28] :
      ( r1_xboole_0('#skF_4',A_28)
      | k7_relat_1('#skF_6',A_28) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80293,c_34])).

tff(c_80376,plain,(
    ! [A_3516] :
      ( r1_xboole_0('#skF_4',A_3516)
      | k7_relat_1('#skF_6',A_3516) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_80307])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81272,plain,(
    ! [A_3595] :
      ( k3_xboole_0('#skF_4',A_3595) = k1_xboole_0
      | k7_relat_1('#skF_6',A_3595) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80376,c_2])).

tff(c_81278,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_80950,c_81272])).

tff(c_81283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81039,c_81278])).

tff(c_81284,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80583])).

tff(c_80706,plain,(
    ! [A_3535] :
      ( k3_xboole_0('#skF_3',A_3535) = k1_xboole_0
      | k7_relat_1('#skF_5',A_3535) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80668,c_2])).

tff(c_81312,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_81284,c_80706])).

tff(c_10420,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10397])).

tff(c_80343,plain,(
    ! [B_3515] :
      ( k7_relat_1('#skF_6',B_3515) = k1_xboole_0
      | ~ r1_xboole_0(B_3515,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_80313])).

tff(c_83498,plain,(
    ! [A_3761] :
      ( k7_relat_1('#skF_6',A_3761) = k1_xboole_0
      | k3_xboole_0(A_3761,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_80343])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_27,A_26)),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_83522,plain,(
    ! [A_3761] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_3761)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0(A_3761,'#skF_4') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83498,c_30])).

tff(c_83543,plain,(
    ! [A_3761] :
      ( r1_tarski(k1_xboole_0,A_3761)
      | k3_xboole_0(A_3761,'#skF_4') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_28,c_83522])).

tff(c_83159,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81284,c_80700])).

tff(c_22,plain,(
    ! [A_18,C_22,B_21] :
      ( k9_relat_1(k7_relat_1(A_18,C_22),B_21) = k9_relat_1(A_18,B_21)
      | ~ r1_tarski(B_21,C_22)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_83166,plain,(
    ! [B_21] :
      ( k9_relat_1(k1_xboole_0,B_21) = k9_relat_1('#skF_6',B_21)
      | ~ r1_tarski(B_21,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83159,c_22])).

tff(c_83837,plain,(
    ! [B_3777] :
      ( k9_relat_1(k1_xboole_0,B_3777) = k9_relat_1('#skF_6',B_3777)
      | ~ r1_tarski(B_3777,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_83166])).

tff(c_83845,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83543,c_83837])).

tff(c_83874,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81312,c_10420,c_83845])).

tff(c_83876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83093,c_83874])).

tff(c_83877,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80534])).

tff(c_78611,plain,(
    ! [B_3391,A_3392] :
      ( r1_xboole_0(k1_relat_1(B_3391),A_3392)
      | k7_relat_1(B_3391,A_3392) != k1_xboole_0
      | ~ v1_relat_1(B_3391) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_78625,plain,(
    ! [A_3392] :
      ( r1_xboole_0(k1_xboole_0,A_3392)
      | k7_relat_1(k1_xboole_0,A_3392) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_78611])).

tff(c_78631,plain,(
    ! [A_3393] :
      ( r1_xboole_0(k1_xboole_0,A_3393)
      | k7_relat_1(k1_xboole_0,A_3393) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10421,c_78625])).

tff(c_78647,plain,(
    ! [A_3393] :
      ( k3_xboole_0(k1_xboole_0,A_3393) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_3393) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_78631,c_2])).

tff(c_83907,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_83877,c_78647])).

tff(c_78803,plain,(
    ! [B_3405,A_3406] :
      ( k9_relat_1(B_3405,A_3406) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_3405),A_3406)
      | ~ v1_relat_1(B_3405) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_78820,plain,(
    ! [A_3406] :
      ( k9_relat_1(k1_xboole_0,A_3406) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_3406)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_78803])).

tff(c_78827,plain,(
    ! [A_3407] :
      ( k9_relat_1(k1_xboole_0,A_3407) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_3407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10421,c_78820])).

tff(c_78846,plain,(
    ! [B_2] :
      ( k9_relat_1(k1_xboole_0,B_2) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_78827])).

tff(c_58408,plain,(
    ! [B_2679,A_2680] :
      ( r1_xboole_0(k1_relat_1(B_2679),A_2680)
      | k9_relat_1(B_2679,A_2680) != k1_xboole_0
      | ~ v1_relat_1(B_2679) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_58418,plain,(
    ! [A_2680] :
      ( r1_xboole_0(k1_xboole_0,A_2680)
      | k9_relat_1(k1_xboole_0,A_2680) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_58408])).

tff(c_58422,plain,(
    ! [A_2680] :
      ( r1_xboole_0(k1_xboole_0,A_2680)
      | k9_relat_1(k1_xboole_0,A_2680) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10421,c_58418])).

tff(c_80373,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58422,c_80343])).

tff(c_84236,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_80373])).

tff(c_84239,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78846,c_84236])).

tff(c_84246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83907,c_84239])).

tff(c_84247,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80373])).

tff(c_80436,plain,(
    ! [A_3519,B_3520,C_3521] :
      ( k9_subset_1(A_3519,B_3520,C_3521) = k3_xboole_0(B_3520,C_3521)
      | ~ m1_subset_1(C_3521,k1_zfmisc_1(A_3519)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80449,plain,(
    ! [B_3520] : k9_subset_1('#skF_1',B_3520,'#skF_4') = k3_xboole_0(B_3520,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_80436])).

tff(c_78630,plain,(
    ! [A_3392] :
      ( r1_xboole_0(k1_xboole_0,A_3392)
      | k7_relat_1(k1_xboole_0,A_3392) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10421,c_78625])).

tff(c_78842,plain,(
    ! [A_3392] :
      ( k9_relat_1(k1_xboole_0,A_3392) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_3392) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_78630,c_78827])).

tff(c_80590,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58422,c_80550])).

tff(c_81384,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_80590])).

tff(c_81392,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78842,c_81384])).

tff(c_79808,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_3',A_16)
      | k9_relat_1('#skF_5',A_16) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79791,c_20])).

tff(c_80593,plain,(
    ! [A_3531] :
      ( r1_xboole_0('#skF_3',A_3531)
      | k9_relat_1('#skF_5',A_3531) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_79808])).

tff(c_80630,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80593,c_58407])).

tff(c_82194,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_81392,c_80630])).

tff(c_82237,plain,(
    ! [B_3674] :
      ( k7_relat_1('#skF_5',B_3674) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_3674) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_80489])).

tff(c_82258,plain,(
    ! [B_3674] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_3674)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0('#skF_3',B_3674) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82237,c_30])).

tff(c_82278,plain,(
    ! [B_3674] :
      ( r1_tarski(k1_xboole_0,B_3674)
      | k3_xboole_0('#skF_3',B_3674) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_28,c_82258])).

tff(c_81303,plain,(
    ! [B_21] :
      ( k9_relat_1(k1_xboole_0,B_21) = k9_relat_1('#skF_5',B_21)
      | ~ r1_tarski(B_21,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81284,c_22])).

tff(c_82886,plain,(
    ! [B_3715] :
      ( k9_relat_1(k1_xboole_0,B_3715) = k9_relat_1('#skF_5',B_3715)
      | ~ r1_tarski(B_3715,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_81303])).

tff(c_82898,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82278,c_82886])).

tff(c_82926,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81312,c_10420,c_82898])).

tff(c_82928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82194,c_82926])).

tff(c_82929,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80590])).

tff(c_83043,plain,(
    ! [B_3722,A_3719,F_3720,D_3718,C_3717,E_3721] :
      ( v1_funct_1(k1_tmap_1(A_3719,B_3722,C_3717,D_3718,E_3721,F_3720))
      | ~ m1_subset_1(F_3720,k1_zfmisc_1(k2_zfmisc_1(D_3718,B_3722)))
      | ~ v1_funct_2(F_3720,D_3718,B_3722)
      | ~ v1_funct_1(F_3720)
      | ~ m1_subset_1(E_3721,k1_zfmisc_1(k2_zfmisc_1(C_3717,B_3722)))
      | ~ v1_funct_2(E_3721,C_3717,B_3722)
      | ~ v1_funct_1(E_3721)
      | ~ m1_subset_1(D_3718,k1_zfmisc_1(A_3719))
      | v1_xboole_0(D_3718)
      | ~ m1_subset_1(C_3717,k1_zfmisc_1(A_3719))
      | v1_xboole_0(C_3717)
      | v1_xboole_0(B_3722)
      | v1_xboole_0(A_3719) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_83045,plain,(
    ! [A_3719,C_3717,E_3721] :
      ( v1_funct_1(k1_tmap_1(A_3719,'#skF_2',C_3717,'#skF_4',E_3721,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3721,k1_zfmisc_1(k2_zfmisc_1(C_3717,'#skF_2')))
      | ~ v1_funct_2(E_3721,C_3717,'#skF_2')
      | ~ v1_funct_1(E_3721)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3719))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3717,k1_zfmisc_1(A_3719))
      | v1_xboole_0(C_3717)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3719) ) ),
    inference(resolution,[status(thm)],[c_70,c_83043])).

tff(c_83053,plain,(
    ! [A_3719,C_3717,E_3721] :
      ( v1_funct_1(k1_tmap_1(A_3719,'#skF_2',C_3717,'#skF_4',E_3721,'#skF_6'))
      | ~ m1_subset_1(E_3721,k1_zfmisc_1(k2_zfmisc_1(C_3717,'#skF_2')))
      | ~ v1_funct_2(E_3721,C_3717,'#skF_2')
      | ~ v1_funct_1(E_3721)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3719))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3717,k1_zfmisc_1(A_3719))
      | v1_xboole_0(C_3717)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3719) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_83045])).

tff(c_84712,plain,(
    ! [A_3829,C_3830,E_3831] :
      ( v1_funct_1(k1_tmap_1(A_3829,'#skF_2',C_3830,'#skF_4',E_3831,'#skF_6'))
      | ~ m1_subset_1(E_3831,k1_zfmisc_1(k2_zfmisc_1(C_3830,'#skF_2')))
      | ~ v1_funct_2(E_3831,C_3830,'#skF_2')
      | ~ v1_funct_1(E_3831)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3829))
      | ~ m1_subset_1(C_3830,k1_zfmisc_1(A_3829))
      | v1_xboole_0(C_3830)
      | v1_xboole_0(A_3829) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_83053])).

tff(c_84719,plain,(
    ! [A_3829] :
      ( v1_funct_1(k1_tmap_1(A_3829,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3829))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3829))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3829) ) ),
    inference(resolution,[status(thm)],[c_76,c_84712])).

tff(c_84732,plain,(
    ! [A_3829] :
      ( v1_funct_1(k1_tmap_1(A_3829,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3829))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3829))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_84719])).

tff(c_85149,plain,(
    ! [A_3848] :
      ( v1_funct_1(k1_tmap_1(A_3848,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3848))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3848))
      | v1_xboole_0(A_3848) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84732])).

tff(c_85152,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_85149])).

tff(c_85155,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_85152])).

tff(c_85156,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_85155])).

tff(c_80796,plain,(
    ! [A_3540,B_3541,C_3542,D_3543] :
      ( k2_partfun1(A_3540,B_3541,C_3542,D_3543) = k7_relat_1(C_3542,D_3543)
      | ~ m1_subset_1(C_3542,k1_zfmisc_1(k2_zfmisc_1(A_3540,B_3541)))
      | ~ v1_funct_1(C_3542) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_80800,plain,(
    ! [D_3543] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_3543) = k7_relat_1('#skF_5',D_3543)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_80796])).

tff(c_80809,plain,(
    ! [D_3543] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_3543) = k7_relat_1('#skF_5',D_3543) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80800])).

tff(c_80798,plain,(
    ! [D_3543] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_3543) = k7_relat_1('#skF_6',D_3543)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_80796])).

tff(c_80806,plain,(
    ! [D_3543] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_3543) = k7_relat_1('#skF_6',D_3543) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_80798])).

tff(c_64,plain,(
    ! [C_177,F_180,A_175,D_178,B_176,E_179] :
      ( v1_funct_2(k1_tmap_1(A_175,B_176,C_177,D_178,E_179,F_180),k4_subset_1(A_175,C_177,D_178),B_176)
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(D_178,B_176)))
      | ~ v1_funct_2(F_180,D_178,B_176)
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(C_177,B_176)))
      | ~ v1_funct_2(E_179,C_177,B_176)
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(A_175))
      | v1_xboole_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(A_175))
      | v1_xboole_0(C_177)
      | v1_xboole_0(B_176)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_62,plain,(
    ! [C_177,F_180,A_175,D_178,B_176,E_179] :
      ( m1_subset_1(k1_tmap_1(A_175,B_176,C_177,D_178,E_179,F_180),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_175,C_177,D_178),B_176)))
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(D_178,B_176)))
      | ~ v1_funct_2(F_180,D_178,B_176)
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(C_177,B_176)))
      | ~ v1_funct_2(E_179,C_177,B_176)
      | ~ v1_funct_1(E_179)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(A_175))
      | v1_xboole_0(D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(A_175))
      | v1_xboole_0(C_177)
      | v1_xboole_0(B_176)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_84177,plain,(
    ! [E_3797,B_3802,C_3799,A_3798,D_3800,F_3801] :
      ( k2_partfun1(k4_subset_1(A_3798,C_3799,D_3800),B_3802,k1_tmap_1(A_3798,B_3802,C_3799,D_3800,E_3797,F_3801),C_3799) = E_3797
      | ~ m1_subset_1(k1_tmap_1(A_3798,B_3802,C_3799,D_3800,E_3797,F_3801),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3798,C_3799,D_3800),B_3802)))
      | ~ v1_funct_2(k1_tmap_1(A_3798,B_3802,C_3799,D_3800,E_3797,F_3801),k4_subset_1(A_3798,C_3799,D_3800),B_3802)
      | ~ v1_funct_1(k1_tmap_1(A_3798,B_3802,C_3799,D_3800,E_3797,F_3801))
      | k2_partfun1(D_3800,B_3802,F_3801,k9_subset_1(A_3798,C_3799,D_3800)) != k2_partfun1(C_3799,B_3802,E_3797,k9_subset_1(A_3798,C_3799,D_3800))
      | ~ m1_subset_1(F_3801,k1_zfmisc_1(k2_zfmisc_1(D_3800,B_3802)))
      | ~ v1_funct_2(F_3801,D_3800,B_3802)
      | ~ v1_funct_1(F_3801)
      | ~ m1_subset_1(E_3797,k1_zfmisc_1(k2_zfmisc_1(C_3799,B_3802)))
      | ~ v1_funct_2(E_3797,C_3799,B_3802)
      | ~ v1_funct_1(E_3797)
      | ~ m1_subset_1(D_3800,k1_zfmisc_1(A_3798))
      | v1_xboole_0(D_3800)
      | ~ m1_subset_1(C_3799,k1_zfmisc_1(A_3798))
      | v1_xboole_0(C_3799)
      | v1_xboole_0(B_3802)
      | v1_xboole_0(A_3798) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_104479,plain,(
    ! [F_4336,E_4337,D_4334,B_4338,A_4335,C_4333] :
      ( k2_partfun1(k4_subset_1(A_4335,C_4333,D_4334),B_4338,k1_tmap_1(A_4335,B_4338,C_4333,D_4334,E_4337,F_4336),C_4333) = E_4337
      | ~ v1_funct_2(k1_tmap_1(A_4335,B_4338,C_4333,D_4334,E_4337,F_4336),k4_subset_1(A_4335,C_4333,D_4334),B_4338)
      | ~ v1_funct_1(k1_tmap_1(A_4335,B_4338,C_4333,D_4334,E_4337,F_4336))
      | k2_partfun1(D_4334,B_4338,F_4336,k9_subset_1(A_4335,C_4333,D_4334)) != k2_partfun1(C_4333,B_4338,E_4337,k9_subset_1(A_4335,C_4333,D_4334))
      | ~ m1_subset_1(F_4336,k1_zfmisc_1(k2_zfmisc_1(D_4334,B_4338)))
      | ~ v1_funct_2(F_4336,D_4334,B_4338)
      | ~ v1_funct_1(F_4336)
      | ~ m1_subset_1(E_4337,k1_zfmisc_1(k2_zfmisc_1(C_4333,B_4338)))
      | ~ v1_funct_2(E_4337,C_4333,B_4338)
      | ~ v1_funct_1(E_4337)
      | ~ m1_subset_1(D_4334,k1_zfmisc_1(A_4335))
      | v1_xboole_0(D_4334)
      | ~ m1_subset_1(C_4333,k1_zfmisc_1(A_4335))
      | v1_xboole_0(C_4333)
      | v1_xboole_0(B_4338)
      | v1_xboole_0(A_4335) ) ),
    inference(resolution,[status(thm)],[c_62,c_84177])).

tff(c_111186,plain,(
    ! [A_4452,D_4451,F_4453,E_4454,B_4455,C_4450] :
      ( k2_partfun1(k4_subset_1(A_4452,C_4450,D_4451),B_4455,k1_tmap_1(A_4452,B_4455,C_4450,D_4451,E_4454,F_4453),C_4450) = E_4454
      | ~ v1_funct_1(k1_tmap_1(A_4452,B_4455,C_4450,D_4451,E_4454,F_4453))
      | k2_partfun1(D_4451,B_4455,F_4453,k9_subset_1(A_4452,C_4450,D_4451)) != k2_partfun1(C_4450,B_4455,E_4454,k9_subset_1(A_4452,C_4450,D_4451))
      | ~ m1_subset_1(F_4453,k1_zfmisc_1(k2_zfmisc_1(D_4451,B_4455)))
      | ~ v1_funct_2(F_4453,D_4451,B_4455)
      | ~ v1_funct_1(F_4453)
      | ~ m1_subset_1(E_4454,k1_zfmisc_1(k2_zfmisc_1(C_4450,B_4455)))
      | ~ v1_funct_2(E_4454,C_4450,B_4455)
      | ~ v1_funct_1(E_4454)
      | ~ m1_subset_1(D_4451,k1_zfmisc_1(A_4452))
      | v1_xboole_0(D_4451)
      | ~ m1_subset_1(C_4450,k1_zfmisc_1(A_4452))
      | v1_xboole_0(C_4450)
      | v1_xboole_0(B_4455)
      | v1_xboole_0(A_4452) ) ),
    inference(resolution,[status(thm)],[c_64,c_104479])).

tff(c_111190,plain,(
    ! [A_4452,C_4450,E_4454] :
      ( k2_partfun1(k4_subset_1(A_4452,C_4450,'#skF_4'),'#skF_2',k1_tmap_1(A_4452,'#skF_2',C_4450,'#skF_4',E_4454,'#skF_6'),C_4450) = E_4454
      | ~ v1_funct_1(k1_tmap_1(A_4452,'#skF_2',C_4450,'#skF_4',E_4454,'#skF_6'))
      | k2_partfun1(C_4450,'#skF_2',E_4454,k9_subset_1(A_4452,C_4450,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_4452,C_4450,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_4454,k1_zfmisc_1(k2_zfmisc_1(C_4450,'#skF_2')))
      | ~ v1_funct_2(E_4454,C_4450,'#skF_2')
      | ~ v1_funct_1(E_4454)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4452))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_4450,k1_zfmisc_1(A_4452))
      | v1_xboole_0(C_4450)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_4452) ) ),
    inference(resolution,[status(thm)],[c_70,c_111186])).

tff(c_111199,plain,(
    ! [A_4452,C_4450,E_4454] :
      ( k2_partfun1(k4_subset_1(A_4452,C_4450,'#skF_4'),'#skF_2',k1_tmap_1(A_4452,'#skF_2',C_4450,'#skF_4',E_4454,'#skF_6'),C_4450) = E_4454
      | ~ v1_funct_1(k1_tmap_1(A_4452,'#skF_2',C_4450,'#skF_4',E_4454,'#skF_6'))
      | k2_partfun1(C_4450,'#skF_2',E_4454,k9_subset_1(A_4452,C_4450,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4452,C_4450,'#skF_4'))
      | ~ m1_subset_1(E_4454,k1_zfmisc_1(k2_zfmisc_1(C_4450,'#skF_2')))
      | ~ v1_funct_2(E_4454,C_4450,'#skF_2')
      | ~ v1_funct_1(E_4454)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4452))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_4450,k1_zfmisc_1(A_4452))
      | v1_xboole_0(C_4450)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_4452) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_80806,c_111190])).

tff(c_116923,plain,(
    ! [A_4532,C_4533,E_4534] :
      ( k2_partfun1(k4_subset_1(A_4532,C_4533,'#skF_4'),'#skF_2',k1_tmap_1(A_4532,'#skF_2',C_4533,'#skF_4',E_4534,'#skF_6'),C_4533) = E_4534
      | ~ v1_funct_1(k1_tmap_1(A_4532,'#skF_2',C_4533,'#skF_4',E_4534,'#skF_6'))
      | k2_partfun1(C_4533,'#skF_2',E_4534,k9_subset_1(A_4532,C_4533,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4532,C_4533,'#skF_4'))
      | ~ m1_subset_1(E_4534,k1_zfmisc_1(k2_zfmisc_1(C_4533,'#skF_2')))
      | ~ v1_funct_2(E_4534,C_4533,'#skF_2')
      | ~ v1_funct_1(E_4534)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4532))
      | ~ m1_subset_1(C_4533,k1_zfmisc_1(A_4532))
      | v1_xboole_0(C_4533)
      | v1_xboole_0(A_4532) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_111199])).

tff(c_116930,plain,(
    ! [A_4532] :
      ( k2_partfun1(k4_subset_1(A_4532,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4532,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4532,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_4532,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4532,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4532))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4532))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4532) ) ),
    inference(resolution,[status(thm)],[c_76,c_116923])).

tff(c_116943,plain,(
    ! [A_4532] :
      ( k2_partfun1(k4_subset_1(A_4532,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4532,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4532,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4532,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4532,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4532))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4532))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4532) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_80809,c_116930])).

tff(c_117294,plain,(
    ! [A_4540] :
      ( k2_partfun1(k4_subset_1(A_4540,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4540,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4540,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4540,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4540,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4540))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4540))
      | v1_xboole_0(A_4540) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_116943])).

tff(c_58833,plain,(
    ! [B_2706,A_2707] :
      ( k1_relat_1(B_2706) = A_2707
      | ~ v1_partfun1(B_2706,A_2707)
      | ~ v4_relat_1(B_2706,A_2707)
      | ~ v1_relat_1(B_2706) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58842,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58357,c_58833])).

tff(c_58851,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_58842])).

tff(c_59657,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58851])).

tff(c_60027,plain,(
    ! [C_2805,A_2806,B_2807] :
      ( v1_partfun1(C_2805,A_2806)
      | ~ v1_funct_2(C_2805,A_2806,B_2807)
      | ~ v1_funct_1(C_2805)
      | ~ m1_subset_1(C_2805,k1_zfmisc_1(k2_zfmisc_1(A_2806,B_2807)))
      | v1_xboole_0(B_2807) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_60030,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_60027])).

tff(c_60040,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_60030])).

tff(c_60042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_59657,c_60040])).

tff(c_60043,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58851])).

tff(c_60060,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_4',A_16)
      | k9_relat_1('#skF_6',A_16) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60043,c_20])).

tff(c_60126,plain,(
    ! [A_2809] :
      ( r1_xboole_0('#skF_4',A_2809)
      | k9_relat_1('#skF_6',A_2809) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_60060])).

tff(c_60149,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60126,c_58407])).

tff(c_61675,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60149])).

tff(c_58839,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58358,c_58833])).

tff(c_58848,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_58839])).

tff(c_58858,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58848])).

tff(c_59595,plain,(
    ! [C_2775,A_2776,B_2777] :
      ( v1_partfun1(C_2775,A_2776)
      | ~ v1_funct_2(C_2775,A_2776,B_2777)
      | ~ v1_funct_1(C_2775)
      | ~ m1_subset_1(C_2775,k1_zfmisc_1(k2_zfmisc_1(A_2776,B_2777)))
      | v1_xboole_0(B_2777) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_59601,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_59595])).

tff(c_59612,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_59601])).

tff(c_59614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_58858,c_59612])).

tff(c_59615,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_58848])).

tff(c_59620,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_28)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59615,c_32])).

tff(c_60317,plain,(
    ! [A_2823] :
      ( k7_relat_1('#skF_5',A_2823) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_2823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_59620])).

tff(c_60324,plain,(
    ! [B_31] :
      ( k7_relat_1('#skF_5',B_31) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_60317])).

tff(c_61490,plain,(
    ! [B_2923] :
      ( k7_relat_1('#skF_5',B_2923) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_2923)
      | v1_xboole_0(B_2923) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_60324])).

tff(c_61496,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_61490])).

tff(c_61500,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_61496])).

tff(c_59623,plain,(
    ! [A_28] :
      ( r1_xboole_0('#skF_3',A_28)
      | k7_relat_1('#skF_5',A_28) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59615,c_34])).

tff(c_60334,plain,(
    ! [A_2824] :
      ( r1_xboole_0('#skF_3',A_2824)
      | k7_relat_1('#skF_5',A_2824) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_59623])).

tff(c_59629,plain,(
    ! [A_16] :
      ( k9_relat_1('#skF_5',A_16) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_16)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59615,c_18])).

tff(c_59648,plain,(
    ! [A_16] :
      ( k9_relat_1('#skF_5',A_16) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_59629])).

tff(c_60360,plain,(
    ! [A_2824] :
      ( k9_relat_1('#skF_5',A_2824) = k1_xboole_0
      | k7_relat_1('#skF_5',A_2824) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60334,c_59648])).

tff(c_59632,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_3',A_16)
      | k9_relat_1('#skF_5',A_16) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59615,c_20])).

tff(c_59650,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_3',A_16)
      | k9_relat_1('#skF_5',A_16) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_59632])).

tff(c_60063,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_6',B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60043,c_24])).

tff(c_60403,plain,(
    ! [B_2828] :
      ( k7_relat_1('#skF_6',B_2828) = k1_xboole_0
      | ~ r1_xboole_0(B_2828,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_60063])).

tff(c_60445,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59650,c_60403])).

tff(c_61560,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60445])).

tff(c_61563,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60360,c_61560])).

tff(c_61570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61500,c_61563])).

tff(c_61571,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60445])).

tff(c_60051,plain,(
    ! [A_28] :
      ( r1_xboole_0('#skF_4',A_28)
      | k7_relat_1('#skF_6',A_28) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60043,c_34])).

tff(c_60169,plain,(
    ! [A_2811] :
      ( r1_xboole_0('#skF_4',A_2811)
      | k7_relat_1('#skF_6',A_2811) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_60051])).

tff(c_61793,plain,(
    ! [A_2949] :
      ( k3_xboole_0('#skF_4',A_2949) = k1_xboole_0
      | k7_relat_1('#skF_6',A_2949) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60169,c_2])).

tff(c_61797,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61571,c_61793])).

tff(c_60048,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_6',A_28) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_28)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60043,c_32])).

tff(c_60296,plain,(
    ! [A_2822] :
      ( k7_relat_1('#skF_6',A_2822) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_2822) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_60048])).

tff(c_61848,plain,(
    ! [B_2957] :
      ( k7_relat_1('#skF_6',B_2957) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_2957) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_60296])).

tff(c_61866,plain,(
    ! [B_2957] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_2957)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0('#skF_4',B_2957) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61848,c_30])).

tff(c_61885,plain,(
    ! [B_2957] :
      ( r1_tarski(k1_xboole_0,B_2957)
      | k3_xboole_0('#skF_4',B_2957) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_28,c_61866])).

tff(c_61590,plain,(
    ! [B_21] :
      ( k9_relat_1(k1_xboole_0,B_21) = k9_relat_1('#skF_6',B_21)
      | ~ r1_tarski(B_21,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61571,c_22])).

tff(c_62147,plain,(
    ! [B_2972] :
      ( k9_relat_1(k1_xboole_0,B_2972) = k9_relat_1('#skF_6',B_2972)
      | ~ r1_tarski(B_2972,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58338,c_61590])).

tff(c_62151,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61885,c_62147])).

tff(c_62181,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61797,c_10420,c_62151])).

tff(c_62183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61675,c_62181])).

tff(c_62184,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60149])).

tff(c_58603,plain,(
    ! [B_2693,A_2694] :
      ( r1_xboole_0(k1_relat_1(B_2693),A_2694)
      | k7_relat_1(B_2693,A_2694) != k1_xboole_0
      | ~ v1_relat_1(B_2693) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58620,plain,(
    ! [A_2694] :
      ( r1_xboole_0(k1_xboole_0,A_2694)
      | k7_relat_1(k1_xboole_0,A_2694) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_58603])).

tff(c_58626,plain,(
    ! [A_2694] :
      ( r1_xboole_0(k1_xboole_0,A_2694)
      | k7_relat_1(k1_xboole_0,A_2694) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10421,c_58620])).

tff(c_60449,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58626,c_60403])).

tff(c_62275,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62184,c_60449])).

tff(c_61572,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60445])).

tff(c_60252,plain,(
    ! [A_2820] :
      ( r1_xboole_0('#skF_3',A_2820)
      | k9_relat_1('#skF_5',A_2820) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_59632])).

tff(c_61631,plain,(
    ! [A_2931] :
      ( k3_xboole_0('#skF_3',A_2931) = k1_xboole_0
      | k9_relat_1('#skF_5',A_2931) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60252,c_2])).

tff(c_61651,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61572,c_61631])).

tff(c_60199,plain,(
    ! [A_2812,B_2813,C_2814] :
      ( k9_subset_1(A_2812,B_2813,C_2814) = k3_xboole_0(B_2813,C_2814)
      | ~ m1_subset_1(C_2814,k1_zfmisc_1(A_2812)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60212,plain,(
    ! [B_2813] : k9_subset_1('#skF_1',B_2813,'#skF_4') = k3_xboole_0(B_2813,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_60199])).

tff(c_60276,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60252,c_58407])).

tff(c_60592,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60276])).

tff(c_60597,plain,(
    ! [B_2845] :
      ( k7_relat_1('#skF_5',B_2845) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_2845)
      | v1_xboole_0(B_2845) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_60324])).

tff(c_60600,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_60597])).

tff(c_60603,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_60600])).

tff(c_59644,plain,(
    ! [A_28] :
      ( r1_xboole_0('#skF_3',A_28)
      | k7_relat_1('#skF_5',A_28) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_59623])).

tff(c_60444,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59644,c_60403])).

tff(c_60785,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60603,c_60444])).

tff(c_61065,plain,(
    ! [A_2889] :
      ( k3_xboole_0('#skF_4',A_2889) = k1_xboole_0
      | k7_relat_1('#skF_6',A_2889) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60169,c_2])).

tff(c_61072,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60785,c_61065])).

tff(c_59635,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_5',B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59615,c_24])).

tff(c_60093,plain,(
    ! [B_2808] :
      ( k7_relat_1('#skF_5',B_2808) = k1_xboole_0
      | ~ r1_xboole_0(B_2808,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_59635])).

tff(c_61080,plain,(
    ! [A_2895] :
      ( k7_relat_1('#skF_5',A_2895) = k1_xboole_0
      | k3_xboole_0(A_2895,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_60093])).

tff(c_61101,plain,(
    ! [A_2895] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_2895)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0(A_2895,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61080,c_30])).

tff(c_61121,plain,(
    ! [A_2895] :
      ( r1_tarski(k1_xboole_0,A_2895)
      | k3_xboole_0(A_2895,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_28,c_61101])).

tff(c_60610,plain,(
    ! [B_21] :
      ( k9_relat_1(k1_xboole_0,B_21) = k9_relat_1('#skF_5',B_21)
      | ~ r1_tarski(B_21,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60603,c_22])).

tff(c_61266,plain,(
    ! [B_2907] :
      ( k9_relat_1(k1_xboole_0,B_2907) = k9_relat_1('#skF_5',B_2907)
      | ~ r1_tarski(B_2907,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58339,c_60610])).

tff(c_61274,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61121,c_61266])).

tff(c_61303,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61072,c_10420,c_61274])).

tff(c_61305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60592,c_61303])).

tff(c_61307,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60276])).

tff(c_60329,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_5',A_16) = k1_xboole_0
      | k9_relat_1('#skF_5',A_16) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_59650,c_60317])).

tff(c_61372,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61307,c_60329])).

tff(c_61308,plain,(
    ! [C_2908,E_2912,B_2913,F_2911,A_2910,D_2909] :
      ( v1_funct_1(k1_tmap_1(A_2910,B_2913,C_2908,D_2909,E_2912,F_2911))
      | ~ m1_subset_1(F_2911,k1_zfmisc_1(k2_zfmisc_1(D_2909,B_2913)))
      | ~ v1_funct_2(F_2911,D_2909,B_2913)
      | ~ v1_funct_1(F_2911)
      | ~ m1_subset_1(E_2912,k1_zfmisc_1(k2_zfmisc_1(C_2908,B_2913)))
      | ~ v1_funct_2(E_2912,C_2908,B_2913)
      | ~ v1_funct_1(E_2912)
      | ~ m1_subset_1(D_2909,k1_zfmisc_1(A_2910))
      | v1_xboole_0(D_2909)
      | ~ m1_subset_1(C_2908,k1_zfmisc_1(A_2910))
      | v1_xboole_0(C_2908)
      | v1_xboole_0(B_2913)
      | v1_xboole_0(A_2910) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_61310,plain,(
    ! [A_2910,C_2908,E_2912] :
      ( v1_funct_1(k1_tmap_1(A_2910,'#skF_2',C_2908,'#skF_4',E_2912,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2912,k1_zfmisc_1(k2_zfmisc_1(C_2908,'#skF_2')))
      | ~ v1_funct_2(E_2912,C_2908,'#skF_2')
      | ~ v1_funct_1(E_2912)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2910))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2908,k1_zfmisc_1(A_2910))
      | v1_xboole_0(C_2908)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2910) ) ),
    inference(resolution,[status(thm)],[c_70,c_61308])).

tff(c_61318,plain,(
    ! [A_2910,C_2908,E_2912] :
      ( v1_funct_1(k1_tmap_1(A_2910,'#skF_2',C_2908,'#skF_4',E_2912,'#skF_6'))
      | ~ m1_subset_1(E_2912,k1_zfmisc_1(k2_zfmisc_1(C_2908,'#skF_2')))
      | ~ v1_funct_2(E_2912,C_2908,'#skF_2')
      | ~ v1_funct_1(E_2912)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2910))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2908,k1_zfmisc_1(A_2910))
      | v1_xboole_0(C_2908)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2910) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_61310])).

tff(c_62977,plain,(
    ! [A_3013,C_3014,E_3015] :
      ( v1_funct_1(k1_tmap_1(A_3013,'#skF_2',C_3014,'#skF_4',E_3015,'#skF_6'))
      | ~ m1_subset_1(E_3015,k1_zfmisc_1(k2_zfmisc_1(C_3014,'#skF_2')))
      | ~ v1_funct_2(E_3015,C_3014,'#skF_2')
      | ~ v1_funct_1(E_3015)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3013))
      | ~ m1_subset_1(C_3014,k1_zfmisc_1(A_3013))
      | v1_xboole_0(C_3014)
      | v1_xboole_0(A_3013) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_61318])).

tff(c_62984,plain,(
    ! [A_3013] :
      ( v1_funct_1(k1_tmap_1(A_3013,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3013))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3013))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3013) ) ),
    inference(resolution,[status(thm)],[c_76,c_62977])).

tff(c_62997,plain,(
    ! [A_3013] :
      ( v1_funct_1(k1_tmap_1(A_3013,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3013))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3013))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3013) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_62984])).

tff(c_63490,plain,(
    ! [A_3037] :
      ( v1_funct_1(k1_tmap_1(A_3037,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3037))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3037))
      | v1_xboole_0(A_3037) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_62997])).

tff(c_63493,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_63490])).

tff(c_63496,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_63493])).

tff(c_63497,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_63496])).

tff(c_60504,plain,(
    ! [A_2832,B_2833,C_2834,D_2835] :
      ( k2_partfun1(A_2832,B_2833,C_2834,D_2835) = k7_relat_1(C_2834,D_2835)
      | ~ m1_subset_1(C_2834,k1_zfmisc_1(k2_zfmisc_1(A_2832,B_2833)))
      | ~ v1_funct_1(C_2834) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60508,plain,(
    ! [D_2835] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_2835) = k7_relat_1('#skF_5',D_2835)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_60504])).

tff(c_60517,plain,(
    ! [D_2835] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_2835) = k7_relat_1('#skF_5',D_2835) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_60508])).

tff(c_60506,plain,(
    ! [D_2835] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_2835) = k7_relat_1('#skF_6',D_2835)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_60504])).

tff(c_60514,plain,(
    ! [D_2835] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_2835) = k7_relat_1('#skF_6',D_2835) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60506])).

tff(c_61663,plain,(
    ! [C_2934,B_2937,E_2932,A_2933,D_2935,F_2936] :
      ( k2_partfun1(k4_subset_1(A_2933,C_2934,D_2935),B_2937,k1_tmap_1(A_2933,B_2937,C_2934,D_2935,E_2932,F_2936),D_2935) = F_2936
      | ~ m1_subset_1(k1_tmap_1(A_2933,B_2937,C_2934,D_2935,E_2932,F_2936),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2933,C_2934,D_2935),B_2937)))
      | ~ v1_funct_2(k1_tmap_1(A_2933,B_2937,C_2934,D_2935,E_2932,F_2936),k4_subset_1(A_2933,C_2934,D_2935),B_2937)
      | ~ v1_funct_1(k1_tmap_1(A_2933,B_2937,C_2934,D_2935,E_2932,F_2936))
      | k2_partfun1(D_2935,B_2937,F_2936,k9_subset_1(A_2933,C_2934,D_2935)) != k2_partfun1(C_2934,B_2937,E_2932,k9_subset_1(A_2933,C_2934,D_2935))
      | ~ m1_subset_1(F_2936,k1_zfmisc_1(k2_zfmisc_1(D_2935,B_2937)))
      | ~ v1_funct_2(F_2936,D_2935,B_2937)
      | ~ v1_funct_1(F_2936)
      | ~ m1_subset_1(E_2932,k1_zfmisc_1(k2_zfmisc_1(C_2934,B_2937)))
      | ~ v1_funct_2(E_2932,C_2934,B_2937)
      | ~ v1_funct_1(E_2932)
      | ~ m1_subset_1(D_2935,k1_zfmisc_1(A_2933))
      | v1_xboole_0(D_2935)
      | ~ m1_subset_1(C_2934,k1_zfmisc_1(A_2933))
      | v1_xboole_0(C_2934)
      | v1_xboole_0(B_2937)
      | v1_xboole_0(A_2933) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_70550,plain,(
    ! [B_3247,F_3245,C_3242,E_3246,A_3244,D_3243] :
      ( k2_partfun1(k4_subset_1(A_3244,C_3242,D_3243),B_3247,k1_tmap_1(A_3244,B_3247,C_3242,D_3243,E_3246,F_3245),D_3243) = F_3245
      | ~ v1_funct_2(k1_tmap_1(A_3244,B_3247,C_3242,D_3243,E_3246,F_3245),k4_subset_1(A_3244,C_3242,D_3243),B_3247)
      | ~ v1_funct_1(k1_tmap_1(A_3244,B_3247,C_3242,D_3243,E_3246,F_3245))
      | k2_partfun1(D_3243,B_3247,F_3245,k9_subset_1(A_3244,C_3242,D_3243)) != k2_partfun1(C_3242,B_3247,E_3246,k9_subset_1(A_3244,C_3242,D_3243))
      | ~ m1_subset_1(F_3245,k1_zfmisc_1(k2_zfmisc_1(D_3243,B_3247)))
      | ~ v1_funct_2(F_3245,D_3243,B_3247)
      | ~ v1_funct_1(F_3245)
      | ~ m1_subset_1(E_3246,k1_zfmisc_1(k2_zfmisc_1(C_3242,B_3247)))
      | ~ v1_funct_2(E_3246,C_3242,B_3247)
      | ~ v1_funct_1(E_3246)
      | ~ m1_subset_1(D_3243,k1_zfmisc_1(A_3244))
      | v1_xboole_0(D_3243)
      | ~ m1_subset_1(C_3242,k1_zfmisc_1(A_3244))
      | v1_xboole_0(C_3242)
      | v1_xboole_0(B_3247)
      | v1_xboole_0(A_3244) ) ),
    inference(resolution,[status(thm)],[c_62,c_61663])).

tff(c_76597,plain,(
    ! [C_3346,A_3348,E_3350,D_3347,F_3349,B_3351] :
      ( k2_partfun1(k4_subset_1(A_3348,C_3346,D_3347),B_3351,k1_tmap_1(A_3348,B_3351,C_3346,D_3347,E_3350,F_3349),D_3347) = F_3349
      | ~ v1_funct_1(k1_tmap_1(A_3348,B_3351,C_3346,D_3347,E_3350,F_3349))
      | k2_partfun1(D_3347,B_3351,F_3349,k9_subset_1(A_3348,C_3346,D_3347)) != k2_partfun1(C_3346,B_3351,E_3350,k9_subset_1(A_3348,C_3346,D_3347))
      | ~ m1_subset_1(F_3349,k1_zfmisc_1(k2_zfmisc_1(D_3347,B_3351)))
      | ~ v1_funct_2(F_3349,D_3347,B_3351)
      | ~ v1_funct_1(F_3349)
      | ~ m1_subset_1(E_3350,k1_zfmisc_1(k2_zfmisc_1(C_3346,B_3351)))
      | ~ v1_funct_2(E_3350,C_3346,B_3351)
      | ~ v1_funct_1(E_3350)
      | ~ m1_subset_1(D_3347,k1_zfmisc_1(A_3348))
      | v1_xboole_0(D_3347)
      | ~ m1_subset_1(C_3346,k1_zfmisc_1(A_3348))
      | v1_xboole_0(C_3346)
      | v1_xboole_0(B_3351)
      | v1_xboole_0(A_3348) ) ),
    inference(resolution,[status(thm)],[c_64,c_70550])).

tff(c_76601,plain,(
    ! [A_3348,C_3346,E_3350] :
      ( k2_partfun1(k4_subset_1(A_3348,C_3346,'#skF_4'),'#skF_2',k1_tmap_1(A_3348,'#skF_2',C_3346,'#skF_4',E_3350,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3348,'#skF_2',C_3346,'#skF_4',E_3350,'#skF_6'))
      | k2_partfun1(C_3346,'#skF_2',E_3350,k9_subset_1(A_3348,C_3346,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_3348,C_3346,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3350,k1_zfmisc_1(k2_zfmisc_1(C_3346,'#skF_2')))
      | ~ v1_funct_2(E_3350,C_3346,'#skF_2')
      | ~ v1_funct_1(E_3350)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3348))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3346,k1_zfmisc_1(A_3348))
      | v1_xboole_0(C_3346)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3348) ) ),
    inference(resolution,[status(thm)],[c_70,c_76597])).

tff(c_76610,plain,(
    ! [A_3348,C_3346,E_3350] :
      ( k2_partfun1(k4_subset_1(A_3348,C_3346,'#skF_4'),'#skF_2',k1_tmap_1(A_3348,'#skF_2',C_3346,'#skF_4',E_3350,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3348,'#skF_2',C_3346,'#skF_4',E_3350,'#skF_6'))
      | k2_partfun1(C_3346,'#skF_2',E_3350,k9_subset_1(A_3348,C_3346,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3348,C_3346,'#skF_4'))
      | ~ m1_subset_1(E_3350,k1_zfmisc_1(k2_zfmisc_1(C_3346,'#skF_2')))
      | ~ v1_funct_2(E_3350,C_3346,'#skF_2')
      | ~ v1_funct_1(E_3350)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3348))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3346,k1_zfmisc_1(A_3348))
      | v1_xboole_0(C_3346)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3348) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_60514,c_76601])).

tff(c_76966,plain,(
    ! [A_3354,C_3355,E_3356] :
      ( k2_partfun1(k4_subset_1(A_3354,C_3355,'#skF_4'),'#skF_2',k1_tmap_1(A_3354,'#skF_2',C_3355,'#skF_4',E_3356,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3354,'#skF_2',C_3355,'#skF_4',E_3356,'#skF_6'))
      | k2_partfun1(C_3355,'#skF_2',E_3356,k9_subset_1(A_3354,C_3355,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3354,C_3355,'#skF_4'))
      | ~ m1_subset_1(E_3356,k1_zfmisc_1(k2_zfmisc_1(C_3355,'#skF_2')))
      | ~ v1_funct_2(E_3356,C_3355,'#skF_2')
      | ~ v1_funct_1(E_3356)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3354))
      | ~ m1_subset_1(C_3355,k1_zfmisc_1(A_3354))
      | v1_xboole_0(C_3355)
      | v1_xboole_0(A_3354) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_76610])).

tff(c_76973,plain,(
    ! [A_3354] :
      ( k2_partfun1(k4_subset_1(A_3354,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3354,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3354,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_3354,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3354,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3354))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3354))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3354) ) ),
    inference(resolution,[status(thm)],[c_76,c_76966])).

tff(c_76986,plain,(
    ! [A_3354] :
      ( k2_partfun1(k4_subset_1(A_3354,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3354,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3354,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_3354,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3354,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3354))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3354))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_60517,c_76973])).

tff(c_78526,plain,(
    ! [A_3385] :
      ( k2_partfun1(k4_subset_1(A_3385,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3385,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3385,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_3385,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3385,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3385))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3385))
      | v1_xboole_0(A_3385) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_76986])).

tff(c_4522,plain,(
    ! [C_606,A_607,B_608] :
      ( v1_relat_1(C_606)
      | ~ m1_subset_1(C_606,k1_zfmisc_1(k2_zfmisc_1(A_607,B_608))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4533,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_4522])).

tff(c_4553,plain,(
    ! [C_615,A_616,B_617] :
      ( v4_relat_1(C_615,A_616)
      | ~ m1_subset_1(C_615,k1_zfmisc_1(k2_zfmisc_1(A_616,B_617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4564,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_4553])).

tff(c_5063,plain,(
    ! [B_664,A_665] :
      ( k1_relat_1(B_664) = A_665
      | ~ v1_partfun1(B_664,A_665)
      | ~ v4_relat_1(B_664,A_665)
      | ~ v1_relat_1(B_664) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5072,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4564,c_5063])).

tff(c_5081,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_5072])).

tff(c_5730,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5081])).

tff(c_6007,plain,(
    ! [C_739,A_740,B_741] :
      ( v1_partfun1(C_739,A_740)
      | ~ v1_funct_2(C_739,A_740,B_741)
      | ~ v1_funct_1(C_739)
      | ~ m1_subset_1(C_739,k1_zfmisc_1(k2_zfmisc_1(A_740,B_741)))
      | v1_xboole_0(B_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6010,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_6007])).

tff(c_6020,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_6010])).

tff(c_6022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5730,c_6020])).

tff(c_6023,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5081])).

tff(c_6037,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_4',A_16)
      | k9_relat_1('#skF_6',A_16) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6023,c_20])).

tff(c_6150,plain,(
    ! [A_746] :
      ( r1_xboole_0('#skF_4',A_746)
      | k9_relat_1('#skF_6',A_746) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_6037])).

tff(c_120,plain,(
    ! [A_245] :
      ( k9_relat_1(A_245,k1_relat_1(A_245)) = k2_relat_1(A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_129,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_120])).

tff(c_132,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_129])).

tff(c_133,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_134,plain,(
    ! [C_246,A_247,B_248] :
      ( v1_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_144,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_144])).

tff(c_152,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_4567,plain,(
    ! [A_618,B_619] :
      ( k7_relat_1(A_618,B_619) = k1_xboole_0
      | ~ r1_xboole_0(B_619,k1_relat_1(A_618))
      | ~ v1_relat_1(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4574,plain,(
    ! [B_619] :
      ( k7_relat_1(k1_xboole_0,B_619) = k1_xboole_0
      | ~ r1_xboole_0(B_619,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4567])).

tff(c_4577,plain,(
    ! [B_619] :
      ( k7_relat_1(k1_xboole_0,B_619) = k1_xboole_0
      | ~ r1_xboole_0(B_619,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_4574])).

tff(c_6178,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6150,c_4577])).

tff(c_8280,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6178])).

tff(c_4534,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_4522])).

tff(c_4565,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4553])).

tff(c_5066,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4565,c_5063])).

tff(c_5075,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_5066])).

tff(c_5088,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5075])).

tff(c_5655,plain,(
    ! [C_715,A_716,B_717] :
      ( v1_partfun1(C_715,A_716)
      | ~ v1_funct_2(C_715,A_716,B_717)
      | ~ v1_funct_1(C_715)
      | ~ m1_subset_1(C_715,k1_zfmisc_1(k2_zfmisc_1(A_716,B_717)))
      | v1_xboole_0(B_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5661,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_5655])).

tff(c_5672,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_5661])).

tff(c_5674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5088,c_5672])).

tff(c_5675,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5075])).

tff(c_5680,plain,(
    ! [A_16] :
      ( k9_relat_1('#skF_5',A_16) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_16)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5675,c_18])).

tff(c_6246,plain,(
    ! [A_751] :
      ( k9_relat_1('#skF_5',A_751) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_5680])).

tff(c_6253,plain,(
    ! [B_31] :
      ( k9_relat_1('#skF_5',B_31) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_6246])).

tff(c_6311,plain,(
    ! [B_753] :
      ( k9_relat_1('#skF_5',B_753) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_753)
      | v1_xboole_0(B_753) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_6253])).

tff(c_6314,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_6311])).

tff(c_6317,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6314])).

tff(c_5689,plain,(
    ! [A_16] :
      ( r1_xboole_0('#skF_3',A_16)
      | k9_relat_1('#skF_5',A_16) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5675,c_20])).

tff(c_6360,plain,(
    ! [A_756] :
      ( r1_xboole_0('#skF_3',A_756)
      | k9_relat_1('#skF_5',A_756) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_5689])).

tff(c_6043,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_6',B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6023,c_24])).

tff(c_6060,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_6',B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_6043])).

tff(c_6374,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6360,c_6060])).

tff(c_6395,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_6374])).

tff(c_6031,plain,(
    ! [A_28] :
      ( r1_xboole_0('#skF_4',A_28)
      | k7_relat_1('#skF_6',A_28) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6023,c_34])).

tff(c_6216,plain,(
    ! [A_750] :
      ( r1_xboole_0('#skF_4',A_750)
      | k7_relat_1('#skF_6',A_750) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_6031])).

tff(c_8108,plain,(
    ! [A_882] :
      ( k3_xboole_0('#skF_4',A_882) = k1_xboole_0
      | k7_relat_1('#skF_6',A_882) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6216,c_2])).

tff(c_8112,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6395,c_8108])).

tff(c_151,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_6040,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_6',A_28) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_28)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6023,c_32])).

tff(c_6137,plain,(
    ! [A_745] :
      ( k7_relat_1('#skF_6',A_745) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_745) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_6040])).

tff(c_8425,plain,(
    ! [B_910] :
      ( k7_relat_1('#skF_6',B_910) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_910) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_6137])).

tff(c_8449,plain,(
    ! [B_910] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_910)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0('#skF_4',B_910) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8425,c_30])).

tff(c_8470,plain,(
    ! [B_910] :
      ( r1_tarski(k1_xboole_0,B_910)
      | k3_xboole_0('#skF_4',B_910) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_28,c_8449])).

tff(c_6405,plain,(
    ! [B_21] :
      ( k9_relat_1(k1_xboole_0,B_21) = k9_relat_1('#skF_6',B_21)
      | ~ r1_tarski(B_21,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6395,c_22])).

tff(c_8693,plain,(
    ! [B_923] :
      ( k9_relat_1(k1_xboole_0,B_923) = k9_relat_1('#skF_6',B_923)
      | ~ r1_tarski(B_923,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_6405])).

tff(c_8697,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_6',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8470,c_8693])).

tff(c_8727,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8112,c_151,c_8697])).

tff(c_8729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8280,c_8727])).

tff(c_8730,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6178])).

tff(c_4759,plain,(
    ! [B_644,A_645] :
      ( r1_xboole_0(k1_relat_1(B_644),A_645)
      | k7_relat_1(B_644,A_645) != k1_xboole_0
      | ~ v1_relat_1(B_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4779,plain,(
    ! [A_645] :
      ( r1_xboole_0(k1_xboole_0,A_645)
      | k7_relat_1(k1_xboole_0,A_645) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4759])).

tff(c_4786,plain,(
    ! [A_645] :
      ( r1_xboole_0(k1_xboole_0,A_645)
      | k7_relat_1(k1_xboole_0,A_645) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_4779])).

tff(c_6078,plain,(
    ! [B_743] :
      ( k7_relat_1('#skF_6',B_743) = k1_xboole_0
      | ~ r1_xboole_0(B_743,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_6043])).

tff(c_6103,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4786,c_6078])).

tff(c_8817,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8730,c_6103])).

tff(c_6416,plain,(
    ! [A_757,B_758,C_759,D_760] :
      ( k2_partfun1(A_757,B_758,C_759,D_760) = k7_relat_1(C_759,D_760)
      | ~ m1_subset_1(C_759,k1_zfmisc_1(k2_zfmisc_1(A_757,B_758)))
      | ~ v1_funct_1(C_759) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6418,plain,(
    ! [D_760] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_760) = k7_relat_1('#skF_6',D_760)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_6416])).

tff(c_6426,plain,(
    ! [D_760] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_760) = k7_relat_1('#skF_6',D_760) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6418])).

tff(c_4861,plain,(
    ! [B_650,A_651] :
      ( k9_relat_1(B_650,A_651) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_650),A_651)
      | ~ v1_relat_1(B_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4878,plain,(
    ! [A_651] :
      ( k9_relat_1(k1_xboole_0,A_651) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_651)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4861])).

tff(c_4885,plain,(
    ! [A_652] :
      ( k9_relat_1(k1_xboole_0,A_652) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_652) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_4878])).

tff(c_4900,plain,(
    ! [A_645] :
      ( k9_relat_1(k1_xboole_0,A_645) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,A_645) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4786,c_4885])).

tff(c_4641,plain,(
    ! [B_630,A_631] :
      ( r1_xboole_0(k1_relat_1(B_630),A_631)
      | k9_relat_1(B_630,A_631) != k1_xboole_0
      | ~ v1_relat_1(B_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4661,plain,(
    ! [A_631] :
      ( r1_xboole_0(k1_xboole_0,A_631)
      | k9_relat_1(k1_xboole_0,A_631) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4641])).

tff(c_4668,plain,(
    ! [A_631] :
      ( r1_xboole_0(k1_xboole_0,A_631)
      | k9_relat_1(k1_xboole_0,A_631) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_4661])).

tff(c_5695,plain,(
    ! [B_25] :
      ( k7_relat_1('#skF_5',B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5675,c_24])).

tff(c_6263,plain,(
    ! [B_752] :
      ( k7_relat_1('#skF_5',B_752) = k1_xboole_0
      | ~ r1_xboole_0(B_752,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_5695])).

tff(c_6305,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4668,c_6263])).

tff(c_6625,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6305])).

tff(c_6633,plain,(
    k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4900,c_6625])).

tff(c_6399,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6360,c_4577])).

tff(c_7459,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6633,c_6399])).

tff(c_7477,plain,(
    ! [A_843] :
      ( k3_xboole_0('#skF_4',A_843) = k1_xboole_0
      | k7_relat_1('#skF_6',A_843) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6216,c_2])).

tff(c_7489,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6395,c_7477])).

tff(c_6885,plain,(
    ! [A_807] :
      ( k7_relat_1('#skF_5',A_807) = k1_xboole_0
      | k3_xboole_0(A_807,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_6263])).

tff(c_6903,plain,(
    ! [A_807] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_807)
      | ~ v1_relat_1('#skF_5')
      | k3_xboole_0(A_807,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6885,c_30])).

tff(c_6920,plain,(
    ! [A_807] :
      ( r1_tarski(k1_xboole_0,A_807)
      | k3_xboole_0(A_807,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_28,c_6903])).

tff(c_5692,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_28)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5675,c_32])).

tff(c_5710,plain,(
    ! [A_28] :
      ( k7_relat_1('#skF_5',A_28) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_5692])).

tff(c_6540,plain,(
    ! [A_771] :
      ( k7_relat_1('#skF_5',A_771) = k1_xboole_0
      | k9_relat_1('#skF_5',A_771) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6360,c_5710])).

tff(c_6555,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6317,c_6540])).

tff(c_6561,plain,(
    ! [B_21] :
      ( k9_relat_1(k1_xboole_0,B_21) = k9_relat_1('#skF_5',B_21)
      | ~ r1_tarski(B_21,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6555,c_22])).

tff(c_7816,plain,(
    ! [B_864] :
      ( k9_relat_1(k1_xboole_0,B_864) = k9_relat_1('#skF_5',B_864)
      | ~ r1_tarski(B_864,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_6561])).

tff(c_7824,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1('#skF_5',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6920,c_7816])).

tff(c_7853,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7489,c_151,c_7824])).

tff(c_7855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7459,c_7853])).

tff(c_7856,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6305])).

tff(c_6420,plain,(
    ! [D_760] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_760) = k7_relat_1('#skF_5',D_760)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_6416])).

tff(c_6429,plain,(
    ! [D_760] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_760) = k7_relat_1('#skF_5',D_760) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6420])).

tff(c_7949,plain,(
    ! [A_871] :
      ( k3_xboole_0('#skF_3',A_871) = k1_xboole_0
      | k9_relat_1('#skF_5',A_871) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6360,c_2])).

tff(c_7964,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6317,c_7949])).

tff(c_4954,plain,(
    ! [A_655,B_656,C_657] :
      ( k9_subset_1(A_655,B_656,C_657) = k3_xboole_0(B_656,C_657)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(A_655)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4967,plain,(
    ! [B_656] : k9_subset_1('#skF_1',B_656,'#skF_4') = k3_xboole_0(B_656,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_4954])).

tff(c_68,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_119,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_4970,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_4967,c_119])).

tff(c_10382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8817,c_6426,c_7856,c_6429,c_7964,c_7964,c_4970])).

tff(c_10383,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_58460,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10383])).

tff(c_78537,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78526,c_58460])).

tff(c_78551,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_62275,c_61651,c_60212,c_61372,c_61651,c_60212,c_63497,c_78537])).

tff(c_78553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_78551])).

tff(c_78554,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10383])).

tff(c_117306,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117294,c_78554])).

tff(c_117320,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_84247,c_81312,c_80449,c_82929,c_81312,c_80449,c_85156,c_117306])).

tff(c_117322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_117320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.91/14.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.08/14.97  
% 24.08/14.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.08/14.98  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 24.08/14.98  
% 24.08/14.98  %Foreground sorts:
% 24.08/14.98  
% 24.08/14.98  
% 24.08/14.98  %Background operators:
% 24.08/14.98  
% 24.08/14.98  
% 24.08/14.98  %Foreground operators:
% 24.08/14.98  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 24.08/14.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 24.08/14.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.08/14.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.08/14.98  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 24.08/14.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.08/14.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.08/14.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 24.08/14.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.08/14.98  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 24.08/14.98  tff('#skF_5', type, '#skF_5': $i).
% 24.08/14.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 24.08/14.98  tff('#skF_6', type, '#skF_6': $i).
% 24.08/14.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 24.08/14.98  tff('#skF_2', type, '#skF_2': $i).
% 24.08/14.98  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 24.08/14.98  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 24.08/14.98  tff('#skF_3', type, '#skF_3': $i).
% 24.08/14.98  tff('#skF_1', type, '#skF_1': $i).
% 24.08/14.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 24.08/14.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.08/14.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.08/14.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.08/14.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.08/14.98  tff('#skF_4', type, '#skF_4': $i).
% 24.08/14.98  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 24.08/14.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.08/14.98  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 24.08/14.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 24.08/14.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.08/14.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 24.08/14.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 24.08/14.98  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 24.08/14.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.08/14.98  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 24.08/14.98  
% 24.36/15.03  tff(f_259, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 24.36/15.03  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 24.36/15.03  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 24.36/15.03  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 24.36/15.03  tff(f_121, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 24.36/15.03  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 24.36/15.03  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 24.36/15.03  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 24.36/15.03  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 24.36/15.03  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 24.36/15.03  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 24.36/15.03  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 24.36/15.03  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 24.36/15.03  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 24.36/15.03  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 24.36/15.03  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 24.36/15.03  tff(f_217, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 24.36/15.03  tff(f_135, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 24.36/15.03  tff(f_183, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 24.36/15.03  tff(c_94, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_58327, plain, (![C_2657, A_2658, B_2659]: (v1_relat_1(C_2657) | ~m1_subset_1(C_2657, k1_zfmisc_1(k2_zfmisc_1(A_2658, B_2659))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.36/15.03  tff(c_58338, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_58327])).
% 24.36/15.03  tff(c_92, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_58346, plain, (![C_2660, A_2661, B_2662]: (v4_relat_1(C_2660, A_2661) | ~m1_subset_1(C_2660, k1_zfmisc_1(k2_zfmisc_1(A_2661, B_2662))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 24.36/15.03  tff(c_58357, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_58346])).
% 24.36/15.03  tff(c_78888, plain, (![B_3409, A_3410]: (k1_relat_1(B_3409)=A_3410 | ~v1_partfun1(B_3409, A_3410) | ~v4_relat_1(B_3409, A_3410) | ~v1_relat_1(B_3409))), inference(cnfTransformation, [status(thm)], [f_129])).
% 24.36/15.03  tff(c_78897, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58357, c_78888])).
% 24.36/15.03  tff(c_78906, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_78897])).
% 24.36/15.03  tff(c_79833, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_78906])).
% 24.36/15.03  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_80277, plain, (![C_3512, A_3513, B_3514]: (v1_partfun1(C_3512, A_3513) | ~v1_funct_2(C_3512, A_3513, B_3514) | ~v1_funct_1(C_3512) | ~m1_subset_1(C_3512, k1_zfmisc_1(k2_zfmisc_1(A_3513, B_3514))) | v1_xboole_0(B_3514))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.36/15.03  tff(c_80280, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_80277])).
% 24.36/15.03  tff(c_80290, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_80280])).
% 24.36/15.03  tff(c_80292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_79833, c_80290])).
% 24.36/15.03  tff(c_80293, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_78906])).
% 24.36/15.03  tff(c_20, plain, (![B_17, A_16]: (r1_xboole_0(k1_relat_1(B_17), A_16) | k9_relat_1(B_17, A_16)!=k1_xboole_0 | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.36/15.03  tff(c_80310, plain, (![A_16]: (r1_xboole_0('#skF_4', A_16) | k9_relat_1('#skF_6', A_16)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80293, c_20])).
% 24.36/15.03  tff(c_80502, plain, (![A_3528]: (r1_xboole_0('#skF_4', A_3528) | k9_relat_1('#skF_6', A_3528)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_80310])).
% 24.36/15.03  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.36/15.03  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.36/15.03  tff(c_10385, plain, (![A_989]: (k9_relat_1(A_989, k1_relat_1(A_989))=k2_relat_1(A_989) | ~v1_relat_1(A_989))), inference(cnfTransformation, [status(thm)], [f_54])).
% 24.36/15.03  tff(c_10394, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_10385])).
% 24.36/15.03  tff(c_10397, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10394])).
% 24.36/15.03  tff(c_10398, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10397])).
% 24.36/15.03  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.36/15.03  tff(c_10403, plain, (![C_990, A_991, B_992]: (v1_relat_1(C_990) | ~m1_subset_1(C_990, k1_zfmisc_1(k2_zfmisc_1(A_991, B_992))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.36/15.03  tff(c_10413, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_10403])).
% 24.36/15.03  tff(c_10419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10398, c_10413])).
% 24.36/15.03  tff(c_10421, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_10397])).
% 24.36/15.03  tff(c_58397, plain, (![A_2677, B_2678]: (k7_relat_1(A_2677, B_2678)=k1_xboole_0 | ~r1_xboole_0(B_2678, k1_relat_1(A_2677)) | ~v1_relat_1(A_2677))), inference(cnfTransformation, [status(thm)], [f_74])).
% 24.36/15.03  tff(c_58404, plain, (![B_2678]: (k7_relat_1(k1_xboole_0, B_2678)=k1_xboole_0 | ~r1_xboole_0(B_2678, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_58397])).
% 24.36/15.03  tff(c_58407, plain, (![B_2678]: (k7_relat_1(k1_xboole_0, B_2678)=k1_xboole_0 | ~r1_xboole_0(B_2678, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10421, c_58404])).
% 24.36/15.03  tff(c_80534, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_80502, c_58407])).
% 24.36/15.03  tff(c_83093, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_80534])).
% 24.36/15.03  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.36/15.03  tff(c_18, plain, (![B_17, A_16]: (k9_relat_1(B_17, A_16)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.36/15.03  tff(c_80298, plain, (![A_16]: (k9_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_16) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80293, c_18])).
% 24.36/15.03  tff(c_80419, plain, (![A_3518]: (k9_relat_1('#skF_6', A_3518)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_3518))), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_80298])).
% 24.36/15.03  tff(c_81014, plain, (![B_3567]: (k9_relat_1('#skF_6', B_3567)=k1_xboole_0 | k3_xboole_0('#skF_4', B_3567)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_80419])).
% 24.36/15.03  tff(c_80328, plain, (![A_16]: (r1_xboole_0('#skF_4', A_16) | k9_relat_1('#skF_6', A_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_80310])).
% 24.36/15.03  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_58339, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_58327])).
% 24.36/15.03  tff(c_58358, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_58346])).
% 24.36/15.03  tff(c_78894, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58358, c_78888])).
% 24.36/15.03  tff(c_78903, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_78894])).
% 24.36/15.03  tff(c_78913, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_78903])).
% 24.36/15.03  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_78, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_79771, plain, (![C_3478, A_3479, B_3480]: (v1_partfun1(C_3478, A_3479) | ~v1_funct_2(C_3478, A_3479, B_3480) | ~v1_funct_1(C_3478) | ~m1_subset_1(C_3478, k1_zfmisc_1(k2_zfmisc_1(A_3479, B_3480))) | v1_xboole_0(B_3480))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.36/15.03  tff(c_79777, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_79771])).
% 24.36/15.03  tff(c_79788, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_79777])).
% 24.36/15.03  tff(c_79790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_78913, c_79788])).
% 24.36/15.03  tff(c_79791, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_78903])).
% 24.36/15.03  tff(c_24, plain, (![A_23, B_25]: (k7_relat_1(A_23, B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, k1_relat_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 24.36/15.03  tff(c_79811, plain, (![B_25]: (k7_relat_1('#skF_5', B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_79791, c_24])).
% 24.36/15.03  tff(c_80550, plain, (![B_3530]: (k7_relat_1('#skF_5', B_3530)=k1_xboole_0 | ~r1_xboole_0(B_3530, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_79811])).
% 24.36/15.03  tff(c_80583, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_80328, c_80550])).
% 24.36/15.03  tff(c_80836, plain, (k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_80583])).
% 24.36/15.03  tff(c_81039, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_81014, c_80836])).
% 24.36/15.03  tff(c_86, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_34, plain, (![B_29, A_28]: (r1_xboole_0(k1_relat_1(B_29), A_28) | k7_relat_1(B_29, A_28)!=k1_xboole_0 | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 24.36/15.03  tff(c_79805, plain, (![A_28]: (r1_xboole_0('#skF_3', A_28) | k7_relat_1('#skF_5', A_28)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_79791, c_34])).
% 24.36/15.03  tff(c_80668, plain, (![A_3535]: (r1_xboole_0('#skF_3', A_3535) | k7_relat_1('#skF_5', A_3535)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_79805])).
% 24.36/15.03  tff(c_80313, plain, (![B_25]: (k7_relat_1('#skF_6', B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80293, c_24])).
% 24.36/15.03  tff(c_80330, plain, (![B_25]: (k7_relat_1('#skF_6', B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_80313])).
% 24.36/15.03  tff(c_80700, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_80668, c_80330])).
% 24.36/15.03  tff(c_80885, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_80700])).
% 24.36/15.03  tff(c_82, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_90, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_38, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | ~r1_subset_1(A_30, B_31) | v1_xboole_0(B_31) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_97])).
% 24.36/15.03  tff(c_32, plain, (![B_29, A_28]: (k7_relat_1(B_29, A_28)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 24.36/15.03  tff(c_79802, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_28) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_79791, c_32])).
% 24.36/15.03  tff(c_80489, plain, (![A_3527]: (k7_relat_1('#skF_5', A_3527)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_3527))), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_79802])).
% 24.36/15.03  tff(c_80493, plain, (![B_31]: (k7_relat_1('#skF_5', B_31)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_31) | v1_xboole_0(B_31) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_80489])).
% 24.36/15.03  tff(c_80942, plain, (![B_3560]: (k7_relat_1('#skF_5', B_3560)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_3560) | v1_xboole_0(B_3560))), inference(negUnitSimplification, [status(thm)], [c_90, c_80493])).
% 24.36/15.03  tff(c_80945, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_80942])).
% 24.36/15.03  tff(c_80949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_80885, c_80945])).
% 24.36/15.03  tff(c_80950, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_80700])).
% 24.36/15.03  tff(c_80307, plain, (![A_28]: (r1_xboole_0('#skF_4', A_28) | k7_relat_1('#skF_6', A_28)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80293, c_34])).
% 24.36/15.03  tff(c_80376, plain, (![A_3516]: (r1_xboole_0('#skF_4', A_3516) | k7_relat_1('#skF_6', A_3516)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_80307])).
% 24.36/15.03  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.36/15.03  tff(c_81272, plain, (![A_3595]: (k3_xboole_0('#skF_4', A_3595)=k1_xboole_0 | k7_relat_1('#skF_6', A_3595)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80376, c_2])).
% 24.36/15.03  tff(c_81278, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_80950, c_81272])).
% 24.36/15.03  tff(c_81283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81039, c_81278])).
% 24.36/15.03  tff(c_81284, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_80583])).
% 24.36/15.03  tff(c_80706, plain, (![A_3535]: (k3_xboole_0('#skF_3', A_3535)=k1_xboole_0 | k7_relat_1('#skF_5', A_3535)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80668, c_2])).
% 24.36/15.03  tff(c_81312, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_81284, c_80706])).
% 24.36/15.03  tff(c_10420, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_10397])).
% 24.36/15.03  tff(c_80343, plain, (![B_3515]: (k7_relat_1('#skF_6', B_3515)=k1_xboole_0 | ~r1_xboole_0(B_3515, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_80313])).
% 24.36/15.03  tff(c_83498, plain, (![A_3761]: (k7_relat_1('#skF_6', A_3761)=k1_xboole_0 | k3_xboole_0(A_3761, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_80343])).
% 24.36/15.03  tff(c_30, plain, (![B_27, A_26]: (r1_tarski(k1_relat_1(k7_relat_1(B_27, A_26)), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.36/15.03  tff(c_83522, plain, (![A_3761]: (r1_tarski(k1_relat_1(k1_xboole_0), A_3761) | ~v1_relat_1('#skF_6') | k3_xboole_0(A_3761, '#skF_4')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_83498, c_30])).
% 24.36/15.03  tff(c_83543, plain, (![A_3761]: (r1_tarski(k1_xboole_0, A_3761) | k3_xboole_0(A_3761, '#skF_4')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_28, c_83522])).
% 24.36/15.03  tff(c_83159, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_81284, c_80700])).
% 24.36/15.03  tff(c_22, plain, (![A_18, C_22, B_21]: (k9_relat_1(k7_relat_1(A_18, C_22), B_21)=k9_relat_1(A_18, B_21) | ~r1_tarski(B_21, C_22) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 24.36/15.03  tff(c_83166, plain, (![B_21]: (k9_relat_1(k1_xboole_0, B_21)=k9_relat_1('#skF_6', B_21) | ~r1_tarski(B_21, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_83159, c_22])).
% 24.36/15.03  tff(c_83837, plain, (![B_3777]: (k9_relat_1(k1_xboole_0, B_3777)=k9_relat_1('#skF_6', B_3777) | ~r1_tarski(B_3777, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_83166])).
% 24.36/15.03  tff(c_83845, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_83543, c_83837])).
% 24.36/15.03  tff(c_83874, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_81312, c_10420, c_83845])).
% 24.36/15.03  tff(c_83876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83093, c_83874])).
% 24.36/15.03  tff(c_83877, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_80534])).
% 24.36/15.03  tff(c_78611, plain, (![B_3391, A_3392]: (r1_xboole_0(k1_relat_1(B_3391), A_3392) | k7_relat_1(B_3391, A_3392)!=k1_xboole_0 | ~v1_relat_1(B_3391))), inference(cnfTransformation, [status(thm)], [f_87])).
% 24.36/15.03  tff(c_78625, plain, (![A_3392]: (r1_xboole_0(k1_xboole_0, A_3392) | k7_relat_1(k1_xboole_0, A_3392)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_78611])).
% 24.36/15.03  tff(c_78631, plain, (![A_3393]: (r1_xboole_0(k1_xboole_0, A_3393) | k7_relat_1(k1_xboole_0, A_3393)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10421, c_78625])).
% 24.36/15.03  tff(c_78647, plain, (![A_3393]: (k3_xboole_0(k1_xboole_0, A_3393)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_3393)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_78631, c_2])).
% 24.36/15.03  tff(c_83907, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_83877, c_78647])).
% 24.36/15.03  tff(c_78803, plain, (![B_3405, A_3406]: (k9_relat_1(B_3405, A_3406)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_3405), A_3406) | ~v1_relat_1(B_3405))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.36/15.03  tff(c_78820, plain, (![A_3406]: (k9_relat_1(k1_xboole_0, A_3406)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_3406) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_78803])).
% 24.36/15.03  tff(c_78827, plain, (![A_3407]: (k9_relat_1(k1_xboole_0, A_3407)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_3407))), inference(demodulation, [status(thm), theory('equality')], [c_10421, c_78820])).
% 24.36/15.03  tff(c_78846, plain, (![B_2]: (k9_relat_1(k1_xboole_0, B_2)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_78827])).
% 24.36/15.03  tff(c_58408, plain, (![B_2679, A_2680]: (r1_xboole_0(k1_relat_1(B_2679), A_2680) | k9_relat_1(B_2679, A_2680)!=k1_xboole_0 | ~v1_relat_1(B_2679))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.36/15.03  tff(c_58418, plain, (![A_2680]: (r1_xboole_0(k1_xboole_0, A_2680) | k9_relat_1(k1_xboole_0, A_2680)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_58408])).
% 24.36/15.03  tff(c_58422, plain, (![A_2680]: (r1_xboole_0(k1_xboole_0, A_2680) | k9_relat_1(k1_xboole_0, A_2680)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10421, c_58418])).
% 24.36/15.03  tff(c_80373, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_58422, c_80343])).
% 24.36/15.03  tff(c_84236, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_80373])).
% 24.36/15.03  tff(c_84239, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_78846, c_84236])).
% 24.36/15.03  tff(c_84246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83907, c_84239])).
% 24.36/15.03  tff(c_84247, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_80373])).
% 24.36/15.03  tff(c_80436, plain, (![A_3519, B_3520, C_3521]: (k9_subset_1(A_3519, B_3520, C_3521)=k3_xboole_0(B_3520, C_3521) | ~m1_subset_1(C_3521, k1_zfmisc_1(A_3519)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.36/15.03  tff(c_80449, plain, (![B_3520]: (k9_subset_1('#skF_1', B_3520, '#skF_4')=k3_xboole_0(B_3520, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_80436])).
% 24.36/15.03  tff(c_78630, plain, (![A_3392]: (r1_xboole_0(k1_xboole_0, A_3392) | k7_relat_1(k1_xboole_0, A_3392)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10421, c_78625])).
% 24.36/15.03  tff(c_78842, plain, (![A_3392]: (k9_relat_1(k1_xboole_0, A_3392)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_3392)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_78630, c_78827])).
% 24.36/15.03  tff(c_80590, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_58422, c_80550])).
% 24.36/15.03  tff(c_81384, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_80590])).
% 24.36/15.03  tff(c_81392, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_78842, c_81384])).
% 24.36/15.03  tff(c_79808, plain, (![A_16]: (r1_xboole_0('#skF_3', A_16) | k9_relat_1('#skF_5', A_16)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_79791, c_20])).
% 24.36/15.03  tff(c_80593, plain, (![A_3531]: (r1_xboole_0('#skF_3', A_3531) | k9_relat_1('#skF_5', A_3531)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_79808])).
% 24.36/15.03  tff(c_80630, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_80593, c_58407])).
% 24.36/15.03  tff(c_82194, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_81392, c_80630])).
% 24.36/15.03  tff(c_82237, plain, (![B_3674]: (k7_relat_1('#skF_5', B_3674)=k1_xboole_0 | k3_xboole_0('#skF_3', B_3674)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_80489])).
% 24.36/15.03  tff(c_82258, plain, (![B_3674]: (r1_tarski(k1_relat_1(k1_xboole_0), B_3674) | ~v1_relat_1('#skF_5') | k3_xboole_0('#skF_3', B_3674)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82237, c_30])).
% 24.36/15.03  tff(c_82278, plain, (![B_3674]: (r1_tarski(k1_xboole_0, B_3674) | k3_xboole_0('#skF_3', B_3674)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_28, c_82258])).
% 24.36/15.03  tff(c_81303, plain, (![B_21]: (k9_relat_1(k1_xboole_0, B_21)=k9_relat_1('#skF_5', B_21) | ~r1_tarski(B_21, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_81284, c_22])).
% 24.36/15.03  tff(c_82886, plain, (![B_3715]: (k9_relat_1(k1_xboole_0, B_3715)=k9_relat_1('#skF_5', B_3715) | ~r1_tarski(B_3715, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_81303])).
% 24.36/15.03  tff(c_82898, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_82278, c_82886])).
% 24.36/15.03  tff(c_82926, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_81312, c_10420, c_82898])).
% 24.36/15.03  tff(c_82928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82194, c_82926])).
% 24.36/15.03  tff(c_82929, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_80590])).
% 24.36/15.03  tff(c_83043, plain, (![B_3722, A_3719, F_3720, D_3718, C_3717, E_3721]: (v1_funct_1(k1_tmap_1(A_3719, B_3722, C_3717, D_3718, E_3721, F_3720)) | ~m1_subset_1(F_3720, k1_zfmisc_1(k2_zfmisc_1(D_3718, B_3722))) | ~v1_funct_2(F_3720, D_3718, B_3722) | ~v1_funct_1(F_3720) | ~m1_subset_1(E_3721, k1_zfmisc_1(k2_zfmisc_1(C_3717, B_3722))) | ~v1_funct_2(E_3721, C_3717, B_3722) | ~v1_funct_1(E_3721) | ~m1_subset_1(D_3718, k1_zfmisc_1(A_3719)) | v1_xboole_0(D_3718) | ~m1_subset_1(C_3717, k1_zfmisc_1(A_3719)) | v1_xboole_0(C_3717) | v1_xboole_0(B_3722) | v1_xboole_0(A_3719))), inference(cnfTransformation, [status(thm)], [f_217])).
% 24.36/15.03  tff(c_83045, plain, (![A_3719, C_3717, E_3721]: (v1_funct_1(k1_tmap_1(A_3719, '#skF_2', C_3717, '#skF_4', E_3721, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3721, k1_zfmisc_1(k2_zfmisc_1(C_3717, '#skF_2'))) | ~v1_funct_2(E_3721, C_3717, '#skF_2') | ~v1_funct_1(E_3721) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3719)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3717, k1_zfmisc_1(A_3719)) | v1_xboole_0(C_3717) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3719))), inference(resolution, [status(thm)], [c_70, c_83043])).
% 24.36/15.03  tff(c_83053, plain, (![A_3719, C_3717, E_3721]: (v1_funct_1(k1_tmap_1(A_3719, '#skF_2', C_3717, '#skF_4', E_3721, '#skF_6')) | ~m1_subset_1(E_3721, k1_zfmisc_1(k2_zfmisc_1(C_3717, '#skF_2'))) | ~v1_funct_2(E_3721, C_3717, '#skF_2') | ~v1_funct_1(E_3721) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3719)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3717, k1_zfmisc_1(A_3719)) | v1_xboole_0(C_3717) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3719))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_83045])).
% 24.36/15.03  tff(c_84712, plain, (![A_3829, C_3830, E_3831]: (v1_funct_1(k1_tmap_1(A_3829, '#skF_2', C_3830, '#skF_4', E_3831, '#skF_6')) | ~m1_subset_1(E_3831, k1_zfmisc_1(k2_zfmisc_1(C_3830, '#skF_2'))) | ~v1_funct_2(E_3831, C_3830, '#skF_2') | ~v1_funct_1(E_3831) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3829)) | ~m1_subset_1(C_3830, k1_zfmisc_1(A_3829)) | v1_xboole_0(C_3830) | v1_xboole_0(A_3829))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_83053])).
% 24.36/15.03  tff(c_84719, plain, (![A_3829]: (v1_funct_1(k1_tmap_1(A_3829, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3829)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3829)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3829))), inference(resolution, [status(thm)], [c_76, c_84712])).
% 24.36/15.03  tff(c_84732, plain, (![A_3829]: (v1_funct_1(k1_tmap_1(A_3829, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3829)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3829)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3829))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_84719])).
% 24.36/15.03  tff(c_85149, plain, (![A_3848]: (v1_funct_1(k1_tmap_1(A_3848, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3848)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3848)) | v1_xboole_0(A_3848))), inference(negUnitSimplification, [status(thm)], [c_90, c_84732])).
% 24.36/15.03  tff(c_85152, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_85149])).
% 24.36/15.03  tff(c_85155, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_85152])).
% 24.36/15.03  tff(c_85156, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_94, c_85155])).
% 24.36/15.03  tff(c_80796, plain, (![A_3540, B_3541, C_3542, D_3543]: (k2_partfun1(A_3540, B_3541, C_3542, D_3543)=k7_relat_1(C_3542, D_3543) | ~m1_subset_1(C_3542, k1_zfmisc_1(k2_zfmisc_1(A_3540, B_3541))) | ~v1_funct_1(C_3542))), inference(cnfTransformation, [status(thm)], [f_135])).
% 24.36/15.03  tff(c_80800, plain, (![D_3543]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_3543)=k7_relat_1('#skF_5', D_3543) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_80796])).
% 24.36/15.03  tff(c_80809, plain, (![D_3543]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_3543)=k7_relat_1('#skF_5', D_3543))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80800])).
% 24.36/15.03  tff(c_80798, plain, (![D_3543]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_3543)=k7_relat_1('#skF_6', D_3543) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_80796])).
% 24.36/15.03  tff(c_80806, plain, (![D_3543]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_3543)=k7_relat_1('#skF_6', D_3543))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_80798])).
% 24.36/15.03  tff(c_64, plain, (![C_177, F_180, A_175, D_178, B_176, E_179]: (v1_funct_2(k1_tmap_1(A_175, B_176, C_177, D_178, E_179, F_180), k4_subset_1(A_175, C_177, D_178), B_176) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(D_178, B_176))) | ~v1_funct_2(F_180, D_178, B_176) | ~v1_funct_1(F_180) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(C_177, B_176))) | ~v1_funct_2(E_179, C_177, B_176) | ~v1_funct_1(E_179) | ~m1_subset_1(D_178, k1_zfmisc_1(A_175)) | v1_xboole_0(D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(A_175)) | v1_xboole_0(C_177) | v1_xboole_0(B_176) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_217])).
% 24.36/15.03  tff(c_62, plain, (![C_177, F_180, A_175, D_178, B_176, E_179]: (m1_subset_1(k1_tmap_1(A_175, B_176, C_177, D_178, E_179, F_180), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_175, C_177, D_178), B_176))) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(D_178, B_176))) | ~v1_funct_2(F_180, D_178, B_176) | ~v1_funct_1(F_180) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(C_177, B_176))) | ~v1_funct_2(E_179, C_177, B_176) | ~v1_funct_1(E_179) | ~m1_subset_1(D_178, k1_zfmisc_1(A_175)) | v1_xboole_0(D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(A_175)) | v1_xboole_0(C_177) | v1_xboole_0(B_176) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_217])).
% 24.36/15.03  tff(c_84177, plain, (![E_3797, B_3802, C_3799, A_3798, D_3800, F_3801]: (k2_partfun1(k4_subset_1(A_3798, C_3799, D_3800), B_3802, k1_tmap_1(A_3798, B_3802, C_3799, D_3800, E_3797, F_3801), C_3799)=E_3797 | ~m1_subset_1(k1_tmap_1(A_3798, B_3802, C_3799, D_3800, E_3797, F_3801), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3798, C_3799, D_3800), B_3802))) | ~v1_funct_2(k1_tmap_1(A_3798, B_3802, C_3799, D_3800, E_3797, F_3801), k4_subset_1(A_3798, C_3799, D_3800), B_3802) | ~v1_funct_1(k1_tmap_1(A_3798, B_3802, C_3799, D_3800, E_3797, F_3801)) | k2_partfun1(D_3800, B_3802, F_3801, k9_subset_1(A_3798, C_3799, D_3800))!=k2_partfun1(C_3799, B_3802, E_3797, k9_subset_1(A_3798, C_3799, D_3800)) | ~m1_subset_1(F_3801, k1_zfmisc_1(k2_zfmisc_1(D_3800, B_3802))) | ~v1_funct_2(F_3801, D_3800, B_3802) | ~v1_funct_1(F_3801) | ~m1_subset_1(E_3797, k1_zfmisc_1(k2_zfmisc_1(C_3799, B_3802))) | ~v1_funct_2(E_3797, C_3799, B_3802) | ~v1_funct_1(E_3797) | ~m1_subset_1(D_3800, k1_zfmisc_1(A_3798)) | v1_xboole_0(D_3800) | ~m1_subset_1(C_3799, k1_zfmisc_1(A_3798)) | v1_xboole_0(C_3799) | v1_xboole_0(B_3802) | v1_xboole_0(A_3798))), inference(cnfTransformation, [status(thm)], [f_183])).
% 24.36/15.03  tff(c_104479, plain, (![F_4336, E_4337, D_4334, B_4338, A_4335, C_4333]: (k2_partfun1(k4_subset_1(A_4335, C_4333, D_4334), B_4338, k1_tmap_1(A_4335, B_4338, C_4333, D_4334, E_4337, F_4336), C_4333)=E_4337 | ~v1_funct_2(k1_tmap_1(A_4335, B_4338, C_4333, D_4334, E_4337, F_4336), k4_subset_1(A_4335, C_4333, D_4334), B_4338) | ~v1_funct_1(k1_tmap_1(A_4335, B_4338, C_4333, D_4334, E_4337, F_4336)) | k2_partfun1(D_4334, B_4338, F_4336, k9_subset_1(A_4335, C_4333, D_4334))!=k2_partfun1(C_4333, B_4338, E_4337, k9_subset_1(A_4335, C_4333, D_4334)) | ~m1_subset_1(F_4336, k1_zfmisc_1(k2_zfmisc_1(D_4334, B_4338))) | ~v1_funct_2(F_4336, D_4334, B_4338) | ~v1_funct_1(F_4336) | ~m1_subset_1(E_4337, k1_zfmisc_1(k2_zfmisc_1(C_4333, B_4338))) | ~v1_funct_2(E_4337, C_4333, B_4338) | ~v1_funct_1(E_4337) | ~m1_subset_1(D_4334, k1_zfmisc_1(A_4335)) | v1_xboole_0(D_4334) | ~m1_subset_1(C_4333, k1_zfmisc_1(A_4335)) | v1_xboole_0(C_4333) | v1_xboole_0(B_4338) | v1_xboole_0(A_4335))), inference(resolution, [status(thm)], [c_62, c_84177])).
% 24.36/15.03  tff(c_111186, plain, (![A_4452, D_4451, F_4453, E_4454, B_4455, C_4450]: (k2_partfun1(k4_subset_1(A_4452, C_4450, D_4451), B_4455, k1_tmap_1(A_4452, B_4455, C_4450, D_4451, E_4454, F_4453), C_4450)=E_4454 | ~v1_funct_1(k1_tmap_1(A_4452, B_4455, C_4450, D_4451, E_4454, F_4453)) | k2_partfun1(D_4451, B_4455, F_4453, k9_subset_1(A_4452, C_4450, D_4451))!=k2_partfun1(C_4450, B_4455, E_4454, k9_subset_1(A_4452, C_4450, D_4451)) | ~m1_subset_1(F_4453, k1_zfmisc_1(k2_zfmisc_1(D_4451, B_4455))) | ~v1_funct_2(F_4453, D_4451, B_4455) | ~v1_funct_1(F_4453) | ~m1_subset_1(E_4454, k1_zfmisc_1(k2_zfmisc_1(C_4450, B_4455))) | ~v1_funct_2(E_4454, C_4450, B_4455) | ~v1_funct_1(E_4454) | ~m1_subset_1(D_4451, k1_zfmisc_1(A_4452)) | v1_xboole_0(D_4451) | ~m1_subset_1(C_4450, k1_zfmisc_1(A_4452)) | v1_xboole_0(C_4450) | v1_xboole_0(B_4455) | v1_xboole_0(A_4452))), inference(resolution, [status(thm)], [c_64, c_104479])).
% 24.36/15.03  tff(c_111190, plain, (![A_4452, C_4450, E_4454]: (k2_partfun1(k4_subset_1(A_4452, C_4450, '#skF_4'), '#skF_2', k1_tmap_1(A_4452, '#skF_2', C_4450, '#skF_4', E_4454, '#skF_6'), C_4450)=E_4454 | ~v1_funct_1(k1_tmap_1(A_4452, '#skF_2', C_4450, '#skF_4', E_4454, '#skF_6')) | k2_partfun1(C_4450, '#skF_2', E_4454, k9_subset_1(A_4452, C_4450, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_4452, C_4450, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_4454, k1_zfmisc_1(k2_zfmisc_1(C_4450, '#skF_2'))) | ~v1_funct_2(E_4454, C_4450, '#skF_2') | ~v1_funct_1(E_4454) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4452)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_4450, k1_zfmisc_1(A_4452)) | v1_xboole_0(C_4450) | v1_xboole_0('#skF_2') | v1_xboole_0(A_4452))), inference(resolution, [status(thm)], [c_70, c_111186])).
% 24.36/15.03  tff(c_111199, plain, (![A_4452, C_4450, E_4454]: (k2_partfun1(k4_subset_1(A_4452, C_4450, '#skF_4'), '#skF_2', k1_tmap_1(A_4452, '#skF_2', C_4450, '#skF_4', E_4454, '#skF_6'), C_4450)=E_4454 | ~v1_funct_1(k1_tmap_1(A_4452, '#skF_2', C_4450, '#skF_4', E_4454, '#skF_6')) | k2_partfun1(C_4450, '#skF_2', E_4454, k9_subset_1(A_4452, C_4450, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4452, C_4450, '#skF_4')) | ~m1_subset_1(E_4454, k1_zfmisc_1(k2_zfmisc_1(C_4450, '#skF_2'))) | ~v1_funct_2(E_4454, C_4450, '#skF_2') | ~v1_funct_1(E_4454) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4452)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_4450, k1_zfmisc_1(A_4452)) | v1_xboole_0(C_4450) | v1_xboole_0('#skF_2') | v1_xboole_0(A_4452))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_80806, c_111190])).
% 24.36/15.03  tff(c_116923, plain, (![A_4532, C_4533, E_4534]: (k2_partfun1(k4_subset_1(A_4532, C_4533, '#skF_4'), '#skF_2', k1_tmap_1(A_4532, '#skF_2', C_4533, '#skF_4', E_4534, '#skF_6'), C_4533)=E_4534 | ~v1_funct_1(k1_tmap_1(A_4532, '#skF_2', C_4533, '#skF_4', E_4534, '#skF_6')) | k2_partfun1(C_4533, '#skF_2', E_4534, k9_subset_1(A_4532, C_4533, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4532, C_4533, '#skF_4')) | ~m1_subset_1(E_4534, k1_zfmisc_1(k2_zfmisc_1(C_4533, '#skF_2'))) | ~v1_funct_2(E_4534, C_4533, '#skF_2') | ~v1_funct_1(E_4534) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4532)) | ~m1_subset_1(C_4533, k1_zfmisc_1(A_4532)) | v1_xboole_0(C_4533) | v1_xboole_0(A_4532))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_111199])).
% 24.36/15.03  tff(c_116930, plain, (![A_4532]: (k2_partfun1(k4_subset_1(A_4532, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4532, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4532, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_4532, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4532, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4532)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4532)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4532))), inference(resolution, [status(thm)], [c_76, c_116923])).
% 24.36/15.03  tff(c_116943, plain, (![A_4532]: (k2_partfun1(k4_subset_1(A_4532, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4532, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4532, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4532, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4532, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4532)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4532)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4532))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_80809, c_116930])).
% 24.36/15.03  tff(c_117294, plain, (![A_4540]: (k2_partfun1(k4_subset_1(A_4540, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4540, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4540, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4540, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4540, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4540)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4540)) | v1_xboole_0(A_4540))), inference(negUnitSimplification, [status(thm)], [c_90, c_116943])).
% 24.36/15.03  tff(c_58833, plain, (![B_2706, A_2707]: (k1_relat_1(B_2706)=A_2707 | ~v1_partfun1(B_2706, A_2707) | ~v4_relat_1(B_2706, A_2707) | ~v1_relat_1(B_2706))), inference(cnfTransformation, [status(thm)], [f_129])).
% 24.36/15.03  tff(c_58842, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58357, c_58833])).
% 24.36/15.03  tff(c_58851, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_58842])).
% 24.36/15.03  tff(c_59657, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_58851])).
% 24.36/15.03  tff(c_60027, plain, (![C_2805, A_2806, B_2807]: (v1_partfun1(C_2805, A_2806) | ~v1_funct_2(C_2805, A_2806, B_2807) | ~v1_funct_1(C_2805) | ~m1_subset_1(C_2805, k1_zfmisc_1(k2_zfmisc_1(A_2806, B_2807))) | v1_xboole_0(B_2807))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.36/15.03  tff(c_60030, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_60027])).
% 24.36/15.03  tff(c_60040, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_60030])).
% 24.36/15.03  tff(c_60042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_59657, c_60040])).
% 24.36/15.03  tff(c_60043, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_58851])).
% 24.36/15.03  tff(c_60060, plain, (![A_16]: (r1_xboole_0('#skF_4', A_16) | k9_relat_1('#skF_6', A_16)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_60043, c_20])).
% 24.36/15.03  tff(c_60126, plain, (![A_2809]: (r1_xboole_0('#skF_4', A_2809) | k9_relat_1('#skF_6', A_2809)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_60060])).
% 24.36/15.03  tff(c_60149, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_60126, c_58407])).
% 24.36/15.03  tff(c_61675, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60149])).
% 24.36/15.03  tff(c_58839, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58358, c_58833])).
% 24.36/15.03  tff(c_58848, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_58839])).
% 24.36/15.03  tff(c_58858, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_58848])).
% 24.36/15.03  tff(c_59595, plain, (![C_2775, A_2776, B_2777]: (v1_partfun1(C_2775, A_2776) | ~v1_funct_2(C_2775, A_2776, B_2777) | ~v1_funct_1(C_2775) | ~m1_subset_1(C_2775, k1_zfmisc_1(k2_zfmisc_1(A_2776, B_2777))) | v1_xboole_0(B_2777))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.36/15.03  tff(c_59601, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_59595])).
% 24.36/15.03  tff(c_59612, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_59601])).
% 24.36/15.03  tff(c_59614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_58858, c_59612])).
% 24.36/15.03  tff(c_59615, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_58848])).
% 24.36/15.03  tff(c_59620, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_28) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_59615, c_32])).
% 24.36/15.03  tff(c_60317, plain, (![A_2823]: (k7_relat_1('#skF_5', A_2823)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_2823))), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_59620])).
% 24.36/15.03  tff(c_60324, plain, (![B_31]: (k7_relat_1('#skF_5', B_31)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_31) | v1_xboole_0(B_31) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_60317])).
% 24.36/15.03  tff(c_61490, plain, (![B_2923]: (k7_relat_1('#skF_5', B_2923)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_2923) | v1_xboole_0(B_2923))), inference(negUnitSimplification, [status(thm)], [c_90, c_60324])).
% 24.36/15.03  tff(c_61496, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_61490])).
% 24.36/15.03  tff(c_61500, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_61496])).
% 24.36/15.03  tff(c_59623, plain, (![A_28]: (r1_xboole_0('#skF_3', A_28) | k7_relat_1('#skF_5', A_28)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_59615, c_34])).
% 24.36/15.03  tff(c_60334, plain, (![A_2824]: (r1_xboole_0('#skF_3', A_2824) | k7_relat_1('#skF_5', A_2824)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_59623])).
% 24.36/15.03  tff(c_59629, plain, (![A_16]: (k9_relat_1('#skF_5', A_16)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_16) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_59615, c_18])).
% 24.36/15.03  tff(c_59648, plain, (![A_16]: (k9_relat_1('#skF_5', A_16)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_59629])).
% 24.36/15.03  tff(c_60360, plain, (![A_2824]: (k9_relat_1('#skF_5', A_2824)=k1_xboole_0 | k7_relat_1('#skF_5', A_2824)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_60334, c_59648])).
% 24.36/15.03  tff(c_59632, plain, (![A_16]: (r1_xboole_0('#skF_3', A_16) | k9_relat_1('#skF_5', A_16)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_59615, c_20])).
% 24.36/15.03  tff(c_59650, plain, (![A_16]: (r1_xboole_0('#skF_3', A_16) | k9_relat_1('#skF_5', A_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_59632])).
% 24.36/15.03  tff(c_60063, plain, (![B_25]: (k7_relat_1('#skF_6', B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_60043, c_24])).
% 24.36/15.03  tff(c_60403, plain, (![B_2828]: (k7_relat_1('#skF_6', B_2828)=k1_xboole_0 | ~r1_xboole_0(B_2828, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_60063])).
% 24.36/15.03  tff(c_60445, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59650, c_60403])).
% 24.36/15.03  tff(c_61560, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60445])).
% 24.36/15.03  tff(c_61563, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_60360, c_61560])).
% 24.36/15.03  tff(c_61570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61500, c_61563])).
% 24.36/15.03  tff(c_61571, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60445])).
% 24.36/15.03  tff(c_60051, plain, (![A_28]: (r1_xboole_0('#skF_4', A_28) | k7_relat_1('#skF_6', A_28)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_60043, c_34])).
% 24.36/15.03  tff(c_60169, plain, (![A_2811]: (r1_xboole_0('#skF_4', A_2811) | k7_relat_1('#skF_6', A_2811)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_60051])).
% 24.36/15.03  tff(c_61793, plain, (![A_2949]: (k3_xboole_0('#skF_4', A_2949)=k1_xboole_0 | k7_relat_1('#skF_6', A_2949)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_60169, c_2])).
% 24.36/15.03  tff(c_61797, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_61571, c_61793])).
% 24.36/15.03  tff(c_60048, plain, (![A_28]: (k7_relat_1('#skF_6', A_28)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_28) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_60043, c_32])).
% 24.36/15.03  tff(c_60296, plain, (![A_2822]: (k7_relat_1('#skF_6', A_2822)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_2822))), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_60048])).
% 24.36/15.03  tff(c_61848, plain, (![B_2957]: (k7_relat_1('#skF_6', B_2957)=k1_xboole_0 | k3_xboole_0('#skF_4', B_2957)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_60296])).
% 24.36/15.03  tff(c_61866, plain, (![B_2957]: (r1_tarski(k1_relat_1(k1_xboole_0), B_2957) | ~v1_relat_1('#skF_6') | k3_xboole_0('#skF_4', B_2957)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61848, c_30])).
% 24.36/15.03  tff(c_61885, plain, (![B_2957]: (r1_tarski(k1_xboole_0, B_2957) | k3_xboole_0('#skF_4', B_2957)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_28, c_61866])).
% 24.36/15.03  tff(c_61590, plain, (![B_21]: (k9_relat_1(k1_xboole_0, B_21)=k9_relat_1('#skF_6', B_21) | ~r1_tarski(B_21, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_61571, c_22])).
% 24.36/15.03  tff(c_62147, plain, (![B_2972]: (k9_relat_1(k1_xboole_0, B_2972)=k9_relat_1('#skF_6', B_2972) | ~r1_tarski(B_2972, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58338, c_61590])).
% 24.36/15.03  tff(c_62151, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61885, c_62147])).
% 24.36/15.03  tff(c_62181, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61797, c_10420, c_62151])).
% 24.36/15.03  tff(c_62183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61675, c_62181])).
% 24.36/15.03  tff(c_62184, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60149])).
% 24.36/15.03  tff(c_58603, plain, (![B_2693, A_2694]: (r1_xboole_0(k1_relat_1(B_2693), A_2694) | k7_relat_1(B_2693, A_2694)!=k1_xboole_0 | ~v1_relat_1(B_2693))), inference(cnfTransformation, [status(thm)], [f_87])).
% 24.36/15.03  tff(c_58620, plain, (![A_2694]: (r1_xboole_0(k1_xboole_0, A_2694) | k7_relat_1(k1_xboole_0, A_2694)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_58603])).
% 24.36/15.03  tff(c_58626, plain, (![A_2694]: (r1_xboole_0(k1_xboole_0, A_2694) | k7_relat_1(k1_xboole_0, A_2694)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10421, c_58620])).
% 24.36/15.03  tff(c_60449, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_58626, c_60403])).
% 24.36/15.03  tff(c_62275, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62184, c_60449])).
% 24.36/15.03  tff(c_61572, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60445])).
% 24.36/15.03  tff(c_60252, plain, (![A_2820]: (r1_xboole_0('#skF_3', A_2820) | k9_relat_1('#skF_5', A_2820)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_59632])).
% 24.36/15.03  tff(c_61631, plain, (![A_2931]: (k3_xboole_0('#skF_3', A_2931)=k1_xboole_0 | k9_relat_1('#skF_5', A_2931)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_60252, c_2])).
% 24.36/15.03  tff(c_61651, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_61572, c_61631])).
% 24.36/15.03  tff(c_60199, plain, (![A_2812, B_2813, C_2814]: (k9_subset_1(A_2812, B_2813, C_2814)=k3_xboole_0(B_2813, C_2814) | ~m1_subset_1(C_2814, k1_zfmisc_1(A_2812)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.36/15.03  tff(c_60212, plain, (![B_2813]: (k9_subset_1('#skF_1', B_2813, '#skF_4')=k3_xboole_0(B_2813, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_60199])).
% 24.36/15.03  tff(c_60276, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_60252, c_58407])).
% 24.36/15.03  tff(c_60592, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60276])).
% 24.36/15.03  tff(c_60597, plain, (![B_2845]: (k7_relat_1('#skF_5', B_2845)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_2845) | v1_xboole_0(B_2845))), inference(negUnitSimplification, [status(thm)], [c_90, c_60324])).
% 24.36/15.03  tff(c_60600, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_60597])).
% 24.36/15.03  tff(c_60603, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_60600])).
% 24.36/15.03  tff(c_59644, plain, (![A_28]: (r1_xboole_0('#skF_3', A_28) | k7_relat_1('#skF_5', A_28)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_59623])).
% 24.36/15.03  tff(c_60444, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59644, c_60403])).
% 24.36/15.03  tff(c_60785, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60603, c_60444])).
% 24.36/15.03  tff(c_61065, plain, (![A_2889]: (k3_xboole_0('#skF_4', A_2889)=k1_xboole_0 | k7_relat_1('#skF_6', A_2889)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_60169, c_2])).
% 24.36/15.03  tff(c_61072, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_60785, c_61065])).
% 24.36/15.03  tff(c_59635, plain, (![B_25]: (k7_relat_1('#skF_5', B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_59615, c_24])).
% 24.36/15.03  tff(c_60093, plain, (![B_2808]: (k7_relat_1('#skF_5', B_2808)=k1_xboole_0 | ~r1_xboole_0(B_2808, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_59635])).
% 24.36/15.03  tff(c_61080, plain, (![A_2895]: (k7_relat_1('#skF_5', A_2895)=k1_xboole_0 | k3_xboole_0(A_2895, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_60093])).
% 24.36/15.03  tff(c_61101, plain, (![A_2895]: (r1_tarski(k1_relat_1(k1_xboole_0), A_2895) | ~v1_relat_1('#skF_5') | k3_xboole_0(A_2895, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61080, c_30])).
% 24.36/15.03  tff(c_61121, plain, (![A_2895]: (r1_tarski(k1_xboole_0, A_2895) | k3_xboole_0(A_2895, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_28, c_61101])).
% 24.36/15.03  tff(c_60610, plain, (![B_21]: (k9_relat_1(k1_xboole_0, B_21)=k9_relat_1('#skF_5', B_21) | ~r1_tarski(B_21, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_60603, c_22])).
% 24.36/15.03  tff(c_61266, plain, (![B_2907]: (k9_relat_1(k1_xboole_0, B_2907)=k9_relat_1('#skF_5', B_2907) | ~r1_tarski(B_2907, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58339, c_60610])).
% 24.36/15.03  tff(c_61274, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61121, c_61266])).
% 24.36/15.03  tff(c_61303, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61072, c_10420, c_61274])).
% 24.36/15.03  tff(c_61305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60592, c_61303])).
% 24.36/15.03  tff(c_61307, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_60276])).
% 24.36/15.03  tff(c_60329, plain, (![A_16]: (k7_relat_1('#skF_5', A_16)=k1_xboole_0 | k9_relat_1('#skF_5', A_16)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_59650, c_60317])).
% 24.36/15.03  tff(c_61372, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_61307, c_60329])).
% 24.36/15.03  tff(c_61308, plain, (![C_2908, E_2912, B_2913, F_2911, A_2910, D_2909]: (v1_funct_1(k1_tmap_1(A_2910, B_2913, C_2908, D_2909, E_2912, F_2911)) | ~m1_subset_1(F_2911, k1_zfmisc_1(k2_zfmisc_1(D_2909, B_2913))) | ~v1_funct_2(F_2911, D_2909, B_2913) | ~v1_funct_1(F_2911) | ~m1_subset_1(E_2912, k1_zfmisc_1(k2_zfmisc_1(C_2908, B_2913))) | ~v1_funct_2(E_2912, C_2908, B_2913) | ~v1_funct_1(E_2912) | ~m1_subset_1(D_2909, k1_zfmisc_1(A_2910)) | v1_xboole_0(D_2909) | ~m1_subset_1(C_2908, k1_zfmisc_1(A_2910)) | v1_xboole_0(C_2908) | v1_xboole_0(B_2913) | v1_xboole_0(A_2910))), inference(cnfTransformation, [status(thm)], [f_217])).
% 24.36/15.03  tff(c_61310, plain, (![A_2910, C_2908, E_2912]: (v1_funct_1(k1_tmap_1(A_2910, '#skF_2', C_2908, '#skF_4', E_2912, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2912, k1_zfmisc_1(k2_zfmisc_1(C_2908, '#skF_2'))) | ~v1_funct_2(E_2912, C_2908, '#skF_2') | ~v1_funct_1(E_2912) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2910)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2908, k1_zfmisc_1(A_2910)) | v1_xboole_0(C_2908) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2910))), inference(resolution, [status(thm)], [c_70, c_61308])).
% 24.36/15.03  tff(c_61318, plain, (![A_2910, C_2908, E_2912]: (v1_funct_1(k1_tmap_1(A_2910, '#skF_2', C_2908, '#skF_4', E_2912, '#skF_6')) | ~m1_subset_1(E_2912, k1_zfmisc_1(k2_zfmisc_1(C_2908, '#skF_2'))) | ~v1_funct_2(E_2912, C_2908, '#skF_2') | ~v1_funct_1(E_2912) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2910)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2908, k1_zfmisc_1(A_2910)) | v1_xboole_0(C_2908) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2910))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_61310])).
% 24.36/15.03  tff(c_62977, plain, (![A_3013, C_3014, E_3015]: (v1_funct_1(k1_tmap_1(A_3013, '#skF_2', C_3014, '#skF_4', E_3015, '#skF_6')) | ~m1_subset_1(E_3015, k1_zfmisc_1(k2_zfmisc_1(C_3014, '#skF_2'))) | ~v1_funct_2(E_3015, C_3014, '#skF_2') | ~v1_funct_1(E_3015) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3013)) | ~m1_subset_1(C_3014, k1_zfmisc_1(A_3013)) | v1_xboole_0(C_3014) | v1_xboole_0(A_3013))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_61318])).
% 24.36/15.03  tff(c_62984, plain, (![A_3013]: (v1_funct_1(k1_tmap_1(A_3013, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3013)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3013)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3013))), inference(resolution, [status(thm)], [c_76, c_62977])).
% 24.36/15.03  tff(c_62997, plain, (![A_3013]: (v1_funct_1(k1_tmap_1(A_3013, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3013)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3013)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3013))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_62984])).
% 24.36/15.03  tff(c_63490, plain, (![A_3037]: (v1_funct_1(k1_tmap_1(A_3037, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3037)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3037)) | v1_xboole_0(A_3037))), inference(negUnitSimplification, [status(thm)], [c_90, c_62997])).
% 24.36/15.03  tff(c_63493, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_63490])).
% 24.36/15.03  tff(c_63496, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_63493])).
% 24.36/15.03  tff(c_63497, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_94, c_63496])).
% 24.36/15.03  tff(c_60504, plain, (![A_2832, B_2833, C_2834, D_2835]: (k2_partfun1(A_2832, B_2833, C_2834, D_2835)=k7_relat_1(C_2834, D_2835) | ~m1_subset_1(C_2834, k1_zfmisc_1(k2_zfmisc_1(A_2832, B_2833))) | ~v1_funct_1(C_2834))), inference(cnfTransformation, [status(thm)], [f_135])).
% 24.36/15.03  tff(c_60508, plain, (![D_2835]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_2835)=k7_relat_1('#skF_5', D_2835) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_60504])).
% 24.36/15.03  tff(c_60517, plain, (![D_2835]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_2835)=k7_relat_1('#skF_5', D_2835))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_60508])).
% 24.36/15.03  tff(c_60506, plain, (![D_2835]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_2835)=k7_relat_1('#skF_6', D_2835) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_60504])).
% 24.36/15.03  tff(c_60514, plain, (![D_2835]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_2835)=k7_relat_1('#skF_6', D_2835))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60506])).
% 24.36/15.03  tff(c_61663, plain, (![C_2934, B_2937, E_2932, A_2933, D_2935, F_2936]: (k2_partfun1(k4_subset_1(A_2933, C_2934, D_2935), B_2937, k1_tmap_1(A_2933, B_2937, C_2934, D_2935, E_2932, F_2936), D_2935)=F_2936 | ~m1_subset_1(k1_tmap_1(A_2933, B_2937, C_2934, D_2935, E_2932, F_2936), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2933, C_2934, D_2935), B_2937))) | ~v1_funct_2(k1_tmap_1(A_2933, B_2937, C_2934, D_2935, E_2932, F_2936), k4_subset_1(A_2933, C_2934, D_2935), B_2937) | ~v1_funct_1(k1_tmap_1(A_2933, B_2937, C_2934, D_2935, E_2932, F_2936)) | k2_partfun1(D_2935, B_2937, F_2936, k9_subset_1(A_2933, C_2934, D_2935))!=k2_partfun1(C_2934, B_2937, E_2932, k9_subset_1(A_2933, C_2934, D_2935)) | ~m1_subset_1(F_2936, k1_zfmisc_1(k2_zfmisc_1(D_2935, B_2937))) | ~v1_funct_2(F_2936, D_2935, B_2937) | ~v1_funct_1(F_2936) | ~m1_subset_1(E_2932, k1_zfmisc_1(k2_zfmisc_1(C_2934, B_2937))) | ~v1_funct_2(E_2932, C_2934, B_2937) | ~v1_funct_1(E_2932) | ~m1_subset_1(D_2935, k1_zfmisc_1(A_2933)) | v1_xboole_0(D_2935) | ~m1_subset_1(C_2934, k1_zfmisc_1(A_2933)) | v1_xboole_0(C_2934) | v1_xboole_0(B_2937) | v1_xboole_0(A_2933))), inference(cnfTransformation, [status(thm)], [f_183])).
% 24.36/15.03  tff(c_70550, plain, (![B_3247, F_3245, C_3242, E_3246, A_3244, D_3243]: (k2_partfun1(k4_subset_1(A_3244, C_3242, D_3243), B_3247, k1_tmap_1(A_3244, B_3247, C_3242, D_3243, E_3246, F_3245), D_3243)=F_3245 | ~v1_funct_2(k1_tmap_1(A_3244, B_3247, C_3242, D_3243, E_3246, F_3245), k4_subset_1(A_3244, C_3242, D_3243), B_3247) | ~v1_funct_1(k1_tmap_1(A_3244, B_3247, C_3242, D_3243, E_3246, F_3245)) | k2_partfun1(D_3243, B_3247, F_3245, k9_subset_1(A_3244, C_3242, D_3243))!=k2_partfun1(C_3242, B_3247, E_3246, k9_subset_1(A_3244, C_3242, D_3243)) | ~m1_subset_1(F_3245, k1_zfmisc_1(k2_zfmisc_1(D_3243, B_3247))) | ~v1_funct_2(F_3245, D_3243, B_3247) | ~v1_funct_1(F_3245) | ~m1_subset_1(E_3246, k1_zfmisc_1(k2_zfmisc_1(C_3242, B_3247))) | ~v1_funct_2(E_3246, C_3242, B_3247) | ~v1_funct_1(E_3246) | ~m1_subset_1(D_3243, k1_zfmisc_1(A_3244)) | v1_xboole_0(D_3243) | ~m1_subset_1(C_3242, k1_zfmisc_1(A_3244)) | v1_xboole_0(C_3242) | v1_xboole_0(B_3247) | v1_xboole_0(A_3244))), inference(resolution, [status(thm)], [c_62, c_61663])).
% 24.36/15.03  tff(c_76597, plain, (![C_3346, A_3348, E_3350, D_3347, F_3349, B_3351]: (k2_partfun1(k4_subset_1(A_3348, C_3346, D_3347), B_3351, k1_tmap_1(A_3348, B_3351, C_3346, D_3347, E_3350, F_3349), D_3347)=F_3349 | ~v1_funct_1(k1_tmap_1(A_3348, B_3351, C_3346, D_3347, E_3350, F_3349)) | k2_partfun1(D_3347, B_3351, F_3349, k9_subset_1(A_3348, C_3346, D_3347))!=k2_partfun1(C_3346, B_3351, E_3350, k9_subset_1(A_3348, C_3346, D_3347)) | ~m1_subset_1(F_3349, k1_zfmisc_1(k2_zfmisc_1(D_3347, B_3351))) | ~v1_funct_2(F_3349, D_3347, B_3351) | ~v1_funct_1(F_3349) | ~m1_subset_1(E_3350, k1_zfmisc_1(k2_zfmisc_1(C_3346, B_3351))) | ~v1_funct_2(E_3350, C_3346, B_3351) | ~v1_funct_1(E_3350) | ~m1_subset_1(D_3347, k1_zfmisc_1(A_3348)) | v1_xboole_0(D_3347) | ~m1_subset_1(C_3346, k1_zfmisc_1(A_3348)) | v1_xboole_0(C_3346) | v1_xboole_0(B_3351) | v1_xboole_0(A_3348))), inference(resolution, [status(thm)], [c_64, c_70550])).
% 24.36/15.03  tff(c_76601, plain, (![A_3348, C_3346, E_3350]: (k2_partfun1(k4_subset_1(A_3348, C_3346, '#skF_4'), '#skF_2', k1_tmap_1(A_3348, '#skF_2', C_3346, '#skF_4', E_3350, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3348, '#skF_2', C_3346, '#skF_4', E_3350, '#skF_6')) | k2_partfun1(C_3346, '#skF_2', E_3350, k9_subset_1(A_3348, C_3346, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_3348, C_3346, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3350, k1_zfmisc_1(k2_zfmisc_1(C_3346, '#skF_2'))) | ~v1_funct_2(E_3350, C_3346, '#skF_2') | ~v1_funct_1(E_3350) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3348)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3346, k1_zfmisc_1(A_3348)) | v1_xboole_0(C_3346) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3348))), inference(resolution, [status(thm)], [c_70, c_76597])).
% 24.36/15.03  tff(c_76610, plain, (![A_3348, C_3346, E_3350]: (k2_partfun1(k4_subset_1(A_3348, C_3346, '#skF_4'), '#skF_2', k1_tmap_1(A_3348, '#skF_2', C_3346, '#skF_4', E_3350, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3348, '#skF_2', C_3346, '#skF_4', E_3350, '#skF_6')) | k2_partfun1(C_3346, '#skF_2', E_3350, k9_subset_1(A_3348, C_3346, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3348, C_3346, '#skF_4')) | ~m1_subset_1(E_3350, k1_zfmisc_1(k2_zfmisc_1(C_3346, '#skF_2'))) | ~v1_funct_2(E_3350, C_3346, '#skF_2') | ~v1_funct_1(E_3350) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3348)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3346, k1_zfmisc_1(A_3348)) | v1_xboole_0(C_3346) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3348))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_60514, c_76601])).
% 24.36/15.03  tff(c_76966, plain, (![A_3354, C_3355, E_3356]: (k2_partfun1(k4_subset_1(A_3354, C_3355, '#skF_4'), '#skF_2', k1_tmap_1(A_3354, '#skF_2', C_3355, '#skF_4', E_3356, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3354, '#skF_2', C_3355, '#skF_4', E_3356, '#skF_6')) | k2_partfun1(C_3355, '#skF_2', E_3356, k9_subset_1(A_3354, C_3355, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3354, C_3355, '#skF_4')) | ~m1_subset_1(E_3356, k1_zfmisc_1(k2_zfmisc_1(C_3355, '#skF_2'))) | ~v1_funct_2(E_3356, C_3355, '#skF_2') | ~v1_funct_1(E_3356) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3354)) | ~m1_subset_1(C_3355, k1_zfmisc_1(A_3354)) | v1_xboole_0(C_3355) | v1_xboole_0(A_3354))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_76610])).
% 24.36/15.03  tff(c_76973, plain, (![A_3354]: (k2_partfun1(k4_subset_1(A_3354, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3354, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3354, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_3354, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3354, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3354)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3354)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3354))), inference(resolution, [status(thm)], [c_76, c_76966])).
% 24.36/15.03  tff(c_76986, plain, (![A_3354]: (k2_partfun1(k4_subset_1(A_3354, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3354, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3354, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_3354, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3354, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3354)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3354)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3354))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_60517, c_76973])).
% 24.36/15.03  tff(c_78526, plain, (![A_3385]: (k2_partfun1(k4_subset_1(A_3385, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3385, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3385, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_3385, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3385, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3385)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3385)) | v1_xboole_0(A_3385))), inference(negUnitSimplification, [status(thm)], [c_90, c_76986])).
% 24.36/15.03  tff(c_4522, plain, (![C_606, A_607, B_608]: (v1_relat_1(C_606) | ~m1_subset_1(C_606, k1_zfmisc_1(k2_zfmisc_1(A_607, B_608))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.36/15.03  tff(c_4533, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_4522])).
% 24.36/15.03  tff(c_4553, plain, (![C_615, A_616, B_617]: (v4_relat_1(C_615, A_616) | ~m1_subset_1(C_615, k1_zfmisc_1(k2_zfmisc_1(A_616, B_617))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 24.36/15.03  tff(c_4564, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_4553])).
% 24.36/15.03  tff(c_5063, plain, (![B_664, A_665]: (k1_relat_1(B_664)=A_665 | ~v1_partfun1(B_664, A_665) | ~v4_relat_1(B_664, A_665) | ~v1_relat_1(B_664))), inference(cnfTransformation, [status(thm)], [f_129])).
% 24.36/15.03  tff(c_5072, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4564, c_5063])).
% 24.36/15.03  tff(c_5081, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_5072])).
% 24.36/15.03  tff(c_5730, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_5081])).
% 24.36/15.03  tff(c_6007, plain, (![C_739, A_740, B_741]: (v1_partfun1(C_739, A_740) | ~v1_funct_2(C_739, A_740, B_741) | ~v1_funct_1(C_739) | ~m1_subset_1(C_739, k1_zfmisc_1(k2_zfmisc_1(A_740, B_741))) | v1_xboole_0(B_741))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.36/15.03  tff(c_6010, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_6007])).
% 24.36/15.03  tff(c_6020, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_6010])).
% 24.36/15.03  tff(c_6022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_5730, c_6020])).
% 24.36/15.03  tff(c_6023, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_5081])).
% 24.36/15.03  tff(c_6037, plain, (![A_16]: (r1_xboole_0('#skF_4', A_16) | k9_relat_1('#skF_6', A_16)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6023, c_20])).
% 24.36/15.03  tff(c_6150, plain, (![A_746]: (r1_xboole_0('#skF_4', A_746) | k9_relat_1('#skF_6', A_746)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_6037])).
% 24.36/15.03  tff(c_120, plain, (![A_245]: (k9_relat_1(A_245, k1_relat_1(A_245))=k2_relat_1(A_245) | ~v1_relat_1(A_245))), inference(cnfTransformation, [status(thm)], [f_54])).
% 24.36/15.03  tff(c_129, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_120])).
% 24.36/15.03  tff(c_132, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_129])).
% 24.36/15.03  tff(c_133, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_132])).
% 24.36/15.03  tff(c_134, plain, (![C_246, A_247, B_248]: (v1_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.36/15.03  tff(c_144, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_134])).
% 24.36/15.03  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_144])).
% 24.36/15.03  tff(c_152, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_132])).
% 24.36/15.03  tff(c_4567, plain, (![A_618, B_619]: (k7_relat_1(A_618, B_619)=k1_xboole_0 | ~r1_xboole_0(B_619, k1_relat_1(A_618)) | ~v1_relat_1(A_618))), inference(cnfTransformation, [status(thm)], [f_74])).
% 24.36/15.03  tff(c_4574, plain, (![B_619]: (k7_relat_1(k1_xboole_0, B_619)=k1_xboole_0 | ~r1_xboole_0(B_619, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4567])).
% 24.36/15.03  tff(c_4577, plain, (![B_619]: (k7_relat_1(k1_xboole_0, B_619)=k1_xboole_0 | ~r1_xboole_0(B_619, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_4574])).
% 24.36/15.03  tff(c_6178, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_6150, c_4577])).
% 24.36/15.03  tff(c_8280, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6178])).
% 24.36/15.03  tff(c_4534, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_4522])).
% 24.36/15.03  tff(c_4565, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_4553])).
% 24.36/15.03  tff(c_5066, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4565, c_5063])).
% 24.36/15.03  tff(c_5075, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_5066])).
% 24.36/15.03  tff(c_5088, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_5075])).
% 24.36/15.03  tff(c_5655, plain, (![C_715, A_716, B_717]: (v1_partfun1(C_715, A_716) | ~v1_funct_2(C_715, A_716, B_717) | ~v1_funct_1(C_715) | ~m1_subset_1(C_715, k1_zfmisc_1(k2_zfmisc_1(A_716, B_717))) | v1_xboole_0(B_717))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.36/15.03  tff(c_5661, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_5655])).
% 24.36/15.03  tff(c_5672, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_5661])).
% 24.36/15.03  tff(c_5674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_5088, c_5672])).
% 24.36/15.03  tff(c_5675, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_5075])).
% 24.36/15.03  tff(c_5680, plain, (![A_16]: (k9_relat_1('#skF_5', A_16)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_16) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5675, c_18])).
% 24.36/15.03  tff(c_6246, plain, (![A_751]: (k9_relat_1('#skF_5', A_751)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_751))), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_5680])).
% 24.36/15.03  tff(c_6253, plain, (![B_31]: (k9_relat_1('#skF_5', B_31)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_31) | v1_xboole_0(B_31) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_6246])).
% 24.36/15.03  tff(c_6311, plain, (![B_753]: (k9_relat_1('#skF_5', B_753)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_753) | v1_xboole_0(B_753))), inference(negUnitSimplification, [status(thm)], [c_90, c_6253])).
% 24.36/15.03  tff(c_6314, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_6311])).
% 24.36/15.03  tff(c_6317, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_6314])).
% 24.36/15.03  tff(c_5689, plain, (![A_16]: (r1_xboole_0('#skF_3', A_16) | k9_relat_1('#skF_5', A_16)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5675, c_20])).
% 24.36/15.03  tff(c_6360, plain, (![A_756]: (r1_xboole_0('#skF_3', A_756) | k9_relat_1('#skF_5', A_756)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_5689])).
% 24.36/15.03  tff(c_6043, plain, (![B_25]: (k7_relat_1('#skF_6', B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6023, c_24])).
% 24.36/15.03  tff(c_6060, plain, (![B_25]: (k7_relat_1('#skF_6', B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_6043])).
% 24.36/15.03  tff(c_6374, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6360, c_6060])).
% 24.36/15.03  tff(c_6395, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6317, c_6374])).
% 24.36/15.03  tff(c_6031, plain, (![A_28]: (r1_xboole_0('#skF_4', A_28) | k7_relat_1('#skF_6', A_28)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6023, c_34])).
% 24.36/15.03  tff(c_6216, plain, (![A_750]: (r1_xboole_0('#skF_4', A_750) | k7_relat_1('#skF_6', A_750)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_6031])).
% 24.36/15.03  tff(c_8108, plain, (![A_882]: (k3_xboole_0('#skF_4', A_882)=k1_xboole_0 | k7_relat_1('#skF_6', A_882)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6216, c_2])).
% 24.36/15.03  tff(c_8112, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6395, c_8108])).
% 24.36/15.03  tff(c_151, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_132])).
% 24.36/15.03  tff(c_6040, plain, (![A_28]: (k7_relat_1('#skF_6', A_28)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_28) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6023, c_32])).
% 24.36/15.03  tff(c_6137, plain, (![A_745]: (k7_relat_1('#skF_6', A_745)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_745))), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_6040])).
% 24.36/15.03  tff(c_8425, plain, (![B_910]: (k7_relat_1('#skF_6', B_910)=k1_xboole_0 | k3_xboole_0('#skF_4', B_910)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_6137])).
% 24.36/15.03  tff(c_8449, plain, (![B_910]: (r1_tarski(k1_relat_1(k1_xboole_0), B_910) | ~v1_relat_1('#skF_6') | k3_xboole_0('#skF_4', B_910)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8425, c_30])).
% 24.36/15.03  tff(c_8470, plain, (![B_910]: (r1_tarski(k1_xboole_0, B_910) | k3_xboole_0('#skF_4', B_910)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_28, c_8449])).
% 24.36/15.03  tff(c_6405, plain, (![B_21]: (k9_relat_1(k1_xboole_0, B_21)=k9_relat_1('#skF_6', B_21) | ~r1_tarski(B_21, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6395, c_22])).
% 24.36/15.03  tff(c_8693, plain, (![B_923]: (k9_relat_1(k1_xboole_0, B_923)=k9_relat_1('#skF_6', B_923) | ~r1_tarski(B_923, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_6405])).
% 24.36/15.03  tff(c_8697, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_6', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8470, c_8693])).
% 24.36/15.03  tff(c_8727, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8112, c_151, c_8697])).
% 24.36/15.03  tff(c_8729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8280, c_8727])).
% 24.36/15.03  tff(c_8730, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6178])).
% 24.36/15.03  tff(c_4759, plain, (![B_644, A_645]: (r1_xboole_0(k1_relat_1(B_644), A_645) | k7_relat_1(B_644, A_645)!=k1_xboole_0 | ~v1_relat_1(B_644))), inference(cnfTransformation, [status(thm)], [f_87])).
% 24.36/15.03  tff(c_4779, plain, (![A_645]: (r1_xboole_0(k1_xboole_0, A_645) | k7_relat_1(k1_xboole_0, A_645)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4759])).
% 24.36/15.03  tff(c_4786, plain, (![A_645]: (r1_xboole_0(k1_xboole_0, A_645) | k7_relat_1(k1_xboole_0, A_645)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_4779])).
% 24.36/15.03  tff(c_6078, plain, (![B_743]: (k7_relat_1('#skF_6', B_743)=k1_xboole_0 | ~r1_xboole_0(B_743, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_6043])).
% 24.36/15.03  tff(c_6103, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4786, c_6078])).
% 24.36/15.03  tff(c_8817, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8730, c_6103])).
% 24.36/15.03  tff(c_6416, plain, (![A_757, B_758, C_759, D_760]: (k2_partfun1(A_757, B_758, C_759, D_760)=k7_relat_1(C_759, D_760) | ~m1_subset_1(C_759, k1_zfmisc_1(k2_zfmisc_1(A_757, B_758))) | ~v1_funct_1(C_759))), inference(cnfTransformation, [status(thm)], [f_135])).
% 24.36/15.03  tff(c_6418, plain, (![D_760]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_760)=k7_relat_1('#skF_6', D_760) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_6416])).
% 24.36/15.03  tff(c_6426, plain, (![D_760]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_760)=k7_relat_1('#skF_6', D_760))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6418])).
% 24.36/15.03  tff(c_4861, plain, (![B_650, A_651]: (k9_relat_1(B_650, A_651)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_650), A_651) | ~v1_relat_1(B_650))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.36/15.03  tff(c_4878, plain, (![A_651]: (k9_relat_1(k1_xboole_0, A_651)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_651) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4861])).
% 24.36/15.03  tff(c_4885, plain, (![A_652]: (k9_relat_1(k1_xboole_0, A_652)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_652))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_4878])).
% 24.36/15.03  tff(c_4900, plain, (![A_645]: (k9_relat_1(k1_xboole_0, A_645)=k1_xboole_0 | k7_relat_1(k1_xboole_0, A_645)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4786, c_4885])).
% 24.36/15.03  tff(c_4641, plain, (![B_630, A_631]: (r1_xboole_0(k1_relat_1(B_630), A_631) | k9_relat_1(B_630, A_631)!=k1_xboole_0 | ~v1_relat_1(B_630))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.36/15.03  tff(c_4661, plain, (![A_631]: (r1_xboole_0(k1_xboole_0, A_631) | k9_relat_1(k1_xboole_0, A_631)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_4641])).
% 24.36/15.03  tff(c_4668, plain, (![A_631]: (r1_xboole_0(k1_xboole_0, A_631) | k9_relat_1(k1_xboole_0, A_631)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_4661])).
% 24.36/15.03  tff(c_5695, plain, (![B_25]: (k7_relat_1('#skF_5', B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5675, c_24])).
% 24.36/15.03  tff(c_6263, plain, (![B_752]: (k7_relat_1('#skF_5', B_752)=k1_xboole_0 | ~r1_xboole_0(B_752, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_5695])).
% 24.36/15.03  tff(c_6305, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4668, c_6263])).
% 24.36/15.03  tff(c_6625, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6305])).
% 24.36/15.03  tff(c_6633, plain, (k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4900, c_6625])).
% 24.36/15.03  tff(c_6399, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_6360, c_4577])).
% 24.36/15.03  tff(c_7459, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6633, c_6399])).
% 24.36/15.03  tff(c_7477, plain, (![A_843]: (k3_xboole_0('#skF_4', A_843)=k1_xboole_0 | k7_relat_1('#skF_6', A_843)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6216, c_2])).
% 24.36/15.03  tff(c_7489, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6395, c_7477])).
% 24.36/15.03  tff(c_6885, plain, (![A_807]: (k7_relat_1('#skF_5', A_807)=k1_xboole_0 | k3_xboole_0(A_807, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_6263])).
% 24.36/15.03  tff(c_6903, plain, (![A_807]: (r1_tarski(k1_relat_1(k1_xboole_0), A_807) | ~v1_relat_1('#skF_5') | k3_xboole_0(A_807, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6885, c_30])).
% 24.36/15.03  tff(c_6920, plain, (![A_807]: (r1_tarski(k1_xboole_0, A_807) | k3_xboole_0(A_807, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_28, c_6903])).
% 24.36/15.03  tff(c_5692, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_28) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5675, c_32])).
% 24.36/15.03  tff(c_5710, plain, (![A_28]: (k7_relat_1('#skF_5', A_28)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_28))), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_5692])).
% 24.36/15.03  tff(c_6540, plain, (![A_771]: (k7_relat_1('#skF_5', A_771)=k1_xboole_0 | k9_relat_1('#skF_5', A_771)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6360, c_5710])).
% 24.36/15.03  tff(c_6555, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6317, c_6540])).
% 24.36/15.03  tff(c_6561, plain, (![B_21]: (k9_relat_1(k1_xboole_0, B_21)=k9_relat_1('#skF_5', B_21) | ~r1_tarski(B_21, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6555, c_22])).
% 24.36/15.03  tff(c_7816, plain, (![B_864]: (k9_relat_1(k1_xboole_0, B_864)=k9_relat_1('#skF_5', B_864) | ~r1_tarski(B_864, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_6561])).
% 24.36/15.03  tff(c_7824, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1('#skF_5', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6920, c_7816])).
% 24.36/15.03  tff(c_7853, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7489, c_151, c_7824])).
% 24.36/15.03  tff(c_7855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7459, c_7853])).
% 24.36/15.03  tff(c_7856, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_6305])).
% 24.36/15.03  tff(c_6420, plain, (![D_760]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_760)=k7_relat_1('#skF_5', D_760) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_6416])).
% 24.36/15.03  tff(c_6429, plain, (![D_760]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_760)=k7_relat_1('#skF_5', D_760))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6420])).
% 24.36/15.03  tff(c_7949, plain, (![A_871]: (k3_xboole_0('#skF_3', A_871)=k1_xboole_0 | k9_relat_1('#skF_5', A_871)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6360, c_2])).
% 24.36/15.03  tff(c_7964, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6317, c_7949])).
% 24.36/15.03  tff(c_4954, plain, (![A_655, B_656, C_657]: (k9_subset_1(A_655, B_656, C_657)=k3_xboole_0(B_656, C_657) | ~m1_subset_1(C_657, k1_zfmisc_1(A_655)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.36/15.03  tff(c_4967, plain, (![B_656]: (k9_subset_1('#skF_1', B_656, '#skF_4')=k3_xboole_0(B_656, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_4954])).
% 24.36/15.03  tff(c_68, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 24.36/15.03  tff(c_119, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 24.36/15.03  tff(c_4970, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4967, c_4967, c_119])).
% 24.36/15.03  tff(c_10382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8817, c_6426, c_7856, c_6429, c_7964, c_7964, c_4970])).
% 24.36/15.03  tff(c_10383, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_68])).
% 24.36/15.03  tff(c_58460, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_10383])).
% 24.36/15.03  tff(c_78537, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78526, c_58460])).
% 24.36/15.03  tff(c_78551, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_62275, c_61651, c_60212, c_61372, c_61651, c_60212, c_63497, c_78537])).
% 24.36/15.03  tff(c_78553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_78551])).
% 24.36/15.03  tff(c_78554, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_10383])).
% 24.36/15.03  tff(c_117306, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117294, c_78554])).
% 24.36/15.03  tff(c_117320, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_84247, c_81312, c_80449, c_82929, c_81312, c_80449, c_85156, c_117306])).
% 24.36/15.03  tff(c_117322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_117320])).
% 24.36/15.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.36/15.03  
% 24.36/15.03  Inference rules
% 24.36/15.03  ----------------------
% 24.36/15.03  #Ref     : 0
% 24.36/15.03  #Sup     : 23737
% 24.36/15.03  #Fact    : 0
% 24.36/15.03  #Define  : 0
% 24.36/15.03  #Split   : 131
% 24.36/15.03  #Chain   : 0
% 24.36/15.03  #Close   : 0
% 24.36/15.03  
% 24.36/15.03  Ordering : KBO
% 24.36/15.03  
% 24.36/15.03  Simplification rules
% 24.36/15.03  ----------------------
% 24.36/15.03  #Subsume      : 3570
% 24.36/15.03  #Demod        : 49116
% 24.36/15.03  #Tautology    : 13771
% 24.36/15.03  #SimpNegUnit  : 1077
% 24.36/15.03  #BackRed      : 30
% 24.36/15.03  
% 24.36/15.03  #Partial instantiations: 0
% 24.36/15.03  #Strategies tried      : 1
% 24.36/15.03  
% 24.36/15.03  Timing (in seconds)
% 24.36/15.03  ----------------------
% 24.36/15.03  Preprocessing        : 0.46
% 24.36/15.03  Parsing              : 0.23
% 24.36/15.03  CNF conversion       : 0.07
% 24.36/15.03  Main loop            : 13.67
% 24.36/15.03  Inferencing          : 3.33
% 24.36/15.03  Reduction            : 5.37
% 24.36/15.03  Demodulation         : 4.23
% 24.36/15.03  BG Simplification    : 0.26
% 24.36/15.03  Subsumption          : 4.02
% 24.36/15.03  Abstraction          : 0.38
% 24.36/15.03  MUC search           : 0.00
% 24.36/15.03  Cooper               : 0.00
% 24.36/15.03  Total                : 14.29
% 24.36/15.03  Index Insertion      : 0.00
% 24.36/15.03  Index Deletion       : 0.00
% 24.36/15.03  Index Matching       : 0.00
% 24.36/15.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
