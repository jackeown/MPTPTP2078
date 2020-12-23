%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:17 EST 2020

% Result     : Theorem 10.27s
% Output     : CNFRefutation 10.50s
% Verified   : 
% Statistics : Number of formulae       :  285 (2433 expanded)
%              Number of leaves         :   47 ( 829 expanded)
%              Depth                    :   18
%              Number of atoms          :  821 (10338 expanded)
%              Number of equality atoms :  205 (2142 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_225,negated_conjecture,(
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

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_183,axiom,(
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

tff(f_149,axiom,(
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

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_66,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | ~ r1_subset_1(A_15,B_16)
      | v1_xboole_0(B_16)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_102,plain,(
    ! [C_229,A_230,B_231] :
      ( v1_relat_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_109,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_1230,plain,(
    ! [C_354,A_355,B_356] :
      ( v4_relat_1(C_354,A_355)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_355,B_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1237,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1230])).

tff(c_7745,plain,(
    ! [B_819,A_820] :
      ( k1_relat_1(B_819) = A_820
      | ~ v1_partfun1(B_819,A_820)
      | ~ v4_relat_1(B_819,A_820)
      | ~ v1_relat_1(B_819) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7751,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1237,c_7745])).

tff(c_7757,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_7751])).

tff(c_8244,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7757])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_8525,plain,(
    ! [C_883,A_884,B_885] :
      ( v1_partfun1(C_883,A_884)
      | ~ v1_funct_2(C_883,A_884,B_885)
      | ~ v1_funct_1(C_883)
      | ~ m1_subset_1(C_883,k1_zfmisc_1(k2_zfmisc_1(A_884,B_885)))
      | v1_xboole_0(B_885) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8528,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_8525])).

tff(c_8534,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_8528])).

tff(c_8536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_8244,c_8534])).

tff(c_8537,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7757])).

tff(c_10,plain,(
    ! [A_8,B_10] :
      ( k7_relat_1(A_8,B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,k1_relat_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8545,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_6',B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8537,c_10])).

tff(c_8620,plain,(
    ! [B_888] :
      ( k7_relat_1('#skF_6',B_888) = k1_xboole_0
      | ~ r1_xboole_0(B_888,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_8545])).

tff(c_8624,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_subset_1(A_15,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_8620])).

tff(c_8821,plain,(
    ! [A_905] :
      ( k7_relat_1('#skF_6',A_905) = k1_xboole_0
      | ~ r1_subset_1(A_905,'#skF_4')
      | v1_xboole_0(A_905) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8624])).

tff(c_8824,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_8821])).

tff(c_8827,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8824])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k3_xboole_0(k1_relat_1(B_14),A_13) = k1_relat_1(k7_relat_1(B_14,A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8551,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_13)) = k3_xboole_0('#skF_4',A_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8537,c_18])).

tff(c_8561,plain,(
    ! [A_13] : k1_relat_1(k7_relat_1('#skF_6',A_13)) = k3_xboole_0('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_8551])).

tff(c_8834,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8827,c_8561])).

tff(c_8841,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8834])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_110,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_102])).

tff(c_1238,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1230])).

tff(c_7748,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1238,c_7745])).

tff(c_7754,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_7748])).

tff(c_7758,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7754])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_8197,plain,(
    ! [C_860,A_861,B_862] :
      ( v1_partfun1(C_860,A_861)
      | ~ v1_funct_2(C_860,A_861,B_862)
      | ~ v1_funct_1(C_860)
      | ~ m1_subset_1(C_860,k1_zfmisc_1(k2_zfmisc_1(A_861,B_862)))
      | v1_xboole_0(B_862) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8203,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_8197])).

tff(c_8210,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_8203])).

tff(c_8212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7758,c_8210])).

tff(c_8213,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7754])).

tff(c_8221,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_5',B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8213,c_10])).

tff(c_8633,plain,(
    ! [B_889] :
      ( k7_relat_1('#skF_5',B_889) = k1_xboole_0
      | ~ r1_xboole_0(B_889,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_8221])).

tff(c_8676,plain,(
    ! [A_892] :
      ( k7_relat_1('#skF_5',A_892) = k1_xboole_0
      | k3_xboole_0(A_892,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_8633])).

tff(c_8227,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_13)) = k3_xboole_0('#skF_3',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8213,c_18])).

tff(c_8237,plain,(
    ! [A_13] : k1_relat_1(k7_relat_1('#skF_5',A_13)) = k3_xboole_0('#skF_3',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_8227])).

tff(c_8685,plain,(
    ! [A_892] :
      ( k3_xboole_0('#skF_3',A_892) = k1_relat_1(k1_xboole_0)
      | k3_xboole_0(A_892,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8676,c_8237])).

tff(c_8701,plain,(
    ! [A_892] :
      ( k3_xboole_0('#skF_3',A_892) = k1_xboole_0
      | k3_xboole_0(A_892,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8685])).

tff(c_8855,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8841,c_8701])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,k3_xboole_0(k1_relat_1(B_12),A_11)) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8218,plain,(
    ! [A_11] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_11)) = k7_relat_1('#skF_5',A_11)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8213,c_12])).

tff(c_8231,plain,(
    ! [A_11] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_11)) = k7_relat_1('#skF_5',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_8218])).

tff(c_8867,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8855,c_8231])).

tff(c_8542,plain,(
    ! [A_11] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_11)) = k7_relat_1('#skF_6',A_11)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8537,c_12])).

tff(c_8555,plain,(
    ! [A_11] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_11)) = k7_relat_1('#skF_6',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_8542])).

tff(c_8852,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8841,c_8555])).

tff(c_8857,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8827,c_8852])).

tff(c_8787,plain,(
    ! [A_898,B_899,C_900,D_901] :
      ( k2_partfun1(A_898,B_899,C_900,D_901) = k7_relat_1(C_900,D_901)
      | ~ m1_subset_1(C_900,k1_zfmisc_1(k2_zfmisc_1(A_898,B_899)))
      | ~ v1_funct_1(C_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8791,plain,(
    ! [D_901] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_901) = k7_relat_1('#skF_5',D_901)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_8787])).

tff(c_8797,plain,(
    ! [D_901] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_901) = k7_relat_1('#skF_5',D_901) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8791])).

tff(c_8789,plain,(
    ! [D_901] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_901) = k7_relat_1('#skF_6',D_901)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_8787])).

tff(c_8794,plain,(
    ! [D_901] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_901) = k7_relat_1('#skF_6',D_901) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8789])).

tff(c_7680,plain,(
    ! [A_810,B_811,C_812] :
      ( k9_subset_1(A_810,B_811,C_812) = k3_xboole_0(B_811,C_812)
      | ~ m1_subset_1(C_812,k1_zfmisc_1(A_810)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7692,plain,(
    ! [B_811] : k9_subset_1('#skF_1',B_811,'#skF_4') = k3_xboole_0(B_811,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_7680])).

tff(c_112,plain,(
    ! [C_232,A_233,B_234] :
      ( v4_relat_1(C_232,A_233)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_119,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_112])).

tff(c_241,plain,(
    ! [B_256,A_257] :
      ( k1_relat_1(B_256) = A_257
      | ~ v1_partfun1(B_256,A_257)
      | ~ v4_relat_1(B_256,A_257)
      | ~ v1_relat_1(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_247,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_119,c_241])).

tff(c_253,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_247])).

tff(c_514,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_662,plain,(
    ! [C_298,A_299,B_300] :
      ( v1_partfun1(C_298,A_299)
      | ~ v1_funct_2(C_298,A_299,B_300)
      | ~ v1_funct_1(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300)))
      | v1_xboole_0(B_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_665,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_662])).

tff(c_671,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_665])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_514,c_671])).

tff(c_674,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_685,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_6',B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_10])).

tff(c_729,plain,(
    ! [B_302] :
      ( k7_relat_1('#skF_6',B_302) = k1_xboole_0
      | ~ r1_xboole_0(B_302,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_685])).

tff(c_733,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_subset_1(A_15,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_729])).

tff(c_860,plain,(
    ! [A_314] :
      ( k7_relat_1('#skF_6',A_314) = k1_xboole_0
      | ~ r1_subset_1(A_314,'#skF_4')
      | v1_xboole_0(A_314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_733])).

tff(c_863,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_860])).

tff(c_866,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_863])).

tff(c_682,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_13)) = k3_xboole_0('#skF_4',A_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_18])).

tff(c_694,plain,(
    ! [A_13] : k1_relat_1(k7_relat_1('#skF_6',A_13)) = k3_xboole_0('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_682])).

tff(c_870,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_694])).

tff(c_873,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_870])).

tff(c_120,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_244,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_120,c_241])).

tff(c_250,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_244])).

tff(c_254,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_471,plain,(
    ! [C_281,A_282,B_283] :
      ( v1_partfun1(C_281,A_282)
      | ~ v1_funct_2(C_281,A_282,B_283)
      | ~ v1_funct_1(C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | v1_xboole_0(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_477,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_471])).

tff(c_484,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_477])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_254,c_484])).

tff(c_487,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_498,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_5',B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_10])).

tff(c_742,plain,(
    ! [B_303] :
      ( k7_relat_1('#skF_5',B_303) = k1_xboole_0
      | ~ r1_xboole_0(B_303,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_498])).

tff(c_754,plain,(
    ! [A_1] :
      ( k7_relat_1('#skF_5',A_1) = k1_xboole_0
      | k3_xboole_0(A_1,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_742])).

tff(c_679,plain,(
    ! [A_11] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_11)) = k7_relat_1('#skF_6',A_11)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_12])).

tff(c_692,plain,(
    ! [A_11] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_11)) = k7_relat_1('#skF_6',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_679])).

tff(c_881,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_692])).

tff(c_885,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_881])).

tff(c_945,plain,(
    ! [A_319] :
      ( k7_relat_1('#skF_5',A_319) = k1_xboole_0
      | k3_xboole_0(A_319,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_742])).

tff(c_495,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_13)) = k3_xboole_0('#skF_3',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_18])).

tff(c_507,plain,(
    ! [A_13] : k1_relat_1(k7_relat_1('#skF_5',A_13)) = k3_xboole_0('#skF_3',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_495])).

tff(c_954,plain,(
    ! [A_319] :
      ( k3_xboole_0('#skF_3',A_319) = k1_relat_1(k1_xboole_0)
      | k3_xboole_0(A_319,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_507])).

tff(c_1024,plain,(
    ! [A_322] :
      ( k3_xboole_0('#skF_3',A_322) = k1_xboole_0
      | k3_xboole_0(A_322,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_954])).

tff(c_1030,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_1024])).

tff(c_492,plain,(
    ! [A_11] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_11)) = k7_relat_1('#skF_5',A_11)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_12])).

tff(c_505,plain,(
    ! [A_11] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_11)) = k7_relat_1('#skF_5',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_492])).

tff(c_809,plain,(
    ! [A_307,B_308,C_309,D_310] :
      ( k2_partfun1(A_307,B_308,C_309,D_310) = k7_relat_1(C_309,D_310)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_307,B_308)))
      | ~ v1_funct_1(C_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_813,plain,(
    ! [D_310] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_310) = k7_relat_1('#skF_5',D_310)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_809])).

tff(c_819,plain,(
    ! [D_310] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_310) = k7_relat_1('#skF_5',D_310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_813])).

tff(c_811,plain,(
    ! [D_310] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_310) = k7_relat_1('#skF_6',D_310)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_809])).

tff(c_816,plain,(
    ! [D_310] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_310) = k7_relat_1('#skF_6',D_310) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_811])).

tff(c_176,plain,(
    ! [A_247,B_248,C_249] :
      ( k9_subset_1(A_247,B_248,C_249) = k3_xboole_0(B_248,C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(A_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_188,plain,(
    ! [B_248] : k9_subset_1('#skF_1',B_248,'#skF_4') = k3_xboole_0(B_248,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_176])).

tff(c_52,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_111,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_198,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_188,c_111])).

tff(c_820,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_198])).

tff(c_1216,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_1030,c_505,c_819,c_820])).

tff(c_1219,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_754,c_1216])).

tff(c_1223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_1219])).

tff(c_1225,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7717,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7692,c_7692,c_1225])).

tff(c_8798,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8794,c_7717])).

tff(c_8944,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8867,c_8857,c_8855,c_8797,c_8855,c_8798])).

tff(c_9009,plain,(
    ! [A_915,D_913,B_912,E_914,F_916,C_911] :
      ( v1_funct_1(k1_tmap_1(A_915,B_912,C_911,D_913,E_914,F_916))
      | ~ m1_subset_1(F_916,k1_zfmisc_1(k2_zfmisc_1(D_913,B_912)))
      | ~ v1_funct_2(F_916,D_913,B_912)
      | ~ v1_funct_1(F_916)
      | ~ m1_subset_1(E_914,k1_zfmisc_1(k2_zfmisc_1(C_911,B_912)))
      | ~ v1_funct_2(E_914,C_911,B_912)
      | ~ v1_funct_1(E_914)
      | ~ m1_subset_1(D_913,k1_zfmisc_1(A_915))
      | v1_xboole_0(D_913)
      | ~ m1_subset_1(C_911,k1_zfmisc_1(A_915))
      | v1_xboole_0(C_911)
      | v1_xboole_0(B_912)
      | v1_xboole_0(A_915) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_9011,plain,(
    ! [A_915,C_911,E_914] :
      ( v1_funct_1(k1_tmap_1(A_915,'#skF_2',C_911,'#skF_4',E_914,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_914,k1_zfmisc_1(k2_zfmisc_1(C_911,'#skF_2')))
      | ~ v1_funct_2(E_914,C_911,'#skF_2')
      | ~ v1_funct_1(E_914)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_915))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_911,k1_zfmisc_1(A_915))
      | v1_xboole_0(C_911)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_915) ) ),
    inference(resolution,[status(thm)],[c_54,c_9009])).

tff(c_9016,plain,(
    ! [A_915,C_911,E_914] :
      ( v1_funct_1(k1_tmap_1(A_915,'#skF_2',C_911,'#skF_4',E_914,'#skF_6'))
      | ~ m1_subset_1(E_914,k1_zfmisc_1(k2_zfmisc_1(C_911,'#skF_2')))
      | ~ v1_funct_2(E_914,C_911,'#skF_2')
      | ~ v1_funct_1(E_914)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_915))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_911,k1_zfmisc_1(A_915))
      | v1_xboole_0(C_911)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_915) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_9011])).

tff(c_9022,plain,(
    ! [A_917,C_918,E_919] :
      ( v1_funct_1(k1_tmap_1(A_917,'#skF_2',C_918,'#skF_4',E_919,'#skF_6'))
      | ~ m1_subset_1(E_919,k1_zfmisc_1(k2_zfmisc_1(C_918,'#skF_2')))
      | ~ v1_funct_2(E_919,C_918,'#skF_2')
      | ~ v1_funct_1(E_919)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_917))
      | ~ m1_subset_1(C_918,k1_zfmisc_1(A_917))
      | v1_xboole_0(C_918)
      | v1_xboole_0(A_917) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_9016])).

tff(c_9026,plain,(
    ! [A_917] :
      ( v1_funct_1(k1_tmap_1(A_917,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_917))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_917))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_917) ) ),
    inference(resolution,[status(thm)],[c_60,c_9022])).

tff(c_9033,plain,(
    ! [A_917] :
      ( v1_funct_1(k1_tmap_1(A_917,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_917))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_917))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_917) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_9026])).

tff(c_9584,plain,(
    ! [A_951] :
      ( v1_funct_1(k1_tmap_1(A_951,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_951))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_951))
      | v1_xboole_0(A_951) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_9033])).

tff(c_9587,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_9584])).

tff(c_9590,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_9587])).

tff(c_9591,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9590])).

tff(c_48,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_46,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_10033,plain,(
    ! [E_976,D_980,F_978,C_979,B_977,A_975] :
      ( k2_partfun1(k4_subset_1(A_975,C_979,D_980),B_977,k1_tmap_1(A_975,B_977,C_979,D_980,E_976,F_978),C_979) = E_976
      | ~ m1_subset_1(k1_tmap_1(A_975,B_977,C_979,D_980,E_976,F_978),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_975,C_979,D_980),B_977)))
      | ~ v1_funct_2(k1_tmap_1(A_975,B_977,C_979,D_980,E_976,F_978),k4_subset_1(A_975,C_979,D_980),B_977)
      | ~ v1_funct_1(k1_tmap_1(A_975,B_977,C_979,D_980,E_976,F_978))
      | k2_partfun1(D_980,B_977,F_978,k9_subset_1(A_975,C_979,D_980)) != k2_partfun1(C_979,B_977,E_976,k9_subset_1(A_975,C_979,D_980))
      | ~ m1_subset_1(F_978,k1_zfmisc_1(k2_zfmisc_1(D_980,B_977)))
      | ~ v1_funct_2(F_978,D_980,B_977)
      | ~ v1_funct_1(F_978)
      | ~ m1_subset_1(E_976,k1_zfmisc_1(k2_zfmisc_1(C_979,B_977)))
      | ~ v1_funct_2(E_976,C_979,B_977)
      | ~ v1_funct_1(E_976)
      | ~ m1_subset_1(D_980,k1_zfmisc_1(A_975))
      | v1_xboole_0(D_980)
      | ~ m1_subset_1(C_979,k1_zfmisc_1(A_975))
      | v1_xboole_0(C_979)
      | v1_xboole_0(B_977)
      | v1_xboole_0(A_975) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_11507,plain,(
    ! [B_1097,A_1100,F_1101,C_1096,D_1098,E_1099] :
      ( k2_partfun1(k4_subset_1(A_1100,C_1096,D_1098),B_1097,k1_tmap_1(A_1100,B_1097,C_1096,D_1098,E_1099,F_1101),C_1096) = E_1099
      | ~ v1_funct_2(k1_tmap_1(A_1100,B_1097,C_1096,D_1098,E_1099,F_1101),k4_subset_1(A_1100,C_1096,D_1098),B_1097)
      | ~ v1_funct_1(k1_tmap_1(A_1100,B_1097,C_1096,D_1098,E_1099,F_1101))
      | k2_partfun1(D_1098,B_1097,F_1101,k9_subset_1(A_1100,C_1096,D_1098)) != k2_partfun1(C_1096,B_1097,E_1099,k9_subset_1(A_1100,C_1096,D_1098))
      | ~ m1_subset_1(F_1101,k1_zfmisc_1(k2_zfmisc_1(D_1098,B_1097)))
      | ~ v1_funct_2(F_1101,D_1098,B_1097)
      | ~ v1_funct_1(F_1101)
      | ~ m1_subset_1(E_1099,k1_zfmisc_1(k2_zfmisc_1(C_1096,B_1097)))
      | ~ v1_funct_2(E_1099,C_1096,B_1097)
      | ~ v1_funct_1(E_1099)
      | ~ m1_subset_1(D_1098,k1_zfmisc_1(A_1100))
      | v1_xboole_0(D_1098)
      | ~ m1_subset_1(C_1096,k1_zfmisc_1(A_1100))
      | v1_xboole_0(C_1096)
      | v1_xboole_0(B_1097)
      | v1_xboole_0(A_1100) ) ),
    inference(resolution,[status(thm)],[c_46,c_10033])).

tff(c_13487,plain,(
    ! [B_1195,A_1198,E_1197,F_1199,C_1194,D_1196] :
      ( k2_partfun1(k4_subset_1(A_1198,C_1194,D_1196),B_1195,k1_tmap_1(A_1198,B_1195,C_1194,D_1196,E_1197,F_1199),C_1194) = E_1197
      | ~ v1_funct_1(k1_tmap_1(A_1198,B_1195,C_1194,D_1196,E_1197,F_1199))
      | k2_partfun1(D_1196,B_1195,F_1199,k9_subset_1(A_1198,C_1194,D_1196)) != k2_partfun1(C_1194,B_1195,E_1197,k9_subset_1(A_1198,C_1194,D_1196))
      | ~ m1_subset_1(F_1199,k1_zfmisc_1(k2_zfmisc_1(D_1196,B_1195)))
      | ~ v1_funct_2(F_1199,D_1196,B_1195)
      | ~ v1_funct_1(F_1199)
      | ~ m1_subset_1(E_1197,k1_zfmisc_1(k2_zfmisc_1(C_1194,B_1195)))
      | ~ v1_funct_2(E_1197,C_1194,B_1195)
      | ~ v1_funct_1(E_1197)
      | ~ m1_subset_1(D_1196,k1_zfmisc_1(A_1198))
      | v1_xboole_0(D_1196)
      | ~ m1_subset_1(C_1194,k1_zfmisc_1(A_1198))
      | v1_xboole_0(C_1194)
      | v1_xboole_0(B_1195)
      | v1_xboole_0(A_1198) ) ),
    inference(resolution,[status(thm)],[c_48,c_11507])).

tff(c_13491,plain,(
    ! [A_1198,C_1194,E_1197] :
      ( k2_partfun1(k4_subset_1(A_1198,C_1194,'#skF_4'),'#skF_2',k1_tmap_1(A_1198,'#skF_2',C_1194,'#skF_4',E_1197,'#skF_6'),C_1194) = E_1197
      | ~ v1_funct_1(k1_tmap_1(A_1198,'#skF_2',C_1194,'#skF_4',E_1197,'#skF_6'))
      | k2_partfun1(C_1194,'#skF_2',E_1197,k9_subset_1(A_1198,C_1194,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1198,C_1194,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1197,k1_zfmisc_1(k2_zfmisc_1(C_1194,'#skF_2')))
      | ~ v1_funct_2(E_1197,C_1194,'#skF_2')
      | ~ v1_funct_1(E_1197)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1198))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1194,k1_zfmisc_1(A_1198))
      | v1_xboole_0(C_1194)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1198) ) ),
    inference(resolution,[status(thm)],[c_54,c_13487])).

tff(c_13497,plain,(
    ! [A_1198,C_1194,E_1197] :
      ( k2_partfun1(k4_subset_1(A_1198,C_1194,'#skF_4'),'#skF_2',k1_tmap_1(A_1198,'#skF_2',C_1194,'#skF_4',E_1197,'#skF_6'),C_1194) = E_1197
      | ~ v1_funct_1(k1_tmap_1(A_1198,'#skF_2',C_1194,'#skF_4',E_1197,'#skF_6'))
      | k2_partfun1(C_1194,'#skF_2',E_1197,k9_subset_1(A_1198,C_1194,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1198,C_1194,'#skF_4'))
      | ~ m1_subset_1(E_1197,k1_zfmisc_1(k2_zfmisc_1(C_1194,'#skF_2')))
      | ~ v1_funct_2(E_1197,C_1194,'#skF_2')
      | ~ v1_funct_1(E_1197)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1198))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1194,k1_zfmisc_1(A_1198))
      | v1_xboole_0(C_1194)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_8794,c_13491])).

tff(c_13962,plain,(
    ! [A_1230,C_1231,E_1232] :
      ( k2_partfun1(k4_subset_1(A_1230,C_1231,'#skF_4'),'#skF_2',k1_tmap_1(A_1230,'#skF_2',C_1231,'#skF_4',E_1232,'#skF_6'),C_1231) = E_1232
      | ~ v1_funct_1(k1_tmap_1(A_1230,'#skF_2',C_1231,'#skF_4',E_1232,'#skF_6'))
      | k2_partfun1(C_1231,'#skF_2',E_1232,k9_subset_1(A_1230,C_1231,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1230,C_1231,'#skF_4'))
      | ~ m1_subset_1(E_1232,k1_zfmisc_1(k2_zfmisc_1(C_1231,'#skF_2')))
      | ~ v1_funct_2(E_1232,C_1231,'#skF_2')
      | ~ v1_funct_1(E_1232)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1230))
      | ~ m1_subset_1(C_1231,k1_zfmisc_1(A_1230))
      | v1_xboole_0(C_1231)
      | v1_xboole_0(A_1230) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_13497])).

tff(c_13969,plain,(
    ! [A_1230] :
      ( k2_partfun1(k4_subset_1(A_1230,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1230,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1230,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1230,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1230,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1230))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1230))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1230) ) ),
    inference(resolution,[status(thm)],[c_60,c_13962])).

tff(c_13979,plain,(
    ! [A_1230] :
      ( k2_partfun1(k4_subset_1(A_1230,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1230,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1230,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1230,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1230,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1230))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1230))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_8797,c_13969])).

tff(c_14962,plain,(
    ! [A_1253] :
      ( k2_partfun1(k4_subset_1(A_1253,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1253,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1253,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1253,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1253,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1253))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1253))
      | v1_xboole_0(A_1253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_13979])).

tff(c_1360,plain,(
    ! [B_378,A_379] :
      ( k1_relat_1(B_378) = A_379
      | ~ v1_partfun1(B_378,A_379)
      | ~ v4_relat_1(B_378,A_379)
      | ~ v1_relat_1(B_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1366,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1237,c_1360])).

tff(c_1372,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_1366])).

tff(c_1797,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1372])).

tff(c_1996,plain,(
    ! [C_436,A_437,B_438] :
      ( v1_partfun1(C_436,A_437)
      | ~ v1_funct_2(C_436,A_437,B_438)
      | ~ v1_funct_1(C_436)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_437,B_438)))
      | v1_xboole_0(B_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1999,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1996])).

tff(c_2005,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1999])).

tff(c_2007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1797,c_2005])).

tff(c_2008,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1372])).

tff(c_2016,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_6',B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2008,c_10])).

tff(c_2076,plain,(
    ! [B_441] :
      ( k7_relat_1('#skF_6',B_441) = k1_xboole_0
      | ~ r1_xboole_0(B_441,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2016])).

tff(c_2080,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_subset_1(A_15,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_2076])).

tff(c_2173,plain,(
    ! [A_451] :
      ( k7_relat_1('#skF_6',A_451) = k1_xboole_0
      | ~ r1_subset_1(A_451,'#skF_4')
      | v1_xboole_0(A_451) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2080])).

tff(c_2176,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2173])).

tff(c_2179,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2176])).

tff(c_2022,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_13)) = k3_xboole_0('#skF_4',A_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2008,c_18])).

tff(c_2032,plain,(
    ! [A_13] : k1_relat_1(k7_relat_1('#skF_6',A_13)) = k3_xboole_0('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2022])).

tff(c_2183,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2179,c_2032])).

tff(c_2186,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2183])).

tff(c_1363,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1238,c_1360])).

tff(c_1369,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1363])).

tff(c_1373,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1369])).

tff(c_1750,plain,(
    ! [C_417,A_418,B_419] :
      ( v1_partfun1(C_417,A_418)
      | ~ v1_funct_2(C_417,A_418,B_419)
      | ~ v1_funct_1(C_417)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_418,B_419)))
      | v1_xboole_0(B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1756,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1750])).

tff(c_1763,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1756])).

tff(c_1765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1373,c_1763])).

tff(c_1766,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1369])).

tff(c_1774,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_5',B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_10])).

tff(c_2035,plain,(
    ! [B_439] :
      ( k7_relat_1('#skF_5',B_439) = k1_xboole_0
      | ~ r1_xboole_0(B_439,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1774])).

tff(c_2326,plain,(
    ! [A_459] :
      ( k7_relat_1('#skF_5',A_459) = k1_xboole_0
      | k3_xboole_0(A_459,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2035])).

tff(c_1780,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_13)) = k3_xboole_0('#skF_3',A_13)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_18])).

tff(c_1790,plain,(
    ! [A_13] : k1_relat_1(k7_relat_1('#skF_5',A_13)) = k3_xboole_0('#skF_3',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1780])).

tff(c_2335,plain,(
    ! [A_459] :
      ( k3_xboole_0('#skF_3',A_459) = k1_relat_1(k1_xboole_0)
      | k3_xboole_0(A_459,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2326,c_1790])).

tff(c_2362,plain,(
    ! [A_461] :
      ( k3_xboole_0('#skF_3',A_461) = k1_xboole_0
      | k3_xboole_0(A_461,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2335])).

tff(c_2368,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_2362])).

tff(c_1771,plain,(
    ! [A_11] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_11)) = k7_relat_1('#skF_5',A_11)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1766,c_12])).

tff(c_1784,plain,(
    ! [A_11] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_11)) = k7_relat_1('#skF_5',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1771])).

tff(c_2377,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2368,c_1784])).

tff(c_2013,plain,(
    ! [A_11] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_11)) = k7_relat_1('#skF_6',A_11)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2008,c_12])).

tff(c_2026,plain,(
    ! [A_11] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_11)) = k7_relat_1('#skF_6',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2013])).

tff(c_2191,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_2026])).

tff(c_2194,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2179,c_2191])).

tff(c_2130,plain,(
    ! [A_444,B_445,C_446,D_447] :
      ( k2_partfun1(A_444,B_445,C_446,D_447) = k7_relat_1(C_446,D_447)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445)))
      | ~ v1_funct_1(C_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2134,plain,(
    ! [D_447] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_447) = k7_relat_1('#skF_5',D_447)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_2130])).

tff(c_2140,plain,(
    ! [D_447] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_447) = k7_relat_1('#skF_5',D_447) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2134])).

tff(c_2132,plain,(
    ! [D_447] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_447) = k7_relat_1('#skF_6',D_447)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_2130])).

tff(c_2137,plain,(
    ! [D_447] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_447) = k7_relat_1('#skF_6',D_447) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2132])).

tff(c_1295,plain,(
    ! [A_369,B_370,C_371] :
      ( k9_subset_1(A_369,B_370,C_371) = k3_xboole_0(B_370,C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(A_369)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1307,plain,(
    ! [B_370] : k9_subset_1('#skF_1',B_370,'#skF_4') = k3_xboole_0(B_370,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1295])).

tff(c_1332,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_1307,c_1225])).

tff(c_2141,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_1332])).

tff(c_2550,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2377,c_2194,c_2368,c_2140,c_2368,c_2141])).

tff(c_2384,plain,(
    ! [D_464,F_467,E_465,A_466,B_463,C_462] :
      ( v1_funct_1(k1_tmap_1(A_466,B_463,C_462,D_464,E_465,F_467))
      | ~ m1_subset_1(F_467,k1_zfmisc_1(k2_zfmisc_1(D_464,B_463)))
      | ~ v1_funct_2(F_467,D_464,B_463)
      | ~ v1_funct_1(F_467)
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(C_462,B_463)))
      | ~ v1_funct_2(E_465,C_462,B_463)
      | ~ v1_funct_1(E_465)
      | ~ m1_subset_1(D_464,k1_zfmisc_1(A_466))
      | v1_xboole_0(D_464)
      | ~ m1_subset_1(C_462,k1_zfmisc_1(A_466))
      | v1_xboole_0(C_462)
      | v1_xboole_0(B_463)
      | v1_xboole_0(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2386,plain,(
    ! [A_466,C_462,E_465] :
      ( v1_funct_1(k1_tmap_1(A_466,'#skF_2',C_462,'#skF_4',E_465,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(C_462,'#skF_2')))
      | ~ v1_funct_2(E_465,C_462,'#skF_2')
      | ~ v1_funct_1(E_465)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_466))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_462,k1_zfmisc_1(A_466))
      | v1_xboole_0(C_462)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_466) ) ),
    inference(resolution,[status(thm)],[c_54,c_2384])).

tff(c_2391,plain,(
    ! [A_466,C_462,E_465] :
      ( v1_funct_1(k1_tmap_1(A_466,'#skF_2',C_462,'#skF_4',E_465,'#skF_6'))
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(C_462,'#skF_2')))
      | ~ v1_funct_2(E_465,C_462,'#skF_2')
      | ~ v1_funct_1(E_465)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_466))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_462,k1_zfmisc_1(A_466))
      | v1_xboole_0(C_462)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2386])).

tff(c_2424,plain,(
    ! [A_468,C_469,E_470] :
      ( v1_funct_1(k1_tmap_1(A_468,'#skF_2',C_469,'#skF_4',E_470,'#skF_6'))
      | ~ m1_subset_1(E_470,k1_zfmisc_1(k2_zfmisc_1(C_469,'#skF_2')))
      | ~ v1_funct_2(E_470,C_469,'#skF_2')
      | ~ v1_funct_1(E_470)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_468))
      | ~ m1_subset_1(C_469,k1_zfmisc_1(A_468))
      | v1_xboole_0(C_469)
      | v1_xboole_0(A_468) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_2391])).

tff(c_2428,plain,(
    ! [A_468] :
      ( v1_funct_1(k1_tmap_1(A_468,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_468))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_468))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_60,c_2424])).

tff(c_2435,plain,(
    ! [A_468] :
      ( v1_funct_1(k1_tmap_1(A_468,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_468))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_468))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2428])).

tff(c_2586,plain,(
    ! [A_492] :
      ( v1_funct_1(k1_tmap_1(A_492,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_492))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_492))
      | v1_xboole_0(A_492) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2435])).

tff(c_2589,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_2586])).

tff(c_2592,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2589])).

tff(c_2593,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2592])).

tff(c_2744,plain,(
    ! [E_498,A_497,D_502,C_501,F_500,B_499] :
      ( k2_partfun1(k4_subset_1(A_497,C_501,D_502),B_499,k1_tmap_1(A_497,B_499,C_501,D_502,E_498,F_500),D_502) = F_500
      | ~ m1_subset_1(k1_tmap_1(A_497,B_499,C_501,D_502,E_498,F_500),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_497,C_501,D_502),B_499)))
      | ~ v1_funct_2(k1_tmap_1(A_497,B_499,C_501,D_502,E_498,F_500),k4_subset_1(A_497,C_501,D_502),B_499)
      | ~ v1_funct_1(k1_tmap_1(A_497,B_499,C_501,D_502,E_498,F_500))
      | k2_partfun1(D_502,B_499,F_500,k9_subset_1(A_497,C_501,D_502)) != k2_partfun1(C_501,B_499,E_498,k9_subset_1(A_497,C_501,D_502))
      | ~ m1_subset_1(F_500,k1_zfmisc_1(k2_zfmisc_1(D_502,B_499)))
      | ~ v1_funct_2(F_500,D_502,B_499)
      | ~ v1_funct_1(F_500)
      | ~ m1_subset_1(E_498,k1_zfmisc_1(k2_zfmisc_1(C_501,B_499)))
      | ~ v1_funct_2(E_498,C_501,B_499)
      | ~ v1_funct_1(E_498)
      | ~ m1_subset_1(D_502,k1_zfmisc_1(A_497))
      | v1_xboole_0(D_502)
      | ~ m1_subset_1(C_501,k1_zfmisc_1(A_497))
      | v1_xboole_0(C_501)
      | v1_xboole_0(B_499)
      | v1_xboole_0(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4969,plain,(
    ! [C_655,B_656,A_659,F_660,D_657,E_658] :
      ( k2_partfun1(k4_subset_1(A_659,C_655,D_657),B_656,k1_tmap_1(A_659,B_656,C_655,D_657,E_658,F_660),D_657) = F_660
      | ~ v1_funct_2(k1_tmap_1(A_659,B_656,C_655,D_657,E_658,F_660),k4_subset_1(A_659,C_655,D_657),B_656)
      | ~ v1_funct_1(k1_tmap_1(A_659,B_656,C_655,D_657,E_658,F_660))
      | k2_partfun1(D_657,B_656,F_660,k9_subset_1(A_659,C_655,D_657)) != k2_partfun1(C_655,B_656,E_658,k9_subset_1(A_659,C_655,D_657))
      | ~ m1_subset_1(F_660,k1_zfmisc_1(k2_zfmisc_1(D_657,B_656)))
      | ~ v1_funct_2(F_660,D_657,B_656)
      | ~ v1_funct_1(F_660)
      | ~ m1_subset_1(E_658,k1_zfmisc_1(k2_zfmisc_1(C_655,B_656)))
      | ~ v1_funct_2(E_658,C_655,B_656)
      | ~ v1_funct_1(E_658)
      | ~ m1_subset_1(D_657,k1_zfmisc_1(A_659))
      | v1_xboole_0(D_657)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(A_659))
      | v1_xboole_0(C_655)
      | v1_xboole_0(B_656)
      | v1_xboole_0(A_659) ) ),
    inference(resolution,[status(thm)],[c_46,c_2744])).

tff(c_5962,plain,(
    ! [D_720,B_719,A_722,F_723,C_718,E_721] :
      ( k2_partfun1(k4_subset_1(A_722,C_718,D_720),B_719,k1_tmap_1(A_722,B_719,C_718,D_720,E_721,F_723),D_720) = F_723
      | ~ v1_funct_1(k1_tmap_1(A_722,B_719,C_718,D_720,E_721,F_723))
      | k2_partfun1(D_720,B_719,F_723,k9_subset_1(A_722,C_718,D_720)) != k2_partfun1(C_718,B_719,E_721,k9_subset_1(A_722,C_718,D_720))
      | ~ m1_subset_1(F_723,k1_zfmisc_1(k2_zfmisc_1(D_720,B_719)))
      | ~ v1_funct_2(F_723,D_720,B_719)
      | ~ v1_funct_1(F_723)
      | ~ m1_subset_1(E_721,k1_zfmisc_1(k2_zfmisc_1(C_718,B_719)))
      | ~ v1_funct_2(E_721,C_718,B_719)
      | ~ v1_funct_1(E_721)
      | ~ m1_subset_1(D_720,k1_zfmisc_1(A_722))
      | v1_xboole_0(D_720)
      | ~ m1_subset_1(C_718,k1_zfmisc_1(A_722))
      | v1_xboole_0(C_718)
      | v1_xboole_0(B_719)
      | v1_xboole_0(A_722) ) ),
    inference(resolution,[status(thm)],[c_48,c_4969])).

tff(c_5966,plain,(
    ! [A_722,C_718,E_721] :
      ( k2_partfun1(k4_subset_1(A_722,C_718,'#skF_4'),'#skF_2',k1_tmap_1(A_722,'#skF_2',C_718,'#skF_4',E_721,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_722,'#skF_2',C_718,'#skF_4',E_721,'#skF_6'))
      | k2_partfun1(C_718,'#skF_2',E_721,k9_subset_1(A_722,C_718,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_722,C_718,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_721,k1_zfmisc_1(k2_zfmisc_1(C_718,'#skF_2')))
      | ~ v1_funct_2(E_721,C_718,'#skF_2')
      | ~ v1_funct_1(E_721)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_722))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_718,k1_zfmisc_1(A_722))
      | v1_xboole_0(C_718)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_722) ) ),
    inference(resolution,[status(thm)],[c_54,c_5962])).

tff(c_5972,plain,(
    ! [A_722,C_718,E_721] :
      ( k2_partfun1(k4_subset_1(A_722,C_718,'#skF_4'),'#skF_2',k1_tmap_1(A_722,'#skF_2',C_718,'#skF_4',E_721,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_722,'#skF_2',C_718,'#skF_4',E_721,'#skF_6'))
      | k2_partfun1(C_718,'#skF_2',E_721,k9_subset_1(A_722,C_718,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_722,C_718,'#skF_4'))
      | ~ m1_subset_1(E_721,k1_zfmisc_1(k2_zfmisc_1(C_718,'#skF_2')))
      | ~ v1_funct_2(E_721,C_718,'#skF_2')
      | ~ v1_funct_1(E_721)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_722))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_718,k1_zfmisc_1(A_722))
      | v1_xboole_0(C_718)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2137,c_5966])).

tff(c_7315,plain,(
    ! [A_772,C_773,E_774] :
      ( k2_partfun1(k4_subset_1(A_772,C_773,'#skF_4'),'#skF_2',k1_tmap_1(A_772,'#skF_2',C_773,'#skF_4',E_774,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_772,'#skF_2',C_773,'#skF_4',E_774,'#skF_6'))
      | k2_partfun1(C_773,'#skF_2',E_774,k9_subset_1(A_772,C_773,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_772,C_773,'#skF_4'))
      | ~ m1_subset_1(E_774,k1_zfmisc_1(k2_zfmisc_1(C_773,'#skF_2')))
      | ~ v1_funct_2(E_774,C_773,'#skF_2')
      | ~ v1_funct_1(E_774)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_772))
      | ~ m1_subset_1(C_773,k1_zfmisc_1(A_772))
      | v1_xboole_0(C_773)
      | v1_xboole_0(A_772) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_5972])).

tff(c_7322,plain,(
    ! [A_772] :
      ( k2_partfun1(k4_subset_1(A_772,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_772,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_772,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_772,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_772,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_772))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_772))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_772) ) ),
    inference(resolution,[status(thm)],[c_60,c_7315])).

tff(c_7332,plain,(
    ! [A_772] :
      ( k2_partfun1(k4_subset_1(A_772,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_772,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_772,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_772,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_772,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_772))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_772))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2140,c_7322])).

tff(c_7617,plain,(
    ! [A_802] :
      ( k2_partfun1(k4_subset_1(A_802,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_802,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_802,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_802,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_802,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_802))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_802))
      | v1_xboole_0(A_802) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_7332])).

tff(c_1224,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1261,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1224])).

tff(c_7628,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7617,c_1261])).

tff(c_7642,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2550,c_2194,c_2368,c_1784,c_1307,c_1307,c_2593,c_7628])).

tff(c_7644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7642])).

tff(c_7645,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1224])).

tff(c_14971,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14962,c_7645])).

tff(c_14982,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_8944,c_8857,c_8855,c_8231,c_7692,c_7692,c_9591,c_14971])).

tff(c_14984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.27/3.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.50/3.88  
% 10.50/3.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.50/3.88  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.50/3.88  
% 10.50/3.88  %Foreground sorts:
% 10.50/3.88  
% 10.50/3.88  
% 10.50/3.88  %Background operators:
% 10.50/3.88  
% 10.50/3.88  
% 10.50/3.88  %Foreground operators:
% 10.50/3.88  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 10.50/3.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.50/3.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.50/3.88  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.50/3.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.50/3.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.50/3.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.50/3.88  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.50/3.88  tff('#skF_5', type, '#skF_5': $i).
% 10.50/3.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.50/3.88  tff('#skF_6', type, '#skF_6': $i).
% 10.50/3.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.50/3.88  tff('#skF_2', type, '#skF_2': $i).
% 10.50/3.88  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.50/3.88  tff('#skF_3', type, '#skF_3': $i).
% 10.50/3.88  tff('#skF_1', type, '#skF_1': $i).
% 10.50/3.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.50/3.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.50/3.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.50/3.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.50/3.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.50/3.88  tff('#skF_4', type, '#skF_4': $i).
% 10.50/3.88  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.50/3.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.50/3.88  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.50/3.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.50/3.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.50/3.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.50/3.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.50/3.88  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.50/3.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.50/3.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.50/3.88  
% 10.50/3.92  tff(f_225, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 10.50/3.92  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 10.50/3.92  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 10.50/3.92  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.50/3.92  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.50/3.92  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 10.50/3.92  tff(f_87, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 10.50/3.92  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 10.50/3.92  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 10.50/3.92  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.50/3.92  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 10.50/3.92  tff(f_101, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 10.50/3.92  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.50/3.92  tff(f_183, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 10.50/3.92  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 10.50/3.92  tff(c_78, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.50/3.92  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_66, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_22, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | ~r1_subset_1(A_15, B_16) | v1_xboole_0(B_16) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.50/3.92  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_102, plain, (![C_229, A_230, B_231]: (v1_relat_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.50/3.92  tff(c_109, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_102])).
% 10.50/3.92  tff(c_76, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_1230, plain, (![C_354, A_355, B_356]: (v4_relat_1(C_354, A_355) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_355, B_356))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.50/3.92  tff(c_1237, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_1230])).
% 10.50/3.92  tff(c_7745, plain, (![B_819, A_820]: (k1_relat_1(B_819)=A_820 | ~v1_partfun1(B_819, A_820) | ~v4_relat_1(B_819, A_820) | ~v1_relat_1(B_819))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.50/3.92  tff(c_7751, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1237, c_7745])).
% 10.50/3.92  tff(c_7757, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_7751])).
% 10.50/3.92  tff(c_8244, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_7757])).
% 10.50/3.92  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_8525, plain, (![C_883, A_884, B_885]: (v1_partfun1(C_883, A_884) | ~v1_funct_2(C_883, A_884, B_885) | ~v1_funct_1(C_883) | ~m1_subset_1(C_883, k1_zfmisc_1(k2_zfmisc_1(A_884, B_885))) | v1_xboole_0(B_885))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.50/3.92  tff(c_8528, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_8525])).
% 10.50/3.92  tff(c_8534, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_8528])).
% 10.50/3.92  tff(c_8536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_8244, c_8534])).
% 10.50/3.92  tff(c_8537, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_7757])).
% 10.50/3.92  tff(c_10, plain, (![A_8, B_10]: (k7_relat_1(A_8, B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, k1_relat_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.50/3.92  tff(c_8545, plain, (![B_10]: (k7_relat_1('#skF_6', B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8537, c_10])).
% 10.50/3.92  tff(c_8620, plain, (![B_888]: (k7_relat_1('#skF_6', B_888)=k1_xboole_0 | ~r1_xboole_0(B_888, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_8545])).
% 10.50/3.92  tff(c_8624, plain, (![A_15]: (k7_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_subset_1(A_15, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_22, c_8620])).
% 10.50/3.92  tff(c_8821, plain, (![A_905]: (k7_relat_1('#skF_6', A_905)=k1_xboole_0 | ~r1_subset_1(A_905, '#skF_4') | v1_xboole_0(A_905))), inference(negUnitSimplification, [status(thm)], [c_70, c_8624])).
% 10.50/3.92  tff(c_8824, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_8821])).
% 10.50/3.92  tff(c_8827, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_8824])).
% 10.50/3.92  tff(c_18, plain, (![B_14, A_13]: (k3_xboole_0(k1_relat_1(B_14), A_13)=k1_relat_1(k7_relat_1(B_14, A_13)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.50/3.92  tff(c_8551, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_6', A_13))=k3_xboole_0('#skF_4', A_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8537, c_18])).
% 10.50/3.92  tff(c_8561, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_6', A_13))=k3_xboole_0('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_8551])).
% 10.50/3.92  tff(c_8834, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8827, c_8561])).
% 10.50/3.92  tff(c_8841, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8834])).
% 10.50/3.92  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.50/3.92  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_110, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_102])).
% 10.50/3.92  tff(c_1238, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1230])).
% 10.50/3.92  tff(c_7748, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1238, c_7745])).
% 10.50/3.92  tff(c_7754, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_7748])).
% 10.50/3.92  tff(c_7758, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_7754])).
% 10.50/3.92  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_8197, plain, (![C_860, A_861, B_862]: (v1_partfun1(C_860, A_861) | ~v1_funct_2(C_860, A_861, B_862) | ~v1_funct_1(C_860) | ~m1_subset_1(C_860, k1_zfmisc_1(k2_zfmisc_1(A_861, B_862))) | v1_xboole_0(B_862))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.50/3.92  tff(c_8203, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_8197])).
% 10.50/3.92  tff(c_8210, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_8203])).
% 10.50/3.92  tff(c_8212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_7758, c_8210])).
% 10.50/3.92  tff(c_8213, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_7754])).
% 10.50/3.92  tff(c_8221, plain, (![B_10]: (k7_relat_1('#skF_5', B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8213, c_10])).
% 10.50/3.92  tff(c_8633, plain, (![B_889]: (k7_relat_1('#skF_5', B_889)=k1_xboole_0 | ~r1_xboole_0(B_889, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_8221])).
% 10.50/3.92  tff(c_8676, plain, (![A_892]: (k7_relat_1('#skF_5', A_892)=k1_xboole_0 | k3_xboole_0(A_892, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_8633])).
% 10.50/3.92  tff(c_8227, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_5', A_13))=k3_xboole_0('#skF_3', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8213, c_18])).
% 10.50/3.92  tff(c_8237, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_5', A_13))=k3_xboole_0('#skF_3', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_8227])).
% 10.50/3.92  tff(c_8685, plain, (![A_892]: (k3_xboole_0('#skF_3', A_892)=k1_relat_1(k1_xboole_0) | k3_xboole_0(A_892, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8676, c_8237])).
% 10.50/3.92  tff(c_8701, plain, (![A_892]: (k3_xboole_0('#skF_3', A_892)=k1_xboole_0 | k3_xboole_0(A_892, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8685])).
% 10.50/3.92  tff(c_8855, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8841, c_8701])).
% 10.50/3.92  tff(c_12, plain, (![B_12, A_11]: (k7_relat_1(B_12, k3_xboole_0(k1_relat_1(B_12), A_11))=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.50/3.92  tff(c_8218, plain, (![A_11]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_11))=k7_relat_1('#skF_5', A_11) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8213, c_12])).
% 10.50/3.92  tff(c_8231, plain, (![A_11]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_11))=k7_relat_1('#skF_5', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_8218])).
% 10.50/3.92  tff(c_8867, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8855, c_8231])).
% 10.50/3.92  tff(c_8542, plain, (![A_11]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_11))=k7_relat_1('#skF_6', A_11) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8537, c_12])).
% 10.50/3.92  tff(c_8555, plain, (![A_11]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_11))=k7_relat_1('#skF_6', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_8542])).
% 10.50/3.92  tff(c_8852, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8841, c_8555])).
% 10.50/3.92  tff(c_8857, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8827, c_8852])).
% 10.50/3.92  tff(c_8787, plain, (![A_898, B_899, C_900, D_901]: (k2_partfun1(A_898, B_899, C_900, D_901)=k7_relat_1(C_900, D_901) | ~m1_subset_1(C_900, k1_zfmisc_1(k2_zfmisc_1(A_898, B_899))) | ~v1_funct_1(C_900))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.50/3.92  tff(c_8791, plain, (![D_901]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_901)=k7_relat_1('#skF_5', D_901) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_8787])).
% 10.50/3.92  tff(c_8797, plain, (![D_901]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_901)=k7_relat_1('#skF_5', D_901))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8791])).
% 10.50/3.92  tff(c_8789, plain, (![D_901]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_901)=k7_relat_1('#skF_6', D_901) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_8787])).
% 10.50/3.92  tff(c_8794, plain, (![D_901]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_901)=k7_relat_1('#skF_6', D_901))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8789])).
% 10.50/3.92  tff(c_7680, plain, (![A_810, B_811, C_812]: (k9_subset_1(A_810, B_811, C_812)=k3_xboole_0(B_811, C_812) | ~m1_subset_1(C_812, k1_zfmisc_1(A_810)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.50/3.92  tff(c_7692, plain, (![B_811]: (k9_subset_1('#skF_1', B_811, '#skF_4')=k3_xboole_0(B_811, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_7680])).
% 10.50/3.92  tff(c_112, plain, (![C_232, A_233, B_234]: (v4_relat_1(C_232, A_233) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.50/3.92  tff(c_119, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_112])).
% 10.50/3.92  tff(c_241, plain, (![B_256, A_257]: (k1_relat_1(B_256)=A_257 | ~v1_partfun1(B_256, A_257) | ~v4_relat_1(B_256, A_257) | ~v1_relat_1(B_256))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.50/3.92  tff(c_247, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_119, c_241])).
% 10.50/3.92  tff(c_253, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_247])).
% 10.50/3.92  tff(c_514, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_253])).
% 10.50/3.92  tff(c_662, plain, (![C_298, A_299, B_300]: (v1_partfun1(C_298, A_299) | ~v1_funct_2(C_298, A_299, B_300) | ~v1_funct_1(C_298) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))) | v1_xboole_0(B_300))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.50/3.92  tff(c_665, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_662])).
% 10.50/3.92  tff(c_671, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_665])).
% 10.50/3.92  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_514, c_671])).
% 10.50/3.92  tff(c_674, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_253])).
% 10.50/3.92  tff(c_685, plain, (![B_10]: (k7_relat_1('#skF_6', B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_674, c_10])).
% 10.50/3.92  tff(c_729, plain, (![B_302]: (k7_relat_1('#skF_6', B_302)=k1_xboole_0 | ~r1_xboole_0(B_302, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_685])).
% 10.50/3.92  tff(c_733, plain, (![A_15]: (k7_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_subset_1(A_15, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_22, c_729])).
% 10.50/3.92  tff(c_860, plain, (![A_314]: (k7_relat_1('#skF_6', A_314)=k1_xboole_0 | ~r1_subset_1(A_314, '#skF_4') | v1_xboole_0(A_314))), inference(negUnitSimplification, [status(thm)], [c_70, c_733])).
% 10.50/3.92  tff(c_863, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_860])).
% 10.50/3.92  tff(c_866, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_863])).
% 10.50/3.92  tff(c_682, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_6', A_13))=k3_xboole_0('#skF_4', A_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_674, c_18])).
% 10.50/3.92  tff(c_694, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_6', A_13))=k3_xboole_0('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_682])).
% 10.50/3.92  tff(c_870, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_866, c_694])).
% 10.50/3.92  tff(c_873, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_870])).
% 10.50/3.92  tff(c_120, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_112])).
% 10.50/3.92  tff(c_244, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_120, c_241])).
% 10.50/3.92  tff(c_250, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_244])).
% 10.50/3.92  tff(c_254, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_250])).
% 10.50/3.92  tff(c_471, plain, (![C_281, A_282, B_283]: (v1_partfun1(C_281, A_282) | ~v1_funct_2(C_281, A_282, B_283) | ~v1_funct_1(C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | v1_xboole_0(B_283))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.50/3.92  tff(c_477, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_471])).
% 10.50/3.92  tff(c_484, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_477])).
% 10.50/3.92  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_254, c_484])).
% 10.50/3.92  tff(c_487, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_250])).
% 10.50/3.92  tff(c_498, plain, (![B_10]: (k7_relat_1('#skF_5', B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_10])).
% 10.50/3.92  tff(c_742, plain, (![B_303]: (k7_relat_1('#skF_5', B_303)=k1_xboole_0 | ~r1_xboole_0(B_303, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_498])).
% 10.50/3.92  tff(c_754, plain, (![A_1]: (k7_relat_1('#skF_5', A_1)=k1_xboole_0 | k3_xboole_0(A_1, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_742])).
% 10.50/3.92  tff(c_679, plain, (![A_11]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_11))=k7_relat_1('#skF_6', A_11) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_674, c_12])).
% 10.50/3.92  tff(c_692, plain, (![A_11]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_11))=k7_relat_1('#skF_6', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_679])).
% 10.50/3.92  tff(c_881, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_873, c_692])).
% 10.50/3.92  tff(c_885, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_866, c_881])).
% 10.50/3.92  tff(c_945, plain, (![A_319]: (k7_relat_1('#skF_5', A_319)=k1_xboole_0 | k3_xboole_0(A_319, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_742])).
% 10.50/3.92  tff(c_495, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_5', A_13))=k3_xboole_0('#skF_3', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_18])).
% 10.50/3.92  tff(c_507, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_5', A_13))=k3_xboole_0('#skF_3', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_495])).
% 10.50/3.92  tff(c_954, plain, (![A_319]: (k3_xboole_0('#skF_3', A_319)=k1_relat_1(k1_xboole_0) | k3_xboole_0(A_319, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_945, c_507])).
% 10.50/3.92  tff(c_1024, plain, (![A_322]: (k3_xboole_0('#skF_3', A_322)=k1_xboole_0 | k3_xboole_0(A_322, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_954])).
% 10.50/3.92  tff(c_1030, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_873, c_1024])).
% 10.50/3.92  tff(c_492, plain, (![A_11]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_11))=k7_relat_1('#skF_5', A_11) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_12])).
% 10.50/3.92  tff(c_505, plain, (![A_11]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_11))=k7_relat_1('#skF_5', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_492])).
% 10.50/3.92  tff(c_809, plain, (![A_307, B_308, C_309, D_310]: (k2_partfun1(A_307, B_308, C_309, D_310)=k7_relat_1(C_309, D_310) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_307, B_308))) | ~v1_funct_1(C_309))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.50/3.92  tff(c_813, plain, (![D_310]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_310)=k7_relat_1('#skF_5', D_310) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_809])).
% 10.50/3.92  tff(c_819, plain, (![D_310]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_310)=k7_relat_1('#skF_5', D_310))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_813])).
% 10.50/3.92  tff(c_811, plain, (![D_310]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_310)=k7_relat_1('#skF_6', D_310) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_809])).
% 10.50/3.92  tff(c_816, plain, (![D_310]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_310)=k7_relat_1('#skF_6', D_310))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_811])).
% 10.50/3.92  tff(c_176, plain, (![A_247, B_248, C_249]: (k9_subset_1(A_247, B_248, C_249)=k3_xboole_0(B_248, C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(A_247)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.50/3.92  tff(c_188, plain, (![B_248]: (k9_subset_1('#skF_1', B_248, '#skF_4')=k3_xboole_0(B_248, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_176])).
% 10.50/3.92  tff(c_52, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 10.50/3.92  tff(c_111, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 10.50/3.92  tff(c_198, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_188, c_111])).
% 10.50/3.92  tff(c_820, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_198])).
% 10.50/3.92  tff(c_1216, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_885, c_1030, c_505, c_819, c_820])).
% 10.50/3.92  tff(c_1219, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_754, c_1216])).
% 10.50/3.92  tff(c_1223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_873, c_1219])).
% 10.50/3.92  tff(c_1225, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 10.50/3.92  tff(c_7717, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7692, c_7692, c_1225])).
% 10.50/3.92  tff(c_8798, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8794, c_7717])).
% 10.50/3.92  tff(c_8944, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8867, c_8857, c_8855, c_8797, c_8855, c_8798])).
% 10.50/3.92  tff(c_9009, plain, (![A_915, D_913, B_912, E_914, F_916, C_911]: (v1_funct_1(k1_tmap_1(A_915, B_912, C_911, D_913, E_914, F_916)) | ~m1_subset_1(F_916, k1_zfmisc_1(k2_zfmisc_1(D_913, B_912))) | ~v1_funct_2(F_916, D_913, B_912) | ~v1_funct_1(F_916) | ~m1_subset_1(E_914, k1_zfmisc_1(k2_zfmisc_1(C_911, B_912))) | ~v1_funct_2(E_914, C_911, B_912) | ~v1_funct_1(E_914) | ~m1_subset_1(D_913, k1_zfmisc_1(A_915)) | v1_xboole_0(D_913) | ~m1_subset_1(C_911, k1_zfmisc_1(A_915)) | v1_xboole_0(C_911) | v1_xboole_0(B_912) | v1_xboole_0(A_915))), inference(cnfTransformation, [status(thm)], [f_183])).
% 10.50/3.92  tff(c_9011, plain, (![A_915, C_911, E_914]: (v1_funct_1(k1_tmap_1(A_915, '#skF_2', C_911, '#skF_4', E_914, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_914, k1_zfmisc_1(k2_zfmisc_1(C_911, '#skF_2'))) | ~v1_funct_2(E_914, C_911, '#skF_2') | ~v1_funct_1(E_914) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_915)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_911, k1_zfmisc_1(A_915)) | v1_xboole_0(C_911) | v1_xboole_0('#skF_2') | v1_xboole_0(A_915))), inference(resolution, [status(thm)], [c_54, c_9009])).
% 10.50/3.92  tff(c_9016, plain, (![A_915, C_911, E_914]: (v1_funct_1(k1_tmap_1(A_915, '#skF_2', C_911, '#skF_4', E_914, '#skF_6')) | ~m1_subset_1(E_914, k1_zfmisc_1(k2_zfmisc_1(C_911, '#skF_2'))) | ~v1_funct_2(E_914, C_911, '#skF_2') | ~v1_funct_1(E_914) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_915)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_911, k1_zfmisc_1(A_915)) | v1_xboole_0(C_911) | v1_xboole_0('#skF_2') | v1_xboole_0(A_915))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_9011])).
% 10.50/3.92  tff(c_9022, plain, (![A_917, C_918, E_919]: (v1_funct_1(k1_tmap_1(A_917, '#skF_2', C_918, '#skF_4', E_919, '#skF_6')) | ~m1_subset_1(E_919, k1_zfmisc_1(k2_zfmisc_1(C_918, '#skF_2'))) | ~v1_funct_2(E_919, C_918, '#skF_2') | ~v1_funct_1(E_919) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_917)) | ~m1_subset_1(C_918, k1_zfmisc_1(A_917)) | v1_xboole_0(C_918) | v1_xboole_0(A_917))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_9016])).
% 10.50/3.92  tff(c_9026, plain, (![A_917]: (v1_funct_1(k1_tmap_1(A_917, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_917)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_917)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_917))), inference(resolution, [status(thm)], [c_60, c_9022])).
% 10.50/3.92  tff(c_9033, plain, (![A_917]: (v1_funct_1(k1_tmap_1(A_917, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_917)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_917)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_917))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_9026])).
% 10.50/3.92  tff(c_9584, plain, (![A_951]: (v1_funct_1(k1_tmap_1(A_951, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_951)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_951)) | v1_xboole_0(A_951))), inference(negUnitSimplification, [status(thm)], [c_74, c_9033])).
% 10.50/3.92  tff(c_9587, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_9584])).
% 10.50/3.92  tff(c_9590, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_9587])).
% 10.50/3.92  tff(c_9591, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_9590])).
% 10.50/3.92  tff(c_48, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_183])).
% 10.50/3.92  tff(c_46, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_183])).
% 10.50/3.92  tff(c_10033, plain, (![E_976, D_980, F_978, C_979, B_977, A_975]: (k2_partfun1(k4_subset_1(A_975, C_979, D_980), B_977, k1_tmap_1(A_975, B_977, C_979, D_980, E_976, F_978), C_979)=E_976 | ~m1_subset_1(k1_tmap_1(A_975, B_977, C_979, D_980, E_976, F_978), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_975, C_979, D_980), B_977))) | ~v1_funct_2(k1_tmap_1(A_975, B_977, C_979, D_980, E_976, F_978), k4_subset_1(A_975, C_979, D_980), B_977) | ~v1_funct_1(k1_tmap_1(A_975, B_977, C_979, D_980, E_976, F_978)) | k2_partfun1(D_980, B_977, F_978, k9_subset_1(A_975, C_979, D_980))!=k2_partfun1(C_979, B_977, E_976, k9_subset_1(A_975, C_979, D_980)) | ~m1_subset_1(F_978, k1_zfmisc_1(k2_zfmisc_1(D_980, B_977))) | ~v1_funct_2(F_978, D_980, B_977) | ~v1_funct_1(F_978) | ~m1_subset_1(E_976, k1_zfmisc_1(k2_zfmisc_1(C_979, B_977))) | ~v1_funct_2(E_976, C_979, B_977) | ~v1_funct_1(E_976) | ~m1_subset_1(D_980, k1_zfmisc_1(A_975)) | v1_xboole_0(D_980) | ~m1_subset_1(C_979, k1_zfmisc_1(A_975)) | v1_xboole_0(C_979) | v1_xboole_0(B_977) | v1_xboole_0(A_975))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.50/3.92  tff(c_11507, plain, (![B_1097, A_1100, F_1101, C_1096, D_1098, E_1099]: (k2_partfun1(k4_subset_1(A_1100, C_1096, D_1098), B_1097, k1_tmap_1(A_1100, B_1097, C_1096, D_1098, E_1099, F_1101), C_1096)=E_1099 | ~v1_funct_2(k1_tmap_1(A_1100, B_1097, C_1096, D_1098, E_1099, F_1101), k4_subset_1(A_1100, C_1096, D_1098), B_1097) | ~v1_funct_1(k1_tmap_1(A_1100, B_1097, C_1096, D_1098, E_1099, F_1101)) | k2_partfun1(D_1098, B_1097, F_1101, k9_subset_1(A_1100, C_1096, D_1098))!=k2_partfun1(C_1096, B_1097, E_1099, k9_subset_1(A_1100, C_1096, D_1098)) | ~m1_subset_1(F_1101, k1_zfmisc_1(k2_zfmisc_1(D_1098, B_1097))) | ~v1_funct_2(F_1101, D_1098, B_1097) | ~v1_funct_1(F_1101) | ~m1_subset_1(E_1099, k1_zfmisc_1(k2_zfmisc_1(C_1096, B_1097))) | ~v1_funct_2(E_1099, C_1096, B_1097) | ~v1_funct_1(E_1099) | ~m1_subset_1(D_1098, k1_zfmisc_1(A_1100)) | v1_xboole_0(D_1098) | ~m1_subset_1(C_1096, k1_zfmisc_1(A_1100)) | v1_xboole_0(C_1096) | v1_xboole_0(B_1097) | v1_xboole_0(A_1100))), inference(resolution, [status(thm)], [c_46, c_10033])).
% 10.50/3.92  tff(c_13487, plain, (![B_1195, A_1198, E_1197, F_1199, C_1194, D_1196]: (k2_partfun1(k4_subset_1(A_1198, C_1194, D_1196), B_1195, k1_tmap_1(A_1198, B_1195, C_1194, D_1196, E_1197, F_1199), C_1194)=E_1197 | ~v1_funct_1(k1_tmap_1(A_1198, B_1195, C_1194, D_1196, E_1197, F_1199)) | k2_partfun1(D_1196, B_1195, F_1199, k9_subset_1(A_1198, C_1194, D_1196))!=k2_partfun1(C_1194, B_1195, E_1197, k9_subset_1(A_1198, C_1194, D_1196)) | ~m1_subset_1(F_1199, k1_zfmisc_1(k2_zfmisc_1(D_1196, B_1195))) | ~v1_funct_2(F_1199, D_1196, B_1195) | ~v1_funct_1(F_1199) | ~m1_subset_1(E_1197, k1_zfmisc_1(k2_zfmisc_1(C_1194, B_1195))) | ~v1_funct_2(E_1197, C_1194, B_1195) | ~v1_funct_1(E_1197) | ~m1_subset_1(D_1196, k1_zfmisc_1(A_1198)) | v1_xboole_0(D_1196) | ~m1_subset_1(C_1194, k1_zfmisc_1(A_1198)) | v1_xboole_0(C_1194) | v1_xboole_0(B_1195) | v1_xboole_0(A_1198))), inference(resolution, [status(thm)], [c_48, c_11507])).
% 10.50/3.92  tff(c_13491, plain, (![A_1198, C_1194, E_1197]: (k2_partfun1(k4_subset_1(A_1198, C_1194, '#skF_4'), '#skF_2', k1_tmap_1(A_1198, '#skF_2', C_1194, '#skF_4', E_1197, '#skF_6'), C_1194)=E_1197 | ~v1_funct_1(k1_tmap_1(A_1198, '#skF_2', C_1194, '#skF_4', E_1197, '#skF_6')) | k2_partfun1(C_1194, '#skF_2', E_1197, k9_subset_1(A_1198, C_1194, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1198, C_1194, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1197, k1_zfmisc_1(k2_zfmisc_1(C_1194, '#skF_2'))) | ~v1_funct_2(E_1197, C_1194, '#skF_2') | ~v1_funct_1(E_1197) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1198)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1194, k1_zfmisc_1(A_1198)) | v1_xboole_0(C_1194) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1198))), inference(resolution, [status(thm)], [c_54, c_13487])).
% 10.50/3.92  tff(c_13497, plain, (![A_1198, C_1194, E_1197]: (k2_partfun1(k4_subset_1(A_1198, C_1194, '#skF_4'), '#skF_2', k1_tmap_1(A_1198, '#skF_2', C_1194, '#skF_4', E_1197, '#skF_6'), C_1194)=E_1197 | ~v1_funct_1(k1_tmap_1(A_1198, '#skF_2', C_1194, '#skF_4', E_1197, '#skF_6')) | k2_partfun1(C_1194, '#skF_2', E_1197, k9_subset_1(A_1198, C_1194, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1198, C_1194, '#skF_4')) | ~m1_subset_1(E_1197, k1_zfmisc_1(k2_zfmisc_1(C_1194, '#skF_2'))) | ~v1_funct_2(E_1197, C_1194, '#skF_2') | ~v1_funct_1(E_1197) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1198)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1194, k1_zfmisc_1(A_1198)) | v1_xboole_0(C_1194) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1198))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_8794, c_13491])).
% 10.50/3.92  tff(c_13962, plain, (![A_1230, C_1231, E_1232]: (k2_partfun1(k4_subset_1(A_1230, C_1231, '#skF_4'), '#skF_2', k1_tmap_1(A_1230, '#skF_2', C_1231, '#skF_4', E_1232, '#skF_6'), C_1231)=E_1232 | ~v1_funct_1(k1_tmap_1(A_1230, '#skF_2', C_1231, '#skF_4', E_1232, '#skF_6')) | k2_partfun1(C_1231, '#skF_2', E_1232, k9_subset_1(A_1230, C_1231, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1230, C_1231, '#skF_4')) | ~m1_subset_1(E_1232, k1_zfmisc_1(k2_zfmisc_1(C_1231, '#skF_2'))) | ~v1_funct_2(E_1232, C_1231, '#skF_2') | ~v1_funct_1(E_1232) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1230)) | ~m1_subset_1(C_1231, k1_zfmisc_1(A_1230)) | v1_xboole_0(C_1231) | v1_xboole_0(A_1230))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_13497])).
% 10.50/3.92  tff(c_13969, plain, (![A_1230]: (k2_partfun1(k4_subset_1(A_1230, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1230, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1230, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1230, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1230, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1230)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1230)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1230))), inference(resolution, [status(thm)], [c_60, c_13962])).
% 10.50/3.92  tff(c_13979, plain, (![A_1230]: (k2_partfun1(k4_subset_1(A_1230, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1230, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1230, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1230, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1230, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1230)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1230)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1230))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_8797, c_13969])).
% 10.50/3.92  tff(c_14962, plain, (![A_1253]: (k2_partfun1(k4_subset_1(A_1253, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1253, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1253, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1253, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1253, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1253)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1253)) | v1_xboole_0(A_1253))), inference(negUnitSimplification, [status(thm)], [c_74, c_13979])).
% 10.50/3.92  tff(c_1360, plain, (![B_378, A_379]: (k1_relat_1(B_378)=A_379 | ~v1_partfun1(B_378, A_379) | ~v4_relat_1(B_378, A_379) | ~v1_relat_1(B_378))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.50/3.92  tff(c_1366, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1237, c_1360])).
% 10.50/3.92  tff(c_1372, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_1366])).
% 10.50/3.92  tff(c_1797, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1372])).
% 10.50/3.92  tff(c_1996, plain, (![C_436, A_437, B_438]: (v1_partfun1(C_436, A_437) | ~v1_funct_2(C_436, A_437, B_438) | ~v1_funct_1(C_436) | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_437, B_438))) | v1_xboole_0(B_438))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.50/3.92  tff(c_1999, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1996])).
% 10.50/3.92  tff(c_2005, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1999])).
% 10.50/3.92  tff(c_2007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1797, c_2005])).
% 10.50/3.92  tff(c_2008, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1372])).
% 10.50/3.92  tff(c_2016, plain, (![B_10]: (k7_relat_1('#skF_6', B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2008, c_10])).
% 10.50/3.92  tff(c_2076, plain, (![B_441]: (k7_relat_1('#skF_6', B_441)=k1_xboole_0 | ~r1_xboole_0(B_441, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2016])).
% 10.50/3.92  tff(c_2080, plain, (![A_15]: (k7_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_subset_1(A_15, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_22, c_2076])).
% 10.50/3.92  tff(c_2173, plain, (![A_451]: (k7_relat_1('#skF_6', A_451)=k1_xboole_0 | ~r1_subset_1(A_451, '#skF_4') | v1_xboole_0(A_451))), inference(negUnitSimplification, [status(thm)], [c_70, c_2080])).
% 10.50/3.92  tff(c_2176, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2173])).
% 10.50/3.92  tff(c_2179, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_2176])).
% 10.50/3.92  tff(c_2022, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_6', A_13))=k3_xboole_0('#skF_4', A_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2008, c_18])).
% 10.50/3.92  tff(c_2032, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_6', A_13))=k3_xboole_0('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2022])).
% 10.50/3.92  tff(c_2183, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2179, c_2032])).
% 10.50/3.92  tff(c_2186, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2183])).
% 10.50/3.92  tff(c_1363, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1238, c_1360])).
% 10.50/3.92  tff(c_1369, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1363])).
% 10.50/3.92  tff(c_1373, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1369])).
% 10.50/3.92  tff(c_1750, plain, (![C_417, A_418, B_419]: (v1_partfun1(C_417, A_418) | ~v1_funct_2(C_417, A_418, B_419) | ~v1_funct_1(C_417) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_418, B_419))) | v1_xboole_0(B_419))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.50/3.92  tff(c_1756, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1750])).
% 10.50/3.92  tff(c_1763, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1756])).
% 10.50/3.92  tff(c_1765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1373, c_1763])).
% 10.50/3.92  tff(c_1766, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1369])).
% 10.50/3.92  tff(c_1774, plain, (![B_10]: (k7_relat_1('#skF_5', B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1766, c_10])).
% 10.50/3.92  tff(c_2035, plain, (![B_439]: (k7_relat_1('#skF_5', B_439)=k1_xboole_0 | ~r1_xboole_0(B_439, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1774])).
% 10.50/3.92  tff(c_2326, plain, (![A_459]: (k7_relat_1('#skF_5', A_459)=k1_xboole_0 | k3_xboole_0(A_459, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2035])).
% 10.50/3.92  tff(c_1780, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_5', A_13))=k3_xboole_0('#skF_3', A_13) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1766, c_18])).
% 10.50/3.92  tff(c_1790, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_5', A_13))=k3_xboole_0('#skF_3', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1780])).
% 10.50/3.92  tff(c_2335, plain, (![A_459]: (k3_xboole_0('#skF_3', A_459)=k1_relat_1(k1_xboole_0) | k3_xboole_0(A_459, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2326, c_1790])).
% 10.50/3.92  tff(c_2362, plain, (![A_461]: (k3_xboole_0('#skF_3', A_461)=k1_xboole_0 | k3_xboole_0(A_461, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2335])).
% 10.50/3.92  tff(c_2368, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2186, c_2362])).
% 10.50/3.92  tff(c_1771, plain, (![A_11]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_11))=k7_relat_1('#skF_5', A_11) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1766, c_12])).
% 10.50/3.92  tff(c_1784, plain, (![A_11]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_11))=k7_relat_1('#skF_5', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1771])).
% 10.50/3.92  tff(c_2377, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2368, c_1784])).
% 10.50/3.92  tff(c_2013, plain, (![A_11]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_11))=k7_relat_1('#skF_6', A_11) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2008, c_12])).
% 10.50/3.92  tff(c_2026, plain, (![A_11]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_11))=k7_relat_1('#skF_6', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2013])).
% 10.50/3.92  tff(c_2191, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2186, c_2026])).
% 10.50/3.92  tff(c_2194, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2179, c_2191])).
% 10.50/3.92  tff(c_2130, plain, (![A_444, B_445, C_446, D_447]: (k2_partfun1(A_444, B_445, C_446, D_447)=k7_relat_1(C_446, D_447) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_444, B_445))) | ~v1_funct_1(C_446))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.50/3.92  tff(c_2134, plain, (![D_447]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_447)=k7_relat_1('#skF_5', D_447) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_2130])).
% 10.50/3.92  tff(c_2140, plain, (![D_447]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_447)=k7_relat_1('#skF_5', D_447))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2134])).
% 10.50/3.92  tff(c_2132, plain, (![D_447]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_447)=k7_relat_1('#skF_6', D_447) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_2130])).
% 10.50/3.92  tff(c_2137, plain, (![D_447]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_447)=k7_relat_1('#skF_6', D_447))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2132])).
% 10.50/3.92  tff(c_1295, plain, (![A_369, B_370, C_371]: (k9_subset_1(A_369, B_370, C_371)=k3_xboole_0(B_370, C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(A_369)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.50/3.92  tff(c_1307, plain, (![B_370]: (k9_subset_1('#skF_1', B_370, '#skF_4')=k3_xboole_0(B_370, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1295])).
% 10.50/3.92  tff(c_1332, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1307, c_1307, c_1225])).
% 10.50/3.92  tff(c_2141, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_1332])).
% 10.50/3.92  tff(c_2550, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2377, c_2194, c_2368, c_2140, c_2368, c_2141])).
% 10.50/3.92  tff(c_2384, plain, (![D_464, F_467, E_465, A_466, B_463, C_462]: (v1_funct_1(k1_tmap_1(A_466, B_463, C_462, D_464, E_465, F_467)) | ~m1_subset_1(F_467, k1_zfmisc_1(k2_zfmisc_1(D_464, B_463))) | ~v1_funct_2(F_467, D_464, B_463) | ~v1_funct_1(F_467) | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(C_462, B_463))) | ~v1_funct_2(E_465, C_462, B_463) | ~v1_funct_1(E_465) | ~m1_subset_1(D_464, k1_zfmisc_1(A_466)) | v1_xboole_0(D_464) | ~m1_subset_1(C_462, k1_zfmisc_1(A_466)) | v1_xboole_0(C_462) | v1_xboole_0(B_463) | v1_xboole_0(A_466))), inference(cnfTransformation, [status(thm)], [f_183])).
% 10.50/3.92  tff(c_2386, plain, (![A_466, C_462, E_465]: (v1_funct_1(k1_tmap_1(A_466, '#skF_2', C_462, '#skF_4', E_465, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(C_462, '#skF_2'))) | ~v1_funct_2(E_465, C_462, '#skF_2') | ~v1_funct_1(E_465) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_466)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_462, k1_zfmisc_1(A_466)) | v1_xboole_0(C_462) | v1_xboole_0('#skF_2') | v1_xboole_0(A_466))), inference(resolution, [status(thm)], [c_54, c_2384])).
% 10.50/3.92  tff(c_2391, plain, (![A_466, C_462, E_465]: (v1_funct_1(k1_tmap_1(A_466, '#skF_2', C_462, '#skF_4', E_465, '#skF_6')) | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(C_462, '#skF_2'))) | ~v1_funct_2(E_465, C_462, '#skF_2') | ~v1_funct_1(E_465) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_466)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_462, k1_zfmisc_1(A_466)) | v1_xboole_0(C_462) | v1_xboole_0('#skF_2') | v1_xboole_0(A_466))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2386])).
% 10.50/3.92  tff(c_2424, plain, (![A_468, C_469, E_470]: (v1_funct_1(k1_tmap_1(A_468, '#skF_2', C_469, '#skF_4', E_470, '#skF_6')) | ~m1_subset_1(E_470, k1_zfmisc_1(k2_zfmisc_1(C_469, '#skF_2'))) | ~v1_funct_2(E_470, C_469, '#skF_2') | ~v1_funct_1(E_470) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_468)) | ~m1_subset_1(C_469, k1_zfmisc_1(A_468)) | v1_xboole_0(C_469) | v1_xboole_0(A_468))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_2391])).
% 10.50/3.92  tff(c_2428, plain, (![A_468]: (v1_funct_1(k1_tmap_1(A_468, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_468)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_468)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_468))), inference(resolution, [status(thm)], [c_60, c_2424])).
% 10.50/3.92  tff(c_2435, plain, (![A_468]: (v1_funct_1(k1_tmap_1(A_468, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_468)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_468)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_468))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2428])).
% 10.50/3.92  tff(c_2586, plain, (![A_492]: (v1_funct_1(k1_tmap_1(A_492, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_492)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_492)) | v1_xboole_0(A_492))), inference(negUnitSimplification, [status(thm)], [c_74, c_2435])).
% 10.50/3.92  tff(c_2589, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_2586])).
% 10.50/3.92  tff(c_2592, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2589])).
% 10.50/3.92  tff(c_2593, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_2592])).
% 10.50/3.92  tff(c_2744, plain, (![E_498, A_497, D_502, C_501, F_500, B_499]: (k2_partfun1(k4_subset_1(A_497, C_501, D_502), B_499, k1_tmap_1(A_497, B_499, C_501, D_502, E_498, F_500), D_502)=F_500 | ~m1_subset_1(k1_tmap_1(A_497, B_499, C_501, D_502, E_498, F_500), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_497, C_501, D_502), B_499))) | ~v1_funct_2(k1_tmap_1(A_497, B_499, C_501, D_502, E_498, F_500), k4_subset_1(A_497, C_501, D_502), B_499) | ~v1_funct_1(k1_tmap_1(A_497, B_499, C_501, D_502, E_498, F_500)) | k2_partfun1(D_502, B_499, F_500, k9_subset_1(A_497, C_501, D_502))!=k2_partfun1(C_501, B_499, E_498, k9_subset_1(A_497, C_501, D_502)) | ~m1_subset_1(F_500, k1_zfmisc_1(k2_zfmisc_1(D_502, B_499))) | ~v1_funct_2(F_500, D_502, B_499) | ~v1_funct_1(F_500) | ~m1_subset_1(E_498, k1_zfmisc_1(k2_zfmisc_1(C_501, B_499))) | ~v1_funct_2(E_498, C_501, B_499) | ~v1_funct_1(E_498) | ~m1_subset_1(D_502, k1_zfmisc_1(A_497)) | v1_xboole_0(D_502) | ~m1_subset_1(C_501, k1_zfmisc_1(A_497)) | v1_xboole_0(C_501) | v1_xboole_0(B_499) | v1_xboole_0(A_497))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.50/3.92  tff(c_4969, plain, (![C_655, B_656, A_659, F_660, D_657, E_658]: (k2_partfun1(k4_subset_1(A_659, C_655, D_657), B_656, k1_tmap_1(A_659, B_656, C_655, D_657, E_658, F_660), D_657)=F_660 | ~v1_funct_2(k1_tmap_1(A_659, B_656, C_655, D_657, E_658, F_660), k4_subset_1(A_659, C_655, D_657), B_656) | ~v1_funct_1(k1_tmap_1(A_659, B_656, C_655, D_657, E_658, F_660)) | k2_partfun1(D_657, B_656, F_660, k9_subset_1(A_659, C_655, D_657))!=k2_partfun1(C_655, B_656, E_658, k9_subset_1(A_659, C_655, D_657)) | ~m1_subset_1(F_660, k1_zfmisc_1(k2_zfmisc_1(D_657, B_656))) | ~v1_funct_2(F_660, D_657, B_656) | ~v1_funct_1(F_660) | ~m1_subset_1(E_658, k1_zfmisc_1(k2_zfmisc_1(C_655, B_656))) | ~v1_funct_2(E_658, C_655, B_656) | ~v1_funct_1(E_658) | ~m1_subset_1(D_657, k1_zfmisc_1(A_659)) | v1_xboole_0(D_657) | ~m1_subset_1(C_655, k1_zfmisc_1(A_659)) | v1_xboole_0(C_655) | v1_xboole_0(B_656) | v1_xboole_0(A_659))), inference(resolution, [status(thm)], [c_46, c_2744])).
% 10.50/3.92  tff(c_5962, plain, (![D_720, B_719, A_722, F_723, C_718, E_721]: (k2_partfun1(k4_subset_1(A_722, C_718, D_720), B_719, k1_tmap_1(A_722, B_719, C_718, D_720, E_721, F_723), D_720)=F_723 | ~v1_funct_1(k1_tmap_1(A_722, B_719, C_718, D_720, E_721, F_723)) | k2_partfun1(D_720, B_719, F_723, k9_subset_1(A_722, C_718, D_720))!=k2_partfun1(C_718, B_719, E_721, k9_subset_1(A_722, C_718, D_720)) | ~m1_subset_1(F_723, k1_zfmisc_1(k2_zfmisc_1(D_720, B_719))) | ~v1_funct_2(F_723, D_720, B_719) | ~v1_funct_1(F_723) | ~m1_subset_1(E_721, k1_zfmisc_1(k2_zfmisc_1(C_718, B_719))) | ~v1_funct_2(E_721, C_718, B_719) | ~v1_funct_1(E_721) | ~m1_subset_1(D_720, k1_zfmisc_1(A_722)) | v1_xboole_0(D_720) | ~m1_subset_1(C_718, k1_zfmisc_1(A_722)) | v1_xboole_0(C_718) | v1_xboole_0(B_719) | v1_xboole_0(A_722))), inference(resolution, [status(thm)], [c_48, c_4969])).
% 10.50/3.92  tff(c_5966, plain, (![A_722, C_718, E_721]: (k2_partfun1(k4_subset_1(A_722, C_718, '#skF_4'), '#skF_2', k1_tmap_1(A_722, '#skF_2', C_718, '#skF_4', E_721, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_722, '#skF_2', C_718, '#skF_4', E_721, '#skF_6')) | k2_partfun1(C_718, '#skF_2', E_721, k9_subset_1(A_722, C_718, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_722, C_718, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_721, k1_zfmisc_1(k2_zfmisc_1(C_718, '#skF_2'))) | ~v1_funct_2(E_721, C_718, '#skF_2') | ~v1_funct_1(E_721) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_722)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_718, k1_zfmisc_1(A_722)) | v1_xboole_0(C_718) | v1_xboole_0('#skF_2') | v1_xboole_0(A_722))), inference(resolution, [status(thm)], [c_54, c_5962])).
% 10.50/3.92  tff(c_5972, plain, (![A_722, C_718, E_721]: (k2_partfun1(k4_subset_1(A_722, C_718, '#skF_4'), '#skF_2', k1_tmap_1(A_722, '#skF_2', C_718, '#skF_4', E_721, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_722, '#skF_2', C_718, '#skF_4', E_721, '#skF_6')) | k2_partfun1(C_718, '#skF_2', E_721, k9_subset_1(A_722, C_718, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_722, C_718, '#skF_4')) | ~m1_subset_1(E_721, k1_zfmisc_1(k2_zfmisc_1(C_718, '#skF_2'))) | ~v1_funct_2(E_721, C_718, '#skF_2') | ~v1_funct_1(E_721) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_722)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_718, k1_zfmisc_1(A_722)) | v1_xboole_0(C_718) | v1_xboole_0('#skF_2') | v1_xboole_0(A_722))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2137, c_5966])).
% 10.50/3.92  tff(c_7315, plain, (![A_772, C_773, E_774]: (k2_partfun1(k4_subset_1(A_772, C_773, '#skF_4'), '#skF_2', k1_tmap_1(A_772, '#skF_2', C_773, '#skF_4', E_774, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_772, '#skF_2', C_773, '#skF_4', E_774, '#skF_6')) | k2_partfun1(C_773, '#skF_2', E_774, k9_subset_1(A_772, C_773, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_772, C_773, '#skF_4')) | ~m1_subset_1(E_774, k1_zfmisc_1(k2_zfmisc_1(C_773, '#skF_2'))) | ~v1_funct_2(E_774, C_773, '#skF_2') | ~v1_funct_1(E_774) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_772)) | ~m1_subset_1(C_773, k1_zfmisc_1(A_772)) | v1_xboole_0(C_773) | v1_xboole_0(A_772))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_5972])).
% 10.50/3.92  tff(c_7322, plain, (![A_772]: (k2_partfun1(k4_subset_1(A_772, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_772, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_772, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_772, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_772, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_772)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_772)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_772))), inference(resolution, [status(thm)], [c_60, c_7315])).
% 10.50/3.92  tff(c_7332, plain, (![A_772]: (k2_partfun1(k4_subset_1(A_772, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_772, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_772, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_772, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_772, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_772)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_772)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_772))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2140, c_7322])).
% 10.50/3.92  tff(c_7617, plain, (![A_802]: (k2_partfun1(k4_subset_1(A_802, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_802, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_802, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_802, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_802, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_802)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_802)) | v1_xboole_0(A_802))), inference(negUnitSimplification, [status(thm)], [c_74, c_7332])).
% 10.50/3.92  tff(c_1224, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 10.50/3.92  tff(c_1261, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1224])).
% 10.50/3.92  tff(c_7628, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7617, c_1261])).
% 10.50/3.92  tff(c_7642, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2550, c_2194, c_2368, c_1784, c_1307, c_1307, c_2593, c_7628])).
% 10.50/3.92  tff(c_7644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_7642])).
% 10.50/3.92  tff(c_7645, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1224])).
% 10.50/3.92  tff(c_14971, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14962, c_7645])).
% 10.50/3.92  tff(c_14982, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_8944, c_8857, c_8855, c_8231, c_7692, c_7692, c_9591, c_14971])).
% 10.50/3.92  tff(c_14984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_14982])).
% 10.50/3.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.50/3.92  
% 10.50/3.92  Inference rules
% 10.50/3.92  ----------------------
% 10.50/3.92  #Ref     : 0
% 10.50/3.92  #Sup     : 3308
% 10.50/3.92  #Fact    : 0
% 10.50/3.92  #Define  : 0
% 10.50/3.92  #Split   : 43
% 10.50/3.92  #Chain   : 0
% 10.50/3.92  #Close   : 0
% 10.50/3.92  
% 10.50/3.92  Ordering : KBO
% 10.50/3.92  
% 10.50/3.92  Simplification rules
% 10.50/3.92  ----------------------
% 10.50/3.92  #Subsume      : 1556
% 10.50/3.92  #Demod        : 7362
% 10.50/3.92  #Tautology    : 735
% 10.50/3.92  #SimpNegUnit  : 188
% 10.50/3.92  #BackRed      : 15
% 10.50/3.92  
% 10.50/3.92  #Partial instantiations: 0
% 10.50/3.92  #Strategies tried      : 1
% 10.50/3.92  
% 10.50/3.92  Timing (in seconds)
% 10.50/3.92  ----------------------
% 10.50/3.93  Preprocessing        : 0.44
% 10.50/3.93  Parsing              : 0.22
% 10.50/3.93  CNF conversion       : 0.06
% 10.50/3.93  Main loop            : 2.61
% 10.50/3.93  Inferencing          : 0.77
% 10.50/3.93  Reduction            : 1.13
% 10.50/3.93  Demodulation         : 0.89
% 10.50/3.93  BG Simplification    : 0.07
% 10.50/3.93  Subsumption          : 0.50
% 10.50/3.93  Abstraction          : 0.11
% 10.50/3.93  MUC search           : 0.00
% 10.50/3.93  Cooper               : 0.00
% 10.50/3.93  Total                : 3.13
% 10.50/3.93  Index Insertion      : 0.00
% 10.50/3.93  Index Deletion       : 0.00
% 10.50/3.93  Index Matching       : 0.00
% 10.50/3.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
