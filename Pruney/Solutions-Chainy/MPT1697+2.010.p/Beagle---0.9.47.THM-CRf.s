%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:09 EST 2020

% Result     : Theorem 14.17s
% Output     : CNFRefutation 14.70s
% Verified   : 
% Statistics : Number of formulae       :  524 (3609 expanded)
%              Number of leaves         :   52 (1199 expanded)
%              Depth                    :   18
%              Number of atoms          : 1329 (14453 expanded)
%              Number of equality atoms :  407 (2947 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_253,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_211,axiom,(
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

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_177,axiom,(
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

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_5782,plain,(
    ! [C_763,A_764,B_765] :
      ( v1_relat_1(C_763)
      | ~ m1_subset_1(C_763,k1_zfmisc_1(k2_zfmisc_1(A_764,B_765))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5789,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_5782])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_5791,plain,(
    ! [C_766,A_767,B_768] :
      ( v4_relat_1(C_766,A_767)
      | ~ m1_subset_1(C_766,k1_zfmisc_1(k2_zfmisc_1(A_767,B_768))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5798,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_5791])).

tff(c_20296,plain,(
    ! [B_1678,A_1679] :
      ( k1_relat_1(B_1678) = A_1679
      | ~ v1_partfun1(B_1678,A_1679)
      | ~ v4_relat_1(B_1678,A_1679)
      | ~ v1_relat_1(B_1678) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_20305,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5798,c_20296])).

tff(c_20314,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_20305])).

tff(c_21105,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20314])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_70,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_21394,plain,(
    ! [C_1768,A_1769,B_1770] :
      ( v1_partfun1(C_1768,A_1769)
      | ~ v1_funct_2(C_1768,A_1769,B_1770)
      | ~ v1_funct_1(C_1768)
      | ~ m1_subset_1(C_1768,k1_zfmisc_1(k2_zfmisc_1(A_1769,B_1770)))
      | v1_xboole_0(B_1770) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_21397,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_21394])).

tff(c_21403,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_21397])).

tff(c_21405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_21105,c_21403])).

tff(c_21406,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20314])).

tff(c_32,plain,(
    ! [B_26,A_25] :
      ( r1_xboole_0(k1_relat_1(B_26),A_25)
      | k7_relat_1(B_26,A_25) != k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_21426,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21406,c_32])).

tff(c_21599,plain,(
    ! [A_1783] :
      ( r1_xboole_0('#skF_4',A_1783)
      | k7_relat_1('#skF_6',A_1783) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_21426])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_80,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | ~ r1_subset_1(A_27,B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5800,plain,(
    ! [B_769,A_770] :
      ( r1_tarski(k1_relat_1(B_769),A_770)
      | ~ v4_relat_1(B_769,A_770)
      | ~ v1_relat_1(B_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5803,plain,(
    ! [A_770] :
      ( r1_tarski(k1_xboole_0,A_770)
      | ~ v4_relat_1(k1_xboole_0,A_770)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5800])).

tff(c_5804,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5803])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6027,plain,(
    ! [B_804,A_805] :
      ( k1_relat_1(B_804) = A_805
      | ~ v1_partfun1(B_804,A_805)
      | ~ v4_relat_1(B_804,A_805)
      | ~ v1_relat_1(B_804) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6033,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5798,c_6027])).

tff(c_6039,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_6033])).

tff(c_6052,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6039])).

tff(c_6172,plain,(
    ! [C_827,A_828,B_829] :
      ( v1_partfun1(C_827,A_828)
      | ~ v1_funct_2(C_827,A_828,B_829)
      | ~ v1_funct_1(C_827)
      | ~ m1_subset_1(C_827,k1_zfmisc_1(k2_zfmisc_1(A_828,B_829)))
      | v1_xboole_0(B_829) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6175,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_6172])).

tff(c_6181,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_6175])).

tff(c_6183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_6052,c_6181])).

tff(c_6184,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6039])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( k7_relat_1(B_26,A_25) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6192,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_6',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_25)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6184,c_30])).

tff(c_6290,plain,(
    ! [A_834] :
      ( k7_relat_1('#skF_6',A_834) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_834) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_6192])).

tff(c_6376,plain,(
    ! [B_840] :
      ( k7_relat_1('#skF_6',B_840) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_840) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_6290])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6385,plain,(
    ! [B_840] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0('#skF_4',B_840) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6376,c_16])).

tff(c_6393,plain,(
    ! [B_840] :
      ( v1_relat_1(k1_xboole_0)
      | k3_xboole_0('#skF_4',B_840) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_6385])).

tff(c_6394,plain,(
    ! [B_840] : k3_xboole_0('#skF_4',B_840) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5804,c_6393])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_xboole_0(k1_relat_1(B_16),A_15)
      | k9_relat_1(B_16,A_15) != k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6195,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6184,c_20])).

tff(c_6258,plain,(
    ! [A_832] :
      ( r1_xboole_0('#skF_4',A_832)
      | k9_relat_1('#skF_6',A_832) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_6195])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6273,plain,(
    ! [A_832] :
      ( k3_xboole_0('#skF_4',A_832) = k1_xboole_0
      | k9_relat_1('#skF_6',A_832) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6258,c_2])).

tff(c_6396,plain,(
    ! [A_832] : k9_relat_1('#skF_6',A_832) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6394,c_6273])).

tff(c_5899,plain,(
    ! [B_787,A_788] :
      ( k9_relat_1(B_787,A_788) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_787),A_788)
      | ~ v1_relat_1(B_787) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5989,plain,(
    ! [B_800,A_801] :
      ( k9_relat_1(B_800,A_801) = k1_xboole_0
      | k7_relat_1(B_800,A_801) != k1_xboole_0
      | ~ v1_relat_1(B_800) ) ),
    inference(resolution,[status(thm)],[c_32,c_5899])).

tff(c_5997,plain,(
    ! [A_801] :
      ( k9_relat_1('#skF_6',A_801) = k1_xboole_0
      | k7_relat_1('#skF_6',A_801) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5789,c_5989])).

tff(c_6399,plain,(
    ! [A_801] : k7_relat_1('#skF_6',A_801) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6396,c_5997])).

tff(c_24,plain,(
    ! [A_22,B_24] :
      ( k7_relat_1(A_22,B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,k1_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6198,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6184,c_24])).

tff(c_6220,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_6198])).

tff(c_6429,plain,(
    ! [B_849] : ~ r1_xboole_0(B_849,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_6399,c_6220])).

tff(c_6437,plain,(
    ! [A_27] :
      ( ~ r1_subset_1(A_27,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_36,c_6429])).

tff(c_6454,plain,(
    ! [A_852] :
      ( ~ r1_subset_1(A_852,'#skF_4')
      | v1_xboole_0(A_852) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_6437])).

tff(c_6457,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_6454])).

tff(c_6461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_6457])).

tff(c_6463,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5803])).

tff(c_6509,plain,(
    ! [A_864,B_865] :
      ( k7_relat_1(A_864,B_865) = k1_xboole_0
      | ~ r1_xboole_0(B_865,k1_relat_1(A_864))
      | ~ v1_relat_1(A_864) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6524,plain,(
    ! [B_865] :
      ( k7_relat_1(k1_xboole_0,B_865) = k1_xboole_0
      | ~ r1_xboole_0(B_865,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6509])).

tff(c_6529,plain,(
    ! [B_865] :
      ( k7_relat_1(k1_xboole_0,B_865) = k1_xboole_0
      | ~ r1_xboole_0(B_865,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6463,c_6524])).

tff(c_21626,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21599,c_6529])).

tff(c_21853,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_21626])).

tff(c_20150,plain,(
    ! [B_1665,A_1666] :
      ( r1_xboole_0(k1_relat_1(B_1665),A_1666)
      | k9_relat_1(B_1665,A_1666) != k1_xboole_0
      | ~ v1_relat_1(B_1665) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20170,plain,(
    ! [A_1666] :
      ( r1_xboole_0(k1_xboole_0,A_1666)
      | k9_relat_1(k1_xboole_0,A_1666) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_20150])).

tff(c_20177,plain,(
    ! [A_1666] :
      ( r1_xboole_0(k1_xboole_0,A_1666)
      | k9_relat_1(k1_xboole_0,A_1666) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6463,c_20170])).

tff(c_21423,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21406,c_24])).

tff(c_21629,plain,(
    ! [B_1784] :
      ( k7_relat_1('#skF_6',B_1784) = k1_xboole_0
      | ~ r1_xboole_0(B_1784,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_21423])).

tff(c_21659,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20177,c_21629])).

tff(c_22100,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_21853,c_21659])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_5790,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_5782])).

tff(c_5799,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_5791])).

tff(c_20302,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5799,c_20296])).

tff(c_20311,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_20302])).

tff(c_20328,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20311])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_21032,plain,(
    ! [C_1742,A_1743,B_1744] :
      ( v1_partfun1(C_1742,A_1743)
      | ~ v1_funct_2(C_1742,A_1743,B_1744)
      | ~ v1_funct_1(C_1742)
      | ~ m1_subset_1(C_1742,k1_zfmisc_1(k2_zfmisc_1(A_1743,B_1744)))
      | v1_xboole_0(B_1744) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_21038,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_21032])).

tff(c_21045,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_21038])).

tff(c_21047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_20328,c_21045])).

tff(c_21048,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20311])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k9_relat_1(B_16,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_21056,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_5',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21048,c_18])).

tff(c_21586,plain,(
    ! [A_1782] :
      ( k9_relat_1('#skF_5',A_1782) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_1782) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_21056])).

tff(c_21590,plain,(
    ! [B_28] :
      ( k9_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_21586])).

tff(c_22152,plain,(
    ! [B_1837] :
      ( k9_relat_1('#skF_5',B_1837) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_1837)
      | v1_xboole_0(B_1837) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_21590])).

tff(c_22155,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_22152])).

tff(c_22158,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_22155])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21432,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_4',A_11)
      | ~ v4_relat_1('#skF_6',A_11)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21406,c_14])).

tff(c_21467,plain,(
    ! [A_1773] :
      ( r1_tarski('#skF_4',A_1773)
      | ~ v4_relat_1('#skF_6',A_1773) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_21432])).

tff(c_21471,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5798,c_21467])).

tff(c_21068,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21048,c_32])).

tff(c_21786,plain,(
    ! [A_1793] :
      ( r1_xboole_0('#skF_3',A_1793)
      | k7_relat_1('#skF_5',A_1793) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_21068])).

tff(c_21444,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_21423])).

tff(c_21816,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21786,c_21444])).

tff(c_21869,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_21816])).

tff(c_21059,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21048,c_30])).

tff(c_21667,plain,(
    ! [A_1785] :
      ( k7_relat_1('#skF_5',A_1785) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_1785) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_21059])).

tff(c_21671,plain,(
    ! [B_28] :
      ( k7_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_21667])).

tff(c_21898,plain,(
    ! [B_1811] :
      ( k7_relat_1('#skF_5',B_1811) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_1811)
      | v1_xboole_0(B_1811) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_21671])).

tff(c_21904,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_21898])).

tff(c_21909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_21869,c_21904])).

tff(c_21911,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_21816])).

tff(c_22,plain,(
    ! [A_17,C_21,B_20] :
      ( k9_relat_1(k7_relat_1(A_17,C_21),B_20) = k9_relat_1(A_17,B_20)
      | ~ r1_tarski(B_20,C_21)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_21929,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_5',B_20)
      | ~ r1_tarski(B_20,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21911,c_22])).

tff(c_22570,plain,(
    ! [B_1875] :
      ( k9_relat_1(k1_xboole_0,B_1875) = k9_relat_1('#skF_5',B_1875)
      | ~ r1_tarski(B_1875,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_21929])).

tff(c_22573,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = k9_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_21471,c_22570])).

tff(c_22579,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22158,c_22573])).

tff(c_22581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22100,c_22579])).

tff(c_22583,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_21626])).

tff(c_24001,plain,(
    ! [B_2022] :
      ( k9_relat_1('#skF_5',B_2022) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_2022)
      | v1_xboole_0(B_2022) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_21590])).

tff(c_24004,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_24001])).

tff(c_24007,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_24004])).

tff(c_21053,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k9_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21048,c_20])).

tff(c_21747,plain,(
    ! [A_1792] :
      ( r1_xboole_0('#skF_3',A_1792)
      | k9_relat_1('#skF_5',A_1792) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_21053])).

tff(c_21785,plain,(
    ! [A_1792] :
      ( k3_xboole_0('#skF_3',A_1792) = k1_xboole_0
      | k9_relat_1('#skF_5',A_1792) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_21747,c_2])).

tff(c_24022,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24007,c_21785])).

tff(c_20315,plain,(
    ! [A_1680,B_1681,C_1682] :
      ( k9_subset_1(A_1680,B_1681,C_1682) = k3_xboole_0(B_1681,C_1682)
      | ~ m1_subset_1(C_1682,k1_zfmisc_1(A_1680)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20327,plain,(
    ! [B_1681] : k9_subset_1('#skF_1',B_1681,'#skF_4') = k3_xboole_0(B_1681,'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_20315])).

tff(c_20085,plain,(
    ! [B_1660,A_1661] :
      ( k9_relat_1(B_1660,A_1661) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_1660),A_1661)
      | ~ v1_relat_1(B_1660) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20255,plain,(
    ! [B_1674,A_1675] :
      ( k9_relat_1(B_1674,A_1675) = k1_xboole_0
      | k7_relat_1(B_1674,A_1675) != k1_xboole_0
      | ~ v1_relat_1(B_1674) ) ),
    inference(resolution,[status(thm)],[c_32,c_20085])).

tff(c_20265,plain,(
    ! [A_1675] :
      ( k9_relat_1('#skF_5',A_1675) = k1_xboole_0
      | k7_relat_1('#skF_5',A_1675) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5790,c_20255])).

tff(c_21777,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21747,c_21444])).

tff(c_22639,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_21777])).

tff(c_22658,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20265,c_22639])).

tff(c_22864,plain,(
    ! [B_1909] :
      ( k7_relat_1('#skF_5',B_1909) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_1909)
      | v1_xboole_0(B_1909) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_21671])).

tff(c_22873,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_22864])).

tff(c_22879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_22658,c_22873])).

tff(c_22880,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_21777])).

tff(c_23005,plain,(
    ! [A_1925] :
      ( k3_xboole_0('#skF_4',A_1925) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1925) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_21599,c_2])).

tff(c_23012,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22880,c_23005])).

tff(c_21414,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21406,c_18])).

tff(c_21531,plain,(
    ! [A_1779] :
      ( k9_relat_1('#skF_6',A_1779) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_1779) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_21414])).

tff(c_21543,plain,(
    ! [B_2] :
      ( k9_relat_1('#skF_6',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_21531])).

tff(c_21074,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_3',A_11)
      | ~ v4_relat_1('#skF_5',A_11)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21048,c_14])).

tff(c_21462,plain,(
    ! [A_1772] :
      ( r1_tarski('#skF_3',A_1772)
      | ~ v4_relat_1('#skF_5',A_1772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_21074])).

tff(c_21466,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_5799,c_21462])).

tff(c_22885,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_6',B_20)
      | ~ r1_tarski(B_20,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22880,c_22])).

tff(c_23531,plain,(
    ! [B_1971] :
      ( k9_relat_1(k1_xboole_0,B_1971) = k9_relat_1('#skF_6',B_1971)
      | ~ r1_tarski(B_1971,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_22885])).

tff(c_23539,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') = k9_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_21466,c_23531])).

tff(c_21822,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21786,c_6529])).

tff(c_22638,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_21822])).

tff(c_21065,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_5',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21048,c_24])).

tff(c_21544,plain,(
    ! [B_1780] :
      ( k7_relat_1('#skF_5',B_1780) = k1_xboole_0
      | ~ r1_xboole_0(B_1780,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_21065])).

tff(c_21569,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20177,c_21544])).

tff(c_23388,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22638,c_21569])).

tff(c_23541,plain,(
    k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23539,c_23388])).

tff(c_23573,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21543,c_23541])).

tff(c_23580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23012,c_23573])).

tff(c_23582,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_21822])).

tff(c_23938,plain,(
    ! [A_2008,B_2005,D_2007,F_2009,C_2010,E_2006] :
      ( v1_funct_1(k1_tmap_1(A_2008,B_2005,C_2010,D_2007,E_2006,F_2009))
      | ~ m1_subset_1(F_2009,k1_zfmisc_1(k2_zfmisc_1(D_2007,B_2005)))
      | ~ v1_funct_2(F_2009,D_2007,B_2005)
      | ~ v1_funct_1(F_2009)
      | ~ m1_subset_1(E_2006,k1_zfmisc_1(k2_zfmisc_1(C_2010,B_2005)))
      | ~ v1_funct_2(E_2006,C_2010,B_2005)
      | ~ v1_funct_1(E_2006)
      | ~ m1_subset_1(D_2007,k1_zfmisc_1(A_2008))
      | v1_xboole_0(D_2007)
      | ~ m1_subset_1(C_2010,k1_zfmisc_1(A_2008))
      | v1_xboole_0(C_2010)
      | v1_xboole_0(B_2005)
      | v1_xboole_0(A_2008) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_23940,plain,(
    ! [A_2008,C_2010,E_2006] :
      ( v1_funct_1(k1_tmap_1(A_2008,'#skF_2',C_2010,'#skF_4',E_2006,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2006,k1_zfmisc_1(k2_zfmisc_1(C_2010,'#skF_2')))
      | ~ v1_funct_2(E_2006,C_2010,'#skF_2')
      | ~ v1_funct_1(E_2006)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2008))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2010,k1_zfmisc_1(A_2008))
      | v1_xboole_0(C_2010)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2008) ) ),
    inference(resolution,[status(thm)],[c_68,c_23938])).

tff(c_23945,plain,(
    ! [A_2008,C_2010,E_2006] :
      ( v1_funct_1(k1_tmap_1(A_2008,'#skF_2',C_2010,'#skF_4',E_2006,'#skF_6'))
      | ~ m1_subset_1(E_2006,k1_zfmisc_1(k2_zfmisc_1(C_2010,'#skF_2')))
      | ~ v1_funct_2(E_2006,C_2010,'#skF_2')
      | ~ v1_funct_1(E_2006)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2008))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2010,k1_zfmisc_1(A_2008))
      | v1_xboole_0(C_2010)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2008) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_23940])).

tff(c_25339,plain,(
    ! [A_2096,C_2097,E_2098] :
      ( v1_funct_1(k1_tmap_1(A_2096,'#skF_2',C_2097,'#skF_4',E_2098,'#skF_6'))
      | ~ m1_subset_1(E_2098,k1_zfmisc_1(k2_zfmisc_1(C_2097,'#skF_2')))
      | ~ v1_funct_2(E_2098,C_2097,'#skF_2')
      | ~ v1_funct_1(E_2098)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2096))
      | ~ m1_subset_1(C_2097,k1_zfmisc_1(A_2096))
      | v1_xboole_0(C_2097)
      | v1_xboole_0(A_2096) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_23945])).

tff(c_25346,plain,(
    ! [A_2096] :
      ( v1_funct_1(k1_tmap_1(A_2096,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2096))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2096))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2096) ) ),
    inference(resolution,[status(thm)],[c_74,c_25339])).

tff(c_25356,plain,(
    ! [A_2096] :
      ( v1_funct_1(k1_tmap_1(A_2096,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2096))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2096))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2096) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_25346])).

tff(c_25798,plain,(
    ! [A_2112] :
      ( v1_funct_1(k1_tmap_1(A_2112,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2112))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2112))
      | v1_xboole_0(A_2112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_25356])).

tff(c_25801,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_25798])).

tff(c_25804,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_25801])).

tff(c_25805,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_25804])).

tff(c_21697,plain,(
    ! [A_1787,B_1788,C_1789,D_1790] :
      ( k2_partfun1(A_1787,B_1788,C_1789,D_1790) = k7_relat_1(C_1789,D_1790)
      | ~ m1_subset_1(C_1789,k1_zfmisc_1(k2_zfmisc_1(A_1787,B_1788)))
      | ~ v1_funct_1(C_1789) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_21701,plain,(
    ! [D_1790] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1790) = k7_relat_1('#skF_5',D_1790)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_21697])).

tff(c_21707,plain,(
    ! [D_1790] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1790) = k7_relat_1('#skF_5',D_1790) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_21701])).

tff(c_21699,plain,(
    ! [D_1790] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1790) = k7_relat_1('#skF_6',D_1790)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68,c_21697])).

tff(c_21704,plain,(
    ! [D_1790] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1790) = k7_relat_1('#skF_6',D_1790) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_21699])).

tff(c_62,plain,(
    ! [F_177,D_175,A_172,C_174,E_176,B_173] :
      ( v1_funct_2(k1_tmap_1(A_172,B_173,C_174,D_175,E_176,F_177),k4_subset_1(A_172,C_174,D_175),B_173)
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(D_175,B_173)))
      | ~ v1_funct_2(F_177,D_175,B_173)
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(C_174,B_173)))
      | ~ v1_funct_2(E_176,C_174,B_173)
      | ~ v1_funct_1(E_176)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(A_172))
      | v1_xboole_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(A_172))
      | v1_xboole_0(C_174)
      | v1_xboole_0(B_173)
      | v1_xboole_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_60,plain,(
    ! [F_177,D_175,A_172,C_174,E_176,B_173] :
      ( m1_subset_1(k1_tmap_1(A_172,B_173,C_174,D_175,E_176,F_177),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172,C_174,D_175),B_173)))
      | ~ m1_subset_1(F_177,k1_zfmisc_1(k2_zfmisc_1(D_175,B_173)))
      | ~ v1_funct_2(F_177,D_175,B_173)
      | ~ v1_funct_1(F_177)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(C_174,B_173)))
      | ~ v1_funct_2(E_176,C_174,B_173)
      | ~ v1_funct_1(E_176)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(A_172))
      | v1_xboole_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(A_172))
      | v1_xboole_0(C_174)
      | v1_xboole_0(B_173)
      | v1_xboole_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_24201,plain,(
    ! [D_2035,B_2039,A_2036,E_2037,F_2040,C_2038] :
      ( k2_partfun1(k4_subset_1(A_2036,C_2038,D_2035),B_2039,k1_tmap_1(A_2036,B_2039,C_2038,D_2035,E_2037,F_2040),C_2038) = E_2037
      | ~ m1_subset_1(k1_tmap_1(A_2036,B_2039,C_2038,D_2035,E_2037,F_2040),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2036,C_2038,D_2035),B_2039)))
      | ~ v1_funct_2(k1_tmap_1(A_2036,B_2039,C_2038,D_2035,E_2037,F_2040),k4_subset_1(A_2036,C_2038,D_2035),B_2039)
      | ~ v1_funct_1(k1_tmap_1(A_2036,B_2039,C_2038,D_2035,E_2037,F_2040))
      | k2_partfun1(D_2035,B_2039,F_2040,k9_subset_1(A_2036,C_2038,D_2035)) != k2_partfun1(C_2038,B_2039,E_2037,k9_subset_1(A_2036,C_2038,D_2035))
      | ~ m1_subset_1(F_2040,k1_zfmisc_1(k2_zfmisc_1(D_2035,B_2039)))
      | ~ v1_funct_2(F_2040,D_2035,B_2039)
      | ~ v1_funct_1(F_2040)
      | ~ m1_subset_1(E_2037,k1_zfmisc_1(k2_zfmisc_1(C_2038,B_2039)))
      | ~ v1_funct_2(E_2037,C_2038,B_2039)
      | ~ v1_funct_1(E_2037)
      | ~ m1_subset_1(D_2035,k1_zfmisc_1(A_2036))
      | v1_xboole_0(D_2035)
      | ~ m1_subset_1(C_2038,k1_zfmisc_1(A_2036))
      | v1_xboole_0(C_2038)
      | v1_xboole_0(B_2039)
      | v1_xboole_0(A_2036) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_35069,plain,(
    ! [D_2578,C_2581,F_2580,B_2576,A_2579,E_2577] :
      ( k2_partfun1(k4_subset_1(A_2579,C_2581,D_2578),B_2576,k1_tmap_1(A_2579,B_2576,C_2581,D_2578,E_2577,F_2580),C_2581) = E_2577
      | ~ v1_funct_2(k1_tmap_1(A_2579,B_2576,C_2581,D_2578,E_2577,F_2580),k4_subset_1(A_2579,C_2581,D_2578),B_2576)
      | ~ v1_funct_1(k1_tmap_1(A_2579,B_2576,C_2581,D_2578,E_2577,F_2580))
      | k2_partfun1(D_2578,B_2576,F_2580,k9_subset_1(A_2579,C_2581,D_2578)) != k2_partfun1(C_2581,B_2576,E_2577,k9_subset_1(A_2579,C_2581,D_2578))
      | ~ m1_subset_1(F_2580,k1_zfmisc_1(k2_zfmisc_1(D_2578,B_2576)))
      | ~ v1_funct_2(F_2580,D_2578,B_2576)
      | ~ v1_funct_1(F_2580)
      | ~ m1_subset_1(E_2577,k1_zfmisc_1(k2_zfmisc_1(C_2581,B_2576)))
      | ~ v1_funct_2(E_2577,C_2581,B_2576)
      | ~ v1_funct_1(E_2577)
      | ~ m1_subset_1(D_2578,k1_zfmisc_1(A_2579))
      | v1_xboole_0(D_2578)
      | ~ m1_subset_1(C_2581,k1_zfmisc_1(A_2579))
      | v1_xboole_0(C_2581)
      | v1_xboole_0(B_2576)
      | v1_xboole_0(A_2579) ) ),
    inference(resolution,[status(thm)],[c_60,c_24201])).

tff(c_37611,plain,(
    ! [D_2691,F_2693,B_2689,A_2692,E_2690,C_2694] :
      ( k2_partfun1(k4_subset_1(A_2692,C_2694,D_2691),B_2689,k1_tmap_1(A_2692,B_2689,C_2694,D_2691,E_2690,F_2693),C_2694) = E_2690
      | ~ v1_funct_1(k1_tmap_1(A_2692,B_2689,C_2694,D_2691,E_2690,F_2693))
      | k2_partfun1(D_2691,B_2689,F_2693,k9_subset_1(A_2692,C_2694,D_2691)) != k2_partfun1(C_2694,B_2689,E_2690,k9_subset_1(A_2692,C_2694,D_2691))
      | ~ m1_subset_1(F_2693,k1_zfmisc_1(k2_zfmisc_1(D_2691,B_2689)))
      | ~ v1_funct_2(F_2693,D_2691,B_2689)
      | ~ v1_funct_1(F_2693)
      | ~ m1_subset_1(E_2690,k1_zfmisc_1(k2_zfmisc_1(C_2694,B_2689)))
      | ~ v1_funct_2(E_2690,C_2694,B_2689)
      | ~ v1_funct_1(E_2690)
      | ~ m1_subset_1(D_2691,k1_zfmisc_1(A_2692))
      | v1_xboole_0(D_2691)
      | ~ m1_subset_1(C_2694,k1_zfmisc_1(A_2692))
      | v1_xboole_0(C_2694)
      | v1_xboole_0(B_2689)
      | v1_xboole_0(A_2692) ) ),
    inference(resolution,[status(thm)],[c_62,c_35069])).

tff(c_37615,plain,(
    ! [A_2692,C_2694,E_2690] :
      ( k2_partfun1(k4_subset_1(A_2692,C_2694,'#skF_4'),'#skF_2',k1_tmap_1(A_2692,'#skF_2',C_2694,'#skF_4',E_2690,'#skF_6'),C_2694) = E_2690
      | ~ v1_funct_1(k1_tmap_1(A_2692,'#skF_2',C_2694,'#skF_4',E_2690,'#skF_6'))
      | k2_partfun1(C_2694,'#skF_2',E_2690,k9_subset_1(A_2692,C_2694,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_2692,C_2694,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2690,k1_zfmisc_1(k2_zfmisc_1(C_2694,'#skF_2')))
      | ~ v1_funct_2(E_2690,C_2694,'#skF_2')
      | ~ v1_funct_1(E_2690)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2692))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2694,k1_zfmisc_1(A_2692))
      | v1_xboole_0(C_2694)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2692) ) ),
    inference(resolution,[status(thm)],[c_68,c_37611])).

tff(c_37621,plain,(
    ! [A_2692,C_2694,E_2690] :
      ( k2_partfun1(k4_subset_1(A_2692,C_2694,'#skF_4'),'#skF_2',k1_tmap_1(A_2692,'#skF_2',C_2694,'#skF_4',E_2690,'#skF_6'),C_2694) = E_2690
      | ~ v1_funct_1(k1_tmap_1(A_2692,'#skF_2',C_2694,'#skF_4',E_2690,'#skF_6'))
      | k2_partfun1(C_2694,'#skF_2',E_2690,k9_subset_1(A_2692,C_2694,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2692,C_2694,'#skF_4'))
      | ~ m1_subset_1(E_2690,k1_zfmisc_1(k2_zfmisc_1(C_2694,'#skF_2')))
      | ~ v1_funct_2(E_2690,C_2694,'#skF_2')
      | ~ v1_funct_1(E_2690)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2692))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2694,k1_zfmisc_1(A_2692))
      | v1_xboole_0(C_2694)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2692) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_21704,c_37615])).

tff(c_40479,plain,(
    ! [A_2774,C_2775,E_2776] :
      ( k2_partfun1(k4_subset_1(A_2774,C_2775,'#skF_4'),'#skF_2',k1_tmap_1(A_2774,'#skF_2',C_2775,'#skF_4',E_2776,'#skF_6'),C_2775) = E_2776
      | ~ v1_funct_1(k1_tmap_1(A_2774,'#skF_2',C_2775,'#skF_4',E_2776,'#skF_6'))
      | k2_partfun1(C_2775,'#skF_2',E_2776,k9_subset_1(A_2774,C_2775,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2774,C_2775,'#skF_4'))
      | ~ m1_subset_1(E_2776,k1_zfmisc_1(k2_zfmisc_1(C_2775,'#skF_2')))
      | ~ v1_funct_2(E_2776,C_2775,'#skF_2')
      | ~ v1_funct_1(E_2776)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2774))
      | ~ m1_subset_1(C_2775,k1_zfmisc_1(A_2774))
      | v1_xboole_0(C_2775)
      | v1_xboole_0(A_2774) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_37621])).

tff(c_40486,plain,(
    ! [A_2774] :
      ( k2_partfun1(k4_subset_1(A_2774,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2774,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2774,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2774,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2774,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2774))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2774))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2774) ) ),
    inference(resolution,[status(thm)],[c_74,c_40479])).

tff(c_40496,plain,(
    ! [A_2774] :
      ( k2_partfun1(k4_subset_1(A_2774,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2774,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2774,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2774,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2774,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2774))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2774))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2774) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_21707,c_40486])).

tff(c_41664,plain,(
    ! [A_2790] :
      ( k2_partfun1(k4_subset_1(A_2790,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2790,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2790,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2790,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2790,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2790))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2790))
      | v1_xboole_0(A_2790) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_40496])).

tff(c_6815,plain,(
    ! [B_888,A_889] :
      ( k1_relat_1(B_888) = A_889
      | ~ v1_partfun1(B_888,A_889)
      | ~ v4_relat_1(B_888,A_889)
      | ~ v1_relat_1(B_888) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6821,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5799,c_6815])).

tff(c_6830,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_6821])).

tff(c_6834,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6830])).

tff(c_7648,plain,(
    ! [C_967,A_968,B_969] :
      ( v1_partfun1(C_967,A_968)
      | ~ v1_funct_2(C_967,A_968,B_969)
      | ~ v1_funct_1(C_967)
      | ~ m1_subset_1(C_967,k1_zfmisc_1(k2_zfmisc_1(A_968,B_969)))
      | v1_xboole_0(B_969) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7654,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_7648])).

tff(c_7661,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_7654])).

tff(c_7663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_6834,c_7661])).

tff(c_7664,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6830])).

tff(c_7684,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7664,c_32])).

tff(c_7704,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_7684])).

tff(c_7669,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_5',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7664,c_18])).

tff(c_8463,plain,(
    ! [A_1024] :
      ( k9_relat_1('#skF_5',A_1024) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_1024) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_7669])).

tff(c_8479,plain,(
    ! [A_25] :
      ( k9_relat_1('#skF_5',A_25) = k1_xboole_0
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7704,c_8463])).

tff(c_7672,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k9_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7664,c_20])).

tff(c_8419,plain,(
    ! [A_1022] :
      ( r1_xboole_0('#skF_3',A_1022)
      | k9_relat_1('#skF_5',A_1022) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_7672])).

tff(c_8451,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8419,c_6529])).

tff(c_9839,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8451])).

tff(c_9848,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8479,c_9839])).

tff(c_6660,plain,(
    ! [B_876,A_877] :
      ( r1_xboole_0(k1_relat_1(B_876),A_877)
      | k9_relat_1(B_876,A_877) != k1_xboole_0
      | ~ v1_relat_1(B_876) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6677,plain,(
    ! [A_877] :
      ( r1_xboole_0(k1_xboole_0,A_877)
      | k9_relat_1(k1_xboole_0,A_877) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6660])).

tff(c_6683,plain,(
    ! [A_877] :
      ( r1_xboole_0(k1_xboole_0,A_877)
      | k9_relat_1(k1_xboole_0,A_877) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6463,c_6677])).

tff(c_7681,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_5',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7664,c_24])).

tff(c_8171,plain,(
    ! [B_1010] :
      ( k7_relat_1('#skF_5',B_1010) = k1_xboole_0
      | ~ r1_xboole_0(B_1010,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_7681])).

tff(c_8196,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6683,c_8171])).

tff(c_10070,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_9848,c_8196])).

tff(c_6824,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5798,c_6815])).

tff(c_6833,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_6824])).

tff(c_7711,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6833])).

tff(c_8034,plain,(
    ! [C_998,A_999,B_1000] :
      ( v1_partfun1(C_998,A_999)
      | ~ v1_funct_2(C_998,A_999,B_1000)
      | ~ v1_funct_1(C_998)
      | ~ m1_subset_1(C_998,k1_zfmisc_1(k2_zfmisc_1(A_999,B_1000)))
      | v1_xboole_0(B_1000) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8037,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_8034])).

tff(c_8043,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8037])).

tff(c_8045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_7711,c_8043])).

tff(c_8046,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6833])).

tff(c_8051,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8046,c_18])).

tff(c_8398,plain,(
    ! [A_1021] :
      ( k9_relat_1('#skF_6',A_1021) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_1021) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_8051])).

tff(c_8783,plain,(
    ! [B_1066] :
      ( k9_relat_1('#skF_6',B_1066) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_1066) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_8398])).

tff(c_8054,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8046,c_20])).

tff(c_8252,plain,(
    ! [A_1014] :
      ( r1_xboole_0('#skF_4',A_1014)
      | k9_relat_1('#skF_6',A_1014) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_8054])).

tff(c_7702,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_5',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_7681])).

tff(c_8271,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8252,c_7702])).

tff(c_8485,plain,(
    k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8271])).

tff(c_8806,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8783,c_8485])).

tff(c_8363,plain,(
    ! [A_1020] :
      ( r1_xboole_0('#skF_3',A_1020)
      | k7_relat_1('#skF_5',A_1020) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_7684])).

tff(c_8063,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8046,c_24])).

tff(c_8084,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_8063])).

tff(c_8389,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8363,c_8084])).

tff(c_8588,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8389])).

tff(c_8473,plain,(
    ! [B_28] :
      ( k9_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_8463])).

tff(c_8680,plain,(
    ! [B_1057] :
      ( k9_relat_1('#skF_5',B_1057) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_1057)
      | v1_xboole_0(B_1057) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8473])).

tff(c_8686,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_8680])).

tff(c_8690,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_8686])).

tff(c_7675,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7664,c_30])).

tff(c_7698,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_7675])).

tff(c_8718,plain,(
    ! [A_1059] :
      ( k7_relat_1('#skF_5',A_1059) = k1_xboole_0
      | k9_relat_1('#skF_5',A_1059) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8419,c_7698])).

tff(c_8721,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8690,c_8718])).

tff(c_8731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8588,c_8721])).

tff(c_8732,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8389])).

tff(c_8066,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8046,c_32])).

tff(c_8226,plain,(
    ! [A_1013] :
      ( r1_xboole_0('#skF_4',A_1013)
      | k7_relat_1('#skF_6',A_1013) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_8066])).

tff(c_8876,plain,(
    ! [A_1082] :
      ( k3_xboole_0('#skF_4',A_1082) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1082) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8226,c_2])).

tff(c_8879,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8732,c_8876])).

tff(c_8886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8806,c_8879])).

tff(c_8888,plain,(
    k9_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8271])).

tff(c_7690,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_3',A_11)
      | ~ v4_relat_1('#skF_5',A_11)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7664,c_14])).

tff(c_8093,plain,(
    ! [A_1001] :
      ( r1_tarski('#skF_3',A_1001)
      | ~ v4_relat_1('#skF_5',A_1001) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_7690])).

tff(c_8097,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_5799,c_8093])).

tff(c_8299,plain,(
    ! [B_1016] :
      ( k7_relat_1('#skF_6',B_1016) = k1_xboole_0
      | ~ r1_xboole_0(B_1016,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_8063])).

tff(c_8319,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_6',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_36,c_8299])).

tff(c_8907,plain,(
    ! [A_1083] :
      ( k7_relat_1('#skF_6',A_1083) = k1_xboole_0
      | ~ r1_subset_1(A_1083,'#skF_4')
      | v1_xboole_0(A_1083) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_8319])).

tff(c_8910,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_8907])).

tff(c_8913,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8910])).

tff(c_8917,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_6',B_20)
      | ~ r1_tarski(B_20,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8913,c_22])).

tff(c_10302,plain,(
    ! [B_1211] :
      ( k9_relat_1(k1_xboole_0,B_1211) = k9_relat_1('#skF_6',B_1211)
      | ~ r1_tarski(B_1211,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_8917])).

tff(c_10305,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') = k9_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_8097,c_10302])).

tff(c_10311,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8888,c_10305])).

tff(c_10313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10070,c_10311])).

tff(c_10315,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8451])).

tff(c_10409,plain,(
    ! [A_1220] :
      ( k7_relat_1('#skF_5',A_1220) = k1_xboole_0
      | k9_relat_1('#skF_5',A_1220) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8419,c_7698])).

tff(c_10419,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10315,c_10409])).

tff(c_8334,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6683,c_8299])).

tff(c_9024,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8334])).

tff(c_9216,plain,(
    ! [B_1119] :
      ( k9_relat_1('#skF_5',B_1119) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_1119)
      | v1_xboole_0(B_1119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_8473])).

tff(c_9219,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_9216])).

tff(c_9222,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_9219])).

tff(c_8072,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_4',A_11)
      | ~ v4_relat_1('#skF_6',A_11)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8046,c_14])).

tff(c_8098,plain,(
    ! [A_1002] :
      ( r1_tarski('#skF_4',A_1002)
      | ~ v4_relat_1('#skF_6',A_1002) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_8072])).

tff(c_8102,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5798,c_8098])).

tff(c_8887,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8271])).

tff(c_8892,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_5',B_20)
      | ~ r1_tarski(B_20,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8887,c_22])).

tff(c_9583,plain,(
    ! [B_1150] :
      ( k9_relat_1(k1_xboole_0,B_1150) = k9_relat_1('#skF_5',B_1150)
      | ~ r1_tarski(B_1150,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5790,c_8892])).

tff(c_9586,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = k9_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_8102,c_9583])).

tff(c_9592,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9222,c_9586])).

tff(c_9594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9024,c_9592])).

tff(c_9595,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8334])).

tff(c_10388,plain,(
    ! [A_1218] :
      ( k3_xboole_0('#skF_3',A_1218) = k1_xboole_0
      | k7_relat_1('#skF_5',A_1218) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8363,c_2])).

tff(c_10392,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8887,c_10388])).

tff(c_8139,plain,(
    ! [A_1005,B_1006,C_1007] :
      ( k9_subset_1(A_1005,B_1006,C_1007) = k3_xboole_0(B_1006,C_1007)
      | ~ m1_subset_1(C_1007,k1_zfmisc_1(A_1005)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8151,plain,(
    ! [B_1006] : k9_subset_1('#skF_1',B_1006,'#skF_4') = k3_xboole_0(B_1006,'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_8139])).

tff(c_9792,plain,(
    ! [F_1163,B_1159,D_1161,C_1164,A_1162,E_1160] :
      ( v1_funct_1(k1_tmap_1(A_1162,B_1159,C_1164,D_1161,E_1160,F_1163))
      | ~ m1_subset_1(F_1163,k1_zfmisc_1(k2_zfmisc_1(D_1161,B_1159)))
      | ~ v1_funct_2(F_1163,D_1161,B_1159)
      | ~ v1_funct_1(F_1163)
      | ~ m1_subset_1(E_1160,k1_zfmisc_1(k2_zfmisc_1(C_1164,B_1159)))
      | ~ v1_funct_2(E_1160,C_1164,B_1159)
      | ~ v1_funct_1(E_1160)
      | ~ m1_subset_1(D_1161,k1_zfmisc_1(A_1162))
      | v1_xboole_0(D_1161)
      | ~ m1_subset_1(C_1164,k1_zfmisc_1(A_1162))
      | v1_xboole_0(C_1164)
      | v1_xboole_0(B_1159)
      | v1_xboole_0(A_1162) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_9794,plain,(
    ! [A_1162,C_1164,E_1160] :
      ( v1_funct_1(k1_tmap_1(A_1162,'#skF_2',C_1164,'#skF_4',E_1160,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1160,k1_zfmisc_1(k2_zfmisc_1(C_1164,'#skF_2')))
      | ~ v1_funct_2(E_1160,C_1164,'#skF_2')
      | ~ v1_funct_1(E_1160)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1162))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1164,k1_zfmisc_1(A_1162))
      | v1_xboole_0(C_1164)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1162) ) ),
    inference(resolution,[status(thm)],[c_68,c_9792])).

tff(c_9799,plain,(
    ! [A_1162,C_1164,E_1160] :
      ( v1_funct_1(k1_tmap_1(A_1162,'#skF_2',C_1164,'#skF_4',E_1160,'#skF_6'))
      | ~ m1_subset_1(E_1160,k1_zfmisc_1(k2_zfmisc_1(C_1164,'#skF_2')))
      | ~ v1_funct_2(E_1160,C_1164,'#skF_2')
      | ~ v1_funct_1(E_1160)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1162))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1164,k1_zfmisc_1(A_1162))
      | v1_xboole_0(C_1164)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_9794])).

tff(c_10851,plain,(
    ! [A_1253,C_1254,E_1255] :
      ( v1_funct_1(k1_tmap_1(A_1253,'#skF_2',C_1254,'#skF_4',E_1255,'#skF_6'))
      | ~ m1_subset_1(E_1255,k1_zfmisc_1(k2_zfmisc_1(C_1254,'#skF_2')))
      | ~ v1_funct_2(E_1255,C_1254,'#skF_2')
      | ~ v1_funct_1(E_1255)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1253))
      | ~ m1_subset_1(C_1254,k1_zfmisc_1(A_1253))
      | v1_xboole_0(C_1254)
      | v1_xboole_0(A_1253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_9799])).

tff(c_10858,plain,(
    ! [A_1253] :
      ( v1_funct_1(k1_tmap_1(A_1253,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1253))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1253))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1253) ) ),
    inference(resolution,[status(thm)],[c_74,c_10851])).

tff(c_10868,plain,(
    ! [A_1253] :
      ( v1_funct_1(k1_tmap_1(A_1253,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1253))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1253))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_10858])).

tff(c_11282,plain,(
    ! [A_1283] :
      ( v1_funct_1(k1_tmap_1(A_1283,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1283))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1283))
      | v1_xboole_0(A_1283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_10868])).

tff(c_11285,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_11282])).

tff(c_11288,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_11285])).

tff(c_11289,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_11288])).

tff(c_8977,plain,(
    ! [A_1087,B_1088,C_1089,D_1090] :
      ( k2_partfun1(A_1087,B_1088,C_1089,D_1090) = k7_relat_1(C_1089,D_1090)
      | ~ m1_subset_1(C_1089,k1_zfmisc_1(k2_zfmisc_1(A_1087,B_1088)))
      | ~ v1_funct_1(C_1089) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8981,plain,(
    ! [D_1090] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1090) = k7_relat_1('#skF_5',D_1090)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_8977])).

tff(c_8987,plain,(
    ! [D_1090] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1090) = k7_relat_1('#skF_5',D_1090) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8981])).

tff(c_8979,plain,(
    ! [D_1090] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1090) = k7_relat_1('#skF_6',D_1090)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68,c_8977])).

tff(c_8984,plain,(
    ! [D_1090] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1090) = k7_relat_1('#skF_6',D_1090) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_8979])).

tff(c_10807,plain,(
    ! [C_1247,F_1249,A_1245,B_1248,E_1246,D_1244] :
      ( k2_partfun1(k4_subset_1(A_1245,C_1247,D_1244),B_1248,k1_tmap_1(A_1245,B_1248,C_1247,D_1244,E_1246,F_1249),D_1244) = F_1249
      | ~ m1_subset_1(k1_tmap_1(A_1245,B_1248,C_1247,D_1244,E_1246,F_1249),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1245,C_1247,D_1244),B_1248)))
      | ~ v1_funct_2(k1_tmap_1(A_1245,B_1248,C_1247,D_1244,E_1246,F_1249),k4_subset_1(A_1245,C_1247,D_1244),B_1248)
      | ~ v1_funct_1(k1_tmap_1(A_1245,B_1248,C_1247,D_1244,E_1246,F_1249))
      | k2_partfun1(D_1244,B_1248,F_1249,k9_subset_1(A_1245,C_1247,D_1244)) != k2_partfun1(C_1247,B_1248,E_1246,k9_subset_1(A_1245,C_1247,D_1244))
      | ~ m1_subset_1(F_1249,k1_zfmisc_1(k2_zfmisc_1(D_1244,B_1248)))
      | ~ v1_funct_2(F_1249,D_1244,B_1248)
      | ~ v1_funct_1(F_1249)
      | ~ m1_subset_1(E_1246,k1_zfmisc_1(k2_zfmisc_1(C_1247,B_1248)))
      | ~ v1_funct_2(E_1246,C_1247,B_1248)
      | ~ v1_funct_1(E_1246)
      | ~ m1_subset_1(D_1244,k1_zfmisc_1(A_1245))
      | v1_xboole_0(D_1244)
      | ~ m1_subset_1(C_1247,k1_zfmisc_1(A_1245))
      | v1_xboole_0(C_1247)
      | v1_xboole_0(B_1248)
      | v1_xboole_0(A_1245) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_14597,plain,(
    ! [D_1469,C_1472,E_1468,A_1470,B_1467,F_1471] :
      ( k2_partfun1(k4_subset_1(A_1470,C_1472,D_1469),B_1467,k1_tmap_1(A_1470,B_1467,C_1472,D_1469,E_1468,F_1471),D_1469) = F_1471
      | ~ v1_funct_2(k1_tmap_1(A_1470,B_1467,C_1472,D_1469,E_1468,F_1471),k4_subset_1(A_1470,C_1472,D_1469),B_1467)
      | ~ v1_funct_1(k1_tmap_1(A_1470,B_1467,C_1472,D_1469,E_1468,F_1471))
      | k2_partfun1(D_1469,B_1467,F_1471,k9_subset_1(A_1470,C_1472,D_1469)) != k2_partfun1(C_1472,B_1467,E_1468,k9_subset_1(A_1470,C_1472,D_1469))
      | ~ m1_subset_1(F_1471,k1_zfmisc_1(k2_zfmisc_1(D_1469,B_1467)))
      | ~ v1_funct_2(F_1471,D_1469,B_1467)
      | ~ v1_funct_1(F_1471)
      | ~ m1_subset_1(E_1468,k1_zfmisc_1(k2_zfmisc_1(C_1472,B_1467)))
      | ~ v1_funct_2(E_1468,C_1472,B_1467)
      | ~ v1_funct_1(E_1468)
      | ~ m1_subset_1(D_1469,k1_zfmisc_1(A_1470))
      | v1_xboole_0(D_1469)
      | ~ m1_subset_1(C_1472,k1_zfmisc_1(A_1470))
      | v1_xboole_0(C_1472)
      | v1_xboole_0(B_1467)
      | v1_xboole_0(A_1470) ) ),
    inference(resolution,[status(thm)],[c_60,c_10807])).

tff(c_18301,plain,(
    ! [D_1597,F_1599,C_1600,B_1595,A_1598,E_1596] :
      ( k2_partfun1(k4_subset_1(A_1598,C_1600,D_1597),B_1595,k1_tmap_1(A_1598,B_1595,C_1600,D_1597,E_1596,F_1599),D_1597) = F_1599
      | ~ v1_funct_1(k1_tmap_1(A_1598,B_1595,C_1600,D_1597,E_1596,F_1599))
      | k2_partfun1(D_1597,B_1595,F_1599,k9_subset_1(A_1598,C_1600,D_1597)) != k2_partfun1(C_1600,B_1595,E_1596,k9_subset_1(A_1598,C_1600,D_1597))
      | ~ m1_subset_1(F_1599,k1_zfmisc_1(k2_zfmisc_1(D_1597,B_1595)))
      | ~ v1_funct_2(F_1599,D_1597,B_1595)
      | ~ v1_funct_1(F_1599)
      | ~ m1_subset_1(E_1596,k1_zfmisc_1(k2_zfmisc_1(C_1600,B_1595)))
      | ~ v1_funct_2(E_1596,C_1600,B_1595)
      | ~ v1_funct_1(E_1596)
      | ~ m1_subset_1(D_1597,k1_zfmisc_1(A_1598))
      | v1_xboole_0(D_1597)
      | ~ m1_subset_1(C_1600,k1_zfmisc_1(A_1598))
      | v1_xboole_0(C_1600)
      | v1_xboole_0(B_1595)
      | v1_xboole_0(A_1598) ) ),
    inference(resolution,[status(thm)],[c_62,c_14597])).

tff(c_18305,plain,(
    ! [A_1598,C_1600,E_1596] :
      ( k2_partfun1(k4_subset_1(A_1598,C_1600,'#skF_4'),'#skF_2',k1_tmap_1(A_1598,'#skF_2',C_1600,'#skF_4',E_1596,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1598,'#skF_2',C_1600,'#skF_4',E_1596,'#skF_6'))
      | k2_partfun1(C_1600,'#skF_2',E_1596,k9_subset_1(A_1598,C_1600,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1598,C_1600,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1596,k1_zfmisc_1(k2_zfmisc_1(C_1600,'#skF_2')))
      | ~ v1_funct_2(E_1596,C_1600,'#skF_2')
      | ~ v1_funct_1(E_1596)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1598))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1600,k1_zfmisc_1(A_1598))
      | v1_xboole_0(C_1600)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1598) ) ),
    inference(resolution,[status(thm)],[c_68,c_18301])).

tff(c_18311,plain,(
    ! [A_1598,C_1600,E_1596] :
      ( k2_partfun1(k4_subset_1(A_1598,C_1600,'#skF_4'),'#skF_2',k1_tmap_1(A_1598,'#skF_2',C_1600,'#skF_4',E_1596,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1598,'#skF_2',C_1600,'#skF_4',E_1596,'#skF_6'))
      | k2_partfun1(C_1600,'#skF_2',E_1596,k9_subset_1(A_1598,C_1600,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1598,C_1600,'#skF_4'))
      | ~ m1_subset_1(E_1596,k1_zfmisc_1(k2_zfmisc_1(C_1600,'#skF_2')))
      | ~ v1_funct_2(E_1596,C_1600,'#skF_2')
      | ~ v1_funct_1(E_1596)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1598))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1600,k1_zfmisc_1(A_1598))
      | v1_xboole_0(C_1600)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8984,c_18305])).

tff(c_19160,plain,(
    ! [A_1634,C_1635,E_1636] :
      ( k2_partfun1(k4_subset_1(A_1634,C_1635,'#skF_4'),'#skF_2',k1_tmap_1(A_1634,'#skF_2',C_1635,'#skF_4',E_1636,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1634,'#skF_2',C_1635,'#skF_4',E_1636,'#skF_6'))
      | k2_partfun1(C_1635,'#skF_2',E_1636,k9_subset_1(A_1634,C_1635,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1634,C_1635,'#skF_4'))
      | ~ m1_subset_1(E_1636,k1_zfmisc_1(k2_zfmisc_1(C_1635,'#skF_2')))
      | ~ v1_funct_2(E_1636,C_1635,'#skF_2')
      | ~ v1_funct_1(E_1636)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1634))
      | ~ m1_subset_1(C_1635,k1_zfmisc_1(A_1634))
      | v1_xboole_0(C_1635)
      | v1_xboole_0(A_1634) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_18311])).

tff(c_19167,plain,(
    ! [A_1634] :
      ( k2_partfun1(k4_subset_1(A_1634,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1634,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1634,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1634,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1634,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1634))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1634))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1634) ) ),
    inference(resolution,[status(thm)],[c_74,c_19160])).

tff(c_19177,plain,(
    ! [A_1634] :
      ( k2_partfun1(k4_subset_1(A_1634,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1634,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1634,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1634,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1634,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1634))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1634))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1634) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_8987,c_19167])).

tff(c_19976,plain,(
    ! [A_1654] :
      ( k2_partfun1(k4_subset_1(A_1654,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1654,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1654,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1654,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1654,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1654))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1654))
      | v1_xboole_0(A_1654) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_19177])).

tff(c_139,plain,(
    ! [C_245,A_246,B_247] :
      ( v1_relat_1(C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_146,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_139])).

tff(c_1664,plain,(
    ! [C_412,A_413,B_414] :
      ( v4_relat_1(C_412,A_413)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1671,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1664])).

tff(c_2076,plain,(
    ! [B_455,A_456] :
      ( k1_relat_1(B_455) = A_456
      | ~ v1_partfun1(B_455,A_456)
      | ~ v4_relat_1(B_455,A_456)
      | ~ v1_relat_1(B_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2082,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1671,c_2076])).

tff(c_2091,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2082])).

tff(c_2667,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2091])).

tff(c_2942,plain,(
    ! [C_540,A_541,B_542] :
      ( v1_partfun1(C_540,A_541)
      | ~ v1_funct_2(C_540,A_541,B_542)
      | ~ v1_funct_1(C_540)
      | ~ m1_subset_1(C_540,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542)))
      | v1_xboole_0(B_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2945,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2942])).

tff(c_2951,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2945])).

tff(c_2953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2667,c_2951])).

tff(c_2954,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2091])).

tff(c_2968,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_18])).

tff(c_3171,plain,(
    ! [A_555] :
      ( k9_relat_1('#skF_6',A_555) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_555) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2968])).

tff(c_3187,plain,(
    ! [B_2] :
      ( k9_relat_1('#skF_6',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_3171])).

tff(c_2974,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_20])).

tff(c_3267,plain,(
    ! [A_563] :
      ( r1_xboole_0('#skF_4',A_563)
      | k9_relat_1('#skF_6',A_563) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2974])).

tff(c_148,plain,(
    ! [B_248,A_249] :
      ( v4_relat_1(B_248,A_249)
      | ~ r1_tarski(k1_relat_1(B_248),A_249)
      | ~ v1_relat_1(B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_151,plain,(
    ! [A_249] :
      ( v4_relat_1(k1_xboole_0,A_249)
      | ~ r1_tarski(k1_xboole_0,A_249)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_148])).

tff(c_152,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_153,plain,(
    ! [C_250,A_251,B_252] :
      ( v4_relat_1(C_250,A_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_160,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_153])).

tff(c_370,plain,(
    ! [B_285,A_286] :
      ( k1_relat_1(B_285) = A_286
      | ~ v1_partfun1(B_285,A_286)
      | ~ v4_relat_1(B_285,A_286)
      | ~ v1_relat_1(B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_376,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_160,c_370])).

tff(c_382,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_376])).

tff(c_940,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_1171,plain,(
    ! [C_373,A_374,B_375] :
      ( v1_partfun1(C_373,A_374)
      | ~ v1_funct_2(C_373,A_374,B_375)
      | ~ v1_funct_1(C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375)))
      | v1_xboole_0(B_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1174,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1171])).

tff(c_1180,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1174])).

tff(c_1182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_940,c_1180])).

tff(c_1183,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_1200,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_6',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_25)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_30])).

tff(c_1287,plain,(
    ! [A_383] :
      ( k7_relat_1('#skF_6',A_383) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1200])).

tff(c_1574,plain,(
    ! [B_403] :
      ( k7_relat_1('#skF_6',B_403) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_403) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1287])).

tff(c_1583,plain,(
    ! [B_403] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1('#skF_6')
      | k3_xboole_0('#skF_4',B_403) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1574,c_16])).

tff(c_1591,plain,(
    ! [B_403] :
      ( v1_relat_1(k1_xboole_0)
      | k3_xboole_0('#skF_4',B_403) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1583])).

tff(c_1592,plain,(
    ! [B_403] : k3_xboole_0('#skF_4',B_403) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_1591])).

tff(c_1191,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_32])).

tff(c_1317,plain,(
    ! [A_386] :
      ( r1_xboole_0('#skF_4',A_386)
      | k7_relat_1('#skF_6',A_386) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1191])).

tff(c_1336,plain,(
    ! [A_386] :
      ( k3_xboole_0('#skF_4',A_386) = k1_xboole_0
      | k7_relat_1('#skF_6',A_386) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1317,c_2])).

tff(c_1610,plain,(
    ! [A_386] : k7_relat_1('#skF_6',A_386) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1592,c_1336])).

tff(c_1197,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_24])).

tff(c_1219,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1197])).

tff(c_1615,plain,(
    ! [B_409] : ~ r1_xboole_0(B_409,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1610,c_1219])).

tff(c_1635,plain,(
    ! [A_27] :
      ( ~ r1_subset_1(A_27,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_36,c_1615])).

tff(c_1653,plain,(
    ! [A_410] :
      ( ~ r1_subset_1(A_410,'#skF_4')
      | v1_xboole_0(A_410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1635])).

tff(c_1656,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1653])).

tff(c_1660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1656])).

tff(c_1662,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_1718,plain,(
    ! [A_427,B_428] :
      ( k7_relat_1(A_427,B_428) = k1_xboole_0
      | ~ r1_xboole_0(B_428,k1_relat_1(A_427))
      | ~ v1_relat_1(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1737,plain,(
    ! [B_428] :
      ( k7_relat_1(k1_xboole_0,B_428) = k1_xboole_0
      | ~ r1_xboole_0(B_428,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1718])).

tff(c_1743,plain,(
    ! [B_428] :
      ( k7_relat_1(k1_xboole_0,B_428) = k1_xboole_0
      | ~ r1_xboole_0(B_428,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1737])).

tff(c_3298,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3267,c_1743])).

tff(c_4212,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3298])).

tff(c_4225,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3187,c_4212])).

tff(c_2965,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_32])).

tff(c_3068,plain,(
    ! [A_550] :
      ( r1_xboole_0('#skF_4',A_550)
      | k7_relat_1('#skF_6',A_550) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2965])).

tff(c_3086,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3068,c_1743])).

tff(c_4419,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3086])).

tff(c_1692,plain,(
    ! [B_420,A_421] :
      ( r1_xboole_0(k1_relat_1(B_420),A_421)
      | k9_relat_1(B_420,A_421) != k1_xboole_0
      | ~ v1_relat_1(B_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1698,plain,(
    ! [A_421] :
      ( r1_xboole_0(k1_xboole_0,A_421)
      | k9_relat_1(k1_xboole_0,A_421) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1692])).

tff(c_1701,plain,(
    ! [A_421] :
      ( r1_xboole_0(k1_xboole_0,A_421)
      | k9_relat_1(k1_xboole_0,A_421) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1698])).

tff(c_2971,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_24])).

tff(c_3089,plain,(
    ! [B_551] :
      ( k7_relat_1('#skF_6',B_551) = k1_xboole_0
      | ~ r1_xboole_0(B_551,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2971])).

tff(c_3124,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1701,c_3089])).

tff(c_4471,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4419,c_3124])).

tff(c_147,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_139])).

tff(c_1672,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1664])).

tff(c_2079,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1672,c_2076])).

tff(c_2088,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2079])).

tff(c_2095,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2088])).

tff(c_2595,plain,(
    ! [C_512,A_513,B_514] :
      ( v1_partfun1(C_512,A_513)
      | ~ v1_funct_2(C_512,A_513,B_514)
      | ~ v1_funct_1(C_512)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(A_513,B_514)))
      | v1_xboole_0(B_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2601,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_2595])).

tff(c_2608,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2601])).

tff(c_2610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2095,c_2608])).

tff(c_2611,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2088])).

tff(c_2625,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_5',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2611,c_18])).

tff(c_3214,plain,(
    ! [A_557] :
      ( k9_relat_1('#skF_5',A_557) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_557) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2625])).

tff(c_3224,plain,(
    ! [B_28] :
      ( k9_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_3214])).

tff(c_4058,plain,(
    ! [B_634] :
      ( k9_relat_1('#skF_5',B_634) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_634)
      | v1_xboole_0(B_634) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3224])).

tff(c_4061,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_4058])).

tff(c_4064,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4061])).

tff(c_2977,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_4',A_11)
      | ~ v4_relat_1('#skF_6',A_11)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_14])).

tff(c_3029,plain,(
    ! [A_545] :
      ( r1_tarski('#skF_4',A_545)
      | ~ v4_relat_1('#skF_6',A_545) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2977])).

tff(c_3037,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1671,c_3029])).

tff(c_2616,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2611,c_30])).

tff(c_3246,plain,(
    ! [A_562] :
      ( k7_relat_1('#skF_5',A_562) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2616])).

tff(c_3256,plain,(
    ! [B_28] :
      ( k7_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_3246])).

tff(c_3354,plain,(
    ! [B_565] :
      ( k7_relat_1('#skF_5',B_565) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_565)
      | v1_xboole_0(B_565) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3256])).

tff(c_3357,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_3354])).

tff(c_3360,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3357])).

tff(c_3364,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_5',B_20)
      | ~ r1_tarski(B_20,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3360,c_22])).

tff(c_4630,plain,(
    ! [B_686] :
      ( k9_relat_1(k1_xboole_0,B_686) = k9_relat_1('#skF_5',B_686)
      | ~ r1_tarski(B_686,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_3364])).

tff(c_4633,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = k9_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3037,c_4630])).

tff(c_4639,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4064,c_4633])).

tff(c_4641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4471,c_4639])).

tff(c_4643,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3086])).

tff(c_3088,plain,(
    ! [A_550] :
      ( k3_xboole_0('#skF_4',A_550) = k1_xboole_0
      | k7_relat_1('#skF_6',A_550) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3068,c_2])).

tff(c_4680,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4643,c_3088])).

tff(c_4704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4225,c_4680])).

tff(c_4706,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3298])).

tff(c_2959,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_6',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_25)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_30])).

tff(c_2984,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_6',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2959])).

tff(c_4908,plain,(
    ! [A_703] :
      ( k7_relat_1('#skF_6',A_703) = k1_xboole_0
      | k9_relat_1('#skF_6',A_703) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3267,c_2984])).

tff(c_4915,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4706,c_4908])).

tff(c_2622,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2611,c_32])).

tff(c_3128,plain,(
    ! [A_553] :
      ( r1_xboole_0('#skF_3',A_553)
      | k7_relat_1('#skF_5',A_553) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2622])).

tff(c_2992,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2971])).

tff(c_3147,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3128,c_2992])).

tff(c_3816,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3360,c_3147])).

tff(c_2988,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_2965])).

tff(c_3183,plain,(
    ! [A_25] :
      ( k9_relat_1('#skF_6',A_25) = k1_xboole_0
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2988,c_3171])).

tff(c_2634,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_3',A_11)
      | ~ v4_relat_1('#skF_5',A_11)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2611,c_14])).

tff(c_3038,plain,(
    ! [A_546] :
      ( r1_tarski('#skF_3',A_546)
      | ~ v4_relat_1('#skF_5',A_546) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2634])).

tff(c_3046,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1672,c_3038])).

tff(c_3829,plain,(
    ! [B_20] :
      ( k9_relat_1(k1_xboole_0,B_20) = k9_relat_1('#skF_6',B_20)
      | ~ r1_tarski(B_20,'#skF_3')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3816,c_22])).

tff(c_3975,plain,(
    ! [B_628] :
      ( k9_relat_1(k1_xboole_0,B_628) = k9_relat_1('#skF_6',B_628)
      | ~ r1_tarski(B_628,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_3829])).

tff(c_3983,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') = k9_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_3046,c_3975])).

tff(c_2645,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2622])).

tff(c_3557,plain,(
    ! [A_587] :
      ( k9_relat_1('#skF_5',A_587) = k1_xboole_0
      | k7_relat_1('#skF_5',A_587) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2645,c_3214])).

tff(c_2631,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k9_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2611,c_20])).

tff(c_3188,plain,(
    ! [A_556] :
      ( r1_xboole_0('#skF_3',A_556)
      | k9_relat_1('#skF_5',A_556) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2631])).

tff(c_3211,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3188,c_1743])).

tff(c_3485,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3211])).

tff(c_3580,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3557,c_3485])).

tff(c_2628,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_5',B_24) = k1_xboole_0
      | ~ r1_xboole_0(B_24,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2611,c_24])).

tff(c_3301,plain,(
    ! [B_564] :
      ( k7_relat_1('#skF_5',B_564) = k1_xboole_0
      | ~ r1_xboole_0(B_564,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2628])).

tff(c_3351,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1701,c_3301])).

tff(c_3647,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3580,c_3351])).

tff(c_3986,plain,(
    k9_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3983,c_3647])).

tff(c_4013,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3183,c_3986])).

tff(c_4020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_4013])).

tff(c_4022,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3211])).

tff(c_2651,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k9_relat_1('#skF_5',A_15) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2631])).

tff(c_3261,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_5',A_15) = k1_xboole_0
      | k9_relat_1('#skF_5',A_15) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2651,c_3246])).

tff(c_4081,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4022,c_3261])).

tff(c_3235,plain,(
    ! [A_558,B_559,C_560,D_561] :
      ( k2_partfun1(A_558,B_559,C_560,D_561) = k7_relat_1(C_560,D_561)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(A_558,B_559)))
      | ~ v1_funct_1(C_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3239,plain,(
    ! [D_561] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_561) = k7_relat_1('#skF_5',D_561)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_3235])).

tff(c_3245,plain,(
    ! [D_561] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_561) = k7_relat_1('#skF_5',D_561) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3239])).

tff(c_3213,plain,(
    ! [A_556] :
      ( k3_xboole_0('#skF_3',A_556) = k1_xboole_0
      | k9_relat_1('#skF_5',A_556) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3188,c_2])).

tff(c_4104,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4064,c_3213])).

tff(c_3237,plain,(
    ! [D_561] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_561) = k7_relat_1('#skF_6',D_561)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_68,c_3235])).

tff(c_3242,plain,(
    ! [D_561] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_561) = k7_relat_1('#skF_6',D_561) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3237])).

tff(c_1990,plain,(
    ! [A_445,B_446,C_447] :
      ( k9_subset_1(A_445,B_446,C_447) = k3_xboole_0(B_446,C_447)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(A_445)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2002,plain,(
    ! [B_446] : k9_subset_1('#skF_1',B_446,'#skF_4') = k3_xboole_0(B_446,'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_1990])).

tff(c_66,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_117,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_2012,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2002,c_2002,c_117])).

tff(c_3375,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3242,c_2012])).

tff(c_5758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4915,c_4081,c_3245,c_4104,c_4104,c_3375])).

tff(c_5759,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6580,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5759])).

tff(c_19987,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19976,c_6580])).

tff(c_20001,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_10419,c_9595,c_10392,c_10392,c_8151,c_8151,c_11289,c_19987])).

tff(c_20003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_20001])).

tff(c_20004,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5759])).

tff(c_41676,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_41664,c_20004])).

tff(c_41690,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_22583,c_24022,c_20327,c_23582,c_24022,c_20327,c_25805,c_41676])).

tff(c_41692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_41690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:08:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.17/6.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.37/6.98  
% 14.37/6.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.37/6.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.37/6.99  
% 14.37/6.99  %Foreground sorts:
% 14.37/6.99  
% 14.37/6.99  
% 14.37/6.99  %Background operators:
% 14.37/6.99  
% 14.37/6.99  
% 14.37/6.99  %Foreground operators:
% 14.37/6.99  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 14.37/6.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.37/6.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.37/6.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.37/6.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.37/6.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.37/6.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.37/6.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.37/6.99  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.37/6.99  tff('#skF_5', type, '#skF_5': $i).
% 14.37/6.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.37/6.99  tff('#skF_6', type, '#skF_6': $i).
% 14.37/6.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.37/6.99  tff('#skF_2', type, '#skF_2': $i).
% 14.37/6.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.37/6.99  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.37/6.99  tff('#skF_3', type, '#skF_3': $i).
% 14.37/6.99  tff('#skF_1', type, '#skF_1': $i).
% 14.37/6.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.37/6.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.37/6.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.37/6.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.37/6.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.37/6.99  tff('#skF_4', type, '#skF_4': $i).
% 14.37/6.99  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.37/6.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.37/6.99  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 14.37/6.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.37/6.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.37/6.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.37/6.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.37/6.99  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.37/6.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.37/6.99  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.37/6.99  
% 14.70/7.04  tff(f_253, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 14.70/7.04  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.70/7.04  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.70/7.04  tff(f_123, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 14.70/7.04  tff(f_115, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 14.70/7.04  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 14.70/7.04  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 14.70/7.04  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 14.70/7.04  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 14.70/7.04  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 14.70/7.04  tff(f_52, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 14.70/7.04  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 14.70/7.04  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 14.70/7.04  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 14.70/7.04  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.70/7.04  tff(f_211, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 14.70/7.04  tff(f_129, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 14.70/7.04  tff(f_177, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 14.70/7.04  tff(c_92, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_5782, plain, (![C_763, A_764, B_765]: (v1_relat_1(C_763) | ~m1_subset_1(C_763, k1_zfmisc_1(k2_zfmisc_1(A_764, B_765))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.70/7.04  tff(c_5789, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_5782])).
% 14.70/7.04  tff(c_90, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_5791, plain, (![C_766, A_767, B_768]: (v4_relat_1(C_766, A_767) | ~m1_subset_1(C_766, k1_zfmisc_1(k2_zfmisc_1(A_767, B_768))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.70/7.04  tff(c_5798, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_5791])).
% 14.70/7.04  tff(c_20296, plain, (![B_1678, A_1679]: (k1_relat_1(B_1678)=A_1679 | ~v1_partfun1(B_1678, A_1679) | ~v4_relat_1(B_1678, A_1679) | ~v1_relat_1(B_1678))), inference(cnfTransformation, [status(thm)], [f_123])).
% 14.70/7.04  tff(c_20305, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5798, c_20296])).
% 14.70/7.04  tff(c_20314, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_20305])).
% 14.70/7.04  tff(c_21105, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_20314])).
% 14.70/7.04  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_70, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_21394, plain, (![C_1768, A_1769, B_1770]: (v1_partfun1(C_1768, A_1769) | ~v1_funct_2(C_1768, A_1769, B_1770) | ~v1_funct_1(C_1768) | ~m1_subset_1(C_1768, k1_zfmisc_1(k2_zfmisc_1(A_1769, B_1770))) | v1_xboole_0(B_1770))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.70/7.04  tff(c_21397, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_21394])).
% 14.70/7.04  tff(c_21403, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_21397])).
% 14.70/7.04  tff(c_21405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_21105, c_21403])).
% 14.70/7.04  tff(c_21406, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_20314])).
% 14.70/7.04  tff(c_32, plain, (![B_26, A_25]: (r1_xboole_0(k1_relat_1(B_26), A_25) | k7_relat_1(B_26, A_25)!=k1_xboole_0 | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.70/7.04  tff(c_21426, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21406, c_32])).
% 14.70/7.04  tff(c_21599, plain, (![A_1783]: (r1_xboole_0('#skF_4', A_1783) | k7_relat_1('#skF_6', A_1783)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_21426])).
% 14.70/7.04  tff(c_88, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_80, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_84, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_36, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | ~r1_subset_1(A_27, B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.70/7.04  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.70/7.04  tff(c_5800, plain, (![B_769, A_770]: (r1_tarski(k1_relat_1(B_769), A_770) | ~v4_relat_1(B_769, A_770) | ~v1_relat_1(B_769))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.70/7.04  tff(c_5803, plain, (![A_770]: (r1_tarski(k1_xboole_0, A_770) | ~v4_relat_1(k1_xboole_0, A_770) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_5800])).
% 14.70/7.04  tff(c_5804, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5803])).
% 14.70/7.04  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.70/7.04  tff(c_6027, plain, (![B_804, A_805]: (k1_relat_1(B_804)=A_805 | ~v1_partfun1(B_804, A_805) | ~v4_relat_1(B_804, A_805) | ~v1_relat_1(B_804))), inference(cnfTransformation, [status(thm)], [f_123])).
% 14.70/7.04  tff(c_6033, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5798, c_6027])).
% 14.70/7.04  tff(c_6039, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_6033])).
% 14.70/7.04  tff(c_6052, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_6039])).
% 14.70/7.04  tff(c_6172, plain, (![C_827, A_828, B_829]: (v1_partfun1(C_827, A_828) | ~v1_funct_2(C_827, A_828, B_829) | ~v1_funct_1(C_827) | ~m1_subset_1(C_827, k1_zfmisc_1(k2_zfmisc_1(A_828, B_829))) | v1_xboole_0(B_829))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.70/7.04  tff(c_6175, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_6172])).
% 14.70/7.04  tff(c_6181, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_6175])).
% 14.70/7.04  tff(c_6183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_6052, c_6181])).
% 14.70/7.04  tff(c_6184, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_6039])).
% 14.70/7.04  tff(c_30, plain, (![B_26, A_25]: (k7_relat_1(B_26, A_25)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.70/7.04  tff(c_6192, plain, (![A_25]: (k7_relat_1('#skF_6', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_25) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6184, c_30])).
% 14.70/7.04  tff(c_6290, plain, (![A_834]: (k7_relat_1('#skF_6', A_834)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_834))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_6192])).
% 14.70/7.04  tff(c_6376, plain, (![B_840]: (k7_relat_1('#skF_6', B_840)=k1_xboole_0 | k3_xboole_0('#skF_4', B_840)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_6290])).
% 14.70/7.04  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.70/7.04  tff(c_6385, plain, (![B_840]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6') | k3_xboole_0('#skF_4', B_840)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6376, c_16])).
% 14.70/7.04  tff(c_6393, plain, (![B_840]: (v1_relat_1(k1_xboole_0) | k3_xboole_0('#skF_4', B_840)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_6385])).
% 14.70/7.04  tff(c_6394, plain, (![B_840]: (k3_xboole_0('#skF_4', B_840)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_5804, c_6393])).
% 14.70/7.04  tff(c_20, plain, (![B_16, A_15]: (r1_xboole_0(k1_relat_1(B_16), A_15) | k9_relat_1(B_16, A_15)!=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.70/7.04  tff(c_6195, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6184, c_20])).
% 14.70/7.04  tff(c_6258, plain, (![A_832]: (r1_xboole_0('#skF_4', A_832) | k9_relat_1('#skF_6', A_832)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_6195])).
% 14.70/7.04  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.70/7.04  tff(c_6273, plain, (![A_832]: (k3_xboole_0('#skF_4', A_832)=k1_xboole_0 | k9_relat_1('#skF_6', A_832)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6258, c_2])).
% 14.70/7.04  tff(c_6396, plain, (![A_832]: (k9_relat_1('#skF_6', A_832)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_6394, c_6273])).
% 14.70/7.04  tff(c_5899, plain, (![B_787, A_788]: (k9_relat_1(B_787, A_788)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_787), A_788) | ~v1_relat_1(B_787))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.70/7.04  tff(c_5989, plain, (![B_800, A_801]: (k9_relat_1(B_800, A_801)=k1_xboole_0 | k7_relat_1(B_800, A_801)!=k1_xboole_0 | ~v1_relat_1(B_800))), inference(resolution, [status(thm)], [c_32, c_5899])).
% 14.70/7.04  tff(c_5997, plain, (![A_801]: (k9_relat_1('#skF_6', A_801)=k1_xboole_0 | k7_relat_1('#skF_6', A_801)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_5789, c_5989])).
% 14.70/7.04  tff(c_6399, plain, (![A_801]: (k7_relat_1('#skF_6', A_801)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_6396, c_5997])).
% 14.70/7.04  tff(c_24, plain, (![A_22, B_24]: (k7_relat_1(A_22, B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, k1_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.70/7.04  tff(c_6198, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6184, c_24])).
% 14.70/7.04  tff(c_6220, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_6198])).
% 14.70/7.04  tff(c_6429, plain, (![B_849]: (~r1_xboole_0(B_849, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_6399, c_6220])).
% 14.70/7.04  tff(c_6437, plain, (![A_27]: (~r1_subset_1(A_27, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_36, c_6429])).
% 14.70/7.04  tff(c_6454, plain, (![A_852]: (~r1_subset_1(A_852, '#skF_4') | v1_xboole_0(A_852))), inference(negUnitSimplification, [status(thm)], [c_84, c_6437])).
% 14.70/7.04  tff(c_6457, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_6454])).
% 14.70/7.04  tff(c_6461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_6457])).
% 14.70/7.04  tff(c_6463, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_5803])).
% 14.70/7.04  tff(c_6509, plain, (![A_864, B_865]: (k7_relat_1(A_864, B_865)=k1_xboole_0 | ~r1_xboole_0(B_865, k1_relat_1(A_864)) | ~v1_relat_1(A_864))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.70/7.04  tff(c_6524, plain, (![B_865]: (k7_relat_1(k1_xboole_0, B_865)=k1_xboole_0 | ~r1_xboole_0(B_865, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6509])).
% 14.70/7.04  tff(c_6529, plain, (![B_865]: (k7_relat_1(k1_xboole_0, B_865)=k1_xboole_0 | ~r1_xboole_0(B_865, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6463, c_6524])).
% 14.70/7.04  tff(c_21626, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_21599, c_6529])).
% 14.70/7.04  tff(c_21853, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_21626])).
% 14.70/7.04  tff(c_20150, plain, (![B_1665, A_1666]: (r1_xboole_0(k1_relat_1(B_1665), A_1666) | k9_relat_1(B_1665, A_1666)!=k1_xboole_0 | ~v1_relat_1(B_1665))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.70/7.04  tff(c_20170, plain, (![A_1666]: (r1_xboole_0(k1_xboole_0, A_1666) | k9_relat_1(k1_xboole_0, A_1666)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_20150])).
% 14.70/7.04  tff(c_20177, plain, (![A_1666]: (r1_xboole_0(k1_xboole_0, A_1666) | k9_relat_1(k1_xboole_0, A_1666)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6463, c_20170])).
% 14.70/7.04  tff(c_21423, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21406, c_24])).
% 14.70/7.04  tff(c_21629, plain, (![B_1784]: (k7_relat_1('#skF_6', B_1784)=k1_xboole_0 | ~r1_xboole_0(B_1784, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_21423])).
% 14.70/7.04  tff(c_21659, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_20177, c_21629])).
% 14.70/7.04  tff(c_22100, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_21853, c_21659])).
% 14.70/7.04  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_5790, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_5782])).
% 14.70/7.04  tff(c_5799, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_5791])).
% 14.70/7.04  tff(c_20302, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5799, c_20296])).
% 14.70/7.04  tff(c_20311, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_20302])).
% 14.70/7.04  tff(c_20328, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_20311])).
% 14.70/7.04  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_21032, plain, (![C_1742, A_1743, B_1744]: (v1_partfun1(C_1742, A_1743) | ~v1_funct_2(C_1742, A_1743, B_1744) | ~v1_funct_1(C_1742) | ~m1_subset_1(C_1742, k1_zfmisc_1(k2_zfmisc_1(A_1743, B_1744))) | v1_xboole_0(B_1744))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.70/7.04  tff(c_21038, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_21032])).
% 14.70/7.04  tff(c_21045, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_21038])).
% 14.70/7.04  tff(c_21047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_20328, c_21045])).
% 14.70/7.04  tff(c_21048, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_20311])).
% 14.70/7.04  tff(c_18, plain, (![B_16, A_15]: (k9_relat_1(B_16, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.70/7.04  tff(c_21056, plain, (![A_15]: (k9_relat_1('#skF_5', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21048, c_18])).
% 14.70/7.04  tff(c_21586, plain, (![A_1782]: (k9_relat_1('#skF_5', A_1782)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_1782))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_21056])).
% 14.70/7.04  tff(c_21590, plain, (![B_28]: (k9_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_21586])).
% 14.70/7.04  tff(c_22152, plain, (![B_1837]: (k9_relat_1('#skF_5', B_1837)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_1837) | v1_xboole_0(B_1837))), inference(negUnitSimplification, [status(thm)], [c_88, c_21590])).
% 14.70/7.04  tff(c_22155, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_22152])).
% 14.70/7.04  tff(c_22158, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_22155])).
% 14.70/7.04  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.70/7.04  tff(c_21432, plain, (![A_11]: (r1_tarski('#skF_4', A_11) | ~v4_relat_1('#skF_6', A_11) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21406, c_14])).
% 14.70/7.04  tff(c_21467, plain, (![A_1773]: (r1_tarski('#skF_4', A_1773) | ~v4_relat_1('#skF_6', A_1773))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_21432])).
% 14.70/7.04  tff(c_21471, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_5798, c_21467])).
% 14.70/7.04  tff(c_21068, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21048, c_32])).
% 14.70/7.04  tff(c_21786, plain, (![A_1793]: (r1_xboole_0('#skF_3', A_1793) | k7_relat_1('#skF_5', A_1793)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_21068])).
% 14.70/7.04  tff(c_21444, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_21423])).
% 14.70/7.04  tff(c_21816, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_21786, c_21444])).
% 14.70/7.04  tff(c_21869, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_21816])).
% 14.70/7.04  tff(c_21059, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21048, c_30])).
% 14.70/7.04  tff(c_21667, plain, (![A_1785]: (k7_relat_1('#skF_5', A_1785)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_1785))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_21059])).
% 14.70/7.04  tff(c_21671, plain, (![B_28]: (k7_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_21667])).
% 14.70/7.04  tff(c_21898, plain, (![B_1811]: (k7_relat_1('#skF_5', B_1811)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_1811) | v1_xboole_0(B_1811))), inference(negUnitSimplification, [status(thm)], [c_88, c_21671])).
% 14.70/7.04  tff(c_21904, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_21898])).
% 14.70/7.04  tff(c_21909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_21869, c_21904])).
% 14.70/7.04  tff(c_21911, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_21816])).
% 14.70/7.04  tff(c_22, plain, (![A_17, C_21, B_20]: (k9_relat_1(k7_relat_1(A_17, C_21), B_20)=k9_relat_1(A_17, B_20) | ~r1_tarski(B_20, C_21) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.70/7.04  tff(c_21929, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_5', B_20) | ~r1_tarski(B_20, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21911, c_22])).
% 14.70/7.04  tff(c_22570, plain, (![B_1875]: (k9_relat_1(k1_xboole_0, B_1875)=k9_relat_1('#skF_5', B_1875) | ~r1_tarski(B_1875, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_21929])).
% 14.70/7.04  tff(c_22573, plain, (k9_relat_1(k1_xboole_0, '#skF_4')=k9_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_21471, c_22570])).
% 14.70/7.04  tff(c_22579, plain, (k9_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22158, c_22573])).
% 14.70/7.04  tff(c_22581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22100, c_22579])).
% 14.70/7.04  tff(c_22583, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_21626])).
% 14.70/7.04  tff(c_24001, plain, (![B_2022]: (k9_relat_1('#skF_5', B_2022)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_2022) | v1_xboole_0(B_2022))), inference(negUnitSimplification, [status(thm)], [c_88, c_21590])).
% 14.70/7.04  tff(c_24004, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_24001])).
% 14.70/7.04  tff(c_24007, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_24004])).
% 14.70/7.04  tff(c_21053, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k9_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21048, c_20])).
% 14.70/7.04  tff(c_21747, plain, (![A_1792]: (r1_xboole_0('#skF_3', A_1792) | k9_relat_1('#skF_5', A_1792)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_21053])).
% 14.70/7.04  tff(c_21785, plain, (![A_1792]: (k3_xboole_0('#skF_3', A_1792)=k1_xboole_0 | k9_relat_1('#skF_5', A_1792)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_21747, c_2])).
% 14.70/7.04  tff(c_24022, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24007, c_21785])).
% 14.70/7.04  tff(c_20315, plain, (![A_1680, B_1681, C_1682]: (k9_subset_1(A_1680, B_1681, C_1682)=k3_xboole_0(B_1681, C_1682) | ~m1_subset_1(C_1682, k1_zfmisc_1(A_1680)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.70/7.04  tff(c_20327, plain, (![B_1681]: (k9_subset_1('#skF_1', B_1681, '#skF_4')=k3_xboole_0(B_1681, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_20315])).
% 14.70/7.04  tff(c_20085, plain, (![B_1660, A_1661]: (k9_relat_1(B_1660, A_1661)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_1660), A_1661) | ~v1_relat_1(B_1660))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.70/7.04  tff(c_20255, plain, (![B_1674, A_1675]: (k9_relat_1(B_1674, A_1675)=k1_xboole_0 | k7_relat_1(B_1674, A_1675)!=k1_xboole_0 | ~v1_relat_1(B_1674))), inference(resolution, [status(thm)], [c_32, c_20085])).
% 14.70/7.04  tff(c_20265, plain, (![A_1675]: (k9_relat_1('#skF_5', A_1675)=k1_xboole_0 | k7_relat_1('#skF_5', A_1675)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_5790, c_20255])).
% 14.70/7.04  tff(c_21777, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_21747, c_21444])).
% 14.70/7.04  tff(c_22639, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_21777])).
% 14.70/7.04  tff(c_22658, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20265, c_22639])).
% 14.70/7.04  tff(c_22864, plain, (![B_1909]: (k7_relat_1('#skF_5', B_1909)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_1909) | v1_xboole_0(B_1909))), inference(negUnitSimplification, [status(thm)], [c_88, c_21671])).
% 14.70/7.04  tff(c_22873, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_22864])).
% 14.70/7.04  tff(c_22879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_22658, c_22873])).
% 14.70/7.04  tff(c_22880, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_21777])).
% 14.70/7.04  tff(c_23005, plain, (![A_1925]: (k3_xboole_0('#skF_4', A_1925)=k1_xboole_0 | k7_relat_1('#skF_6', A_1925)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_21599, c_2])).
% 14.70/7.04  tff(c_23012, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22880, c_23005])).
% 14.70/7.04  tff(c_21414, plain, (![A_15]: (k9_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_21406, c_18])).
% 14.70/7.04  tff(c_21531, plain, (![A_1779]: (k9_relat_1('#skF_6', A_1779)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_1779))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_21414])).
% 14.70/7.04  tff(c_21543, plain, (![B_2]: (k9_relat_1('#skF_6', B_2)=k1_xboole_0 | k3_xboole_0('#skF_4', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_21531])).
% 14.70/7.04  tff(c_21074, plain, (![A_11]: (r1_tarski('#skF_3', A_11) | ~v4_relat_1('#skF_5', A_11) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21048, c_14])).
% 14.70/7.04  tff(c_21462, plain, (![A_1772]: (r1_tarski('#skF_3', A_1772) | ~v4_relat_1('#skF_5', A_1772))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_21074])).
% 14.70/7.04  tff(c_21466, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_5799, c_21462])).
% 14.70/7.04  tff(c_22885, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_6', B_20) | ~r1_tarski(B_20, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_22880, c_22])).
% 14.70/7.04  tff(c_23531, plain, (![B_1971]: (k9_relat_1(k1_xboole_0, B_1971)=k9_relat_1('#skF_6', B_1971) | ~r1_tarski(B_1971, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_22885])).
% 14.70/7.04  tff(c_23539, plain, (k9_relat_1(k1_xboole_0, '#skF_3')=k9_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_21466, c_23531])).
% 14.70/7.04  tff(c_21822, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_21786, c_6529])).
% 14.70/7.04  tff(c_22638, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_21822])).
% 14.70/7.04  tff(c_21065, plain, (![B_24]: (k7_relat_1('#skF_5', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21048, c_24])).
% 14.70/7.04  tff(c_21544, plain, (![B_1780]: (k7_relat_1('#skF_5', B_1780)=k1_xboole_0 | ~r1_xboole_0(B_1780, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_21065])).
% 14.70/7.04  tff(c_21569, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_20177, c_21544])).
% 14.70/7.04  tff(c_23388, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22638, c_21569])).
% 14.70/7.04  tff(c_23541, plain, (k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_23539, c_23388])).
% 14.70/7.04  tff(c_23573, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_21543, c_23541])).
% 14.70/7.04  tff(c_23580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23012, c_23573])).
% 14.70/7.04  tff(c_23582, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_21822])).
% 14.70/7.04  tff(c_23938, plain, (![A_2008, B_2005, D_2007, F_2009, C_2010, E_2006]: (v1_funct_1(k1_tmap_1(A_2008, B_2005, C_2010, D_2007, E_2006, F_2009)) | ~m1_subset_1(F_2009, k1_zfmisc_1(k2_zfmisc_1(D_2007, B_2005))) | ~v1_funct_2(F_2009, D_2007, B_2005) | ~v1_funct_1(F_2009) | ~m1_subset_1(E_2006, k1_zfmisc_1(k2_zfmisc_1(C_2010, B_2005))) | ~v1_funct_2(E_2006, C_2010, B_2005) | ~v1_funct_1(E_2006) | ~m1_subset_1(D_2007, k1_zfmisc_1(A_2008)) | v1_xboole_0(D_2007) | ~m1_subset_1(C_2010, k1_zfmisc_1(A_2008)) | v1_xboole_0(C_2010) | v1_xboole_0(B_2005) | v1_xboole_0(A_2008))), inference(cnfTransformation, [status(thm)], [f_211])).
% 14.70/7.04  tff(c_23940, plain, (![A_2008, C_2010, E_2006]: (v1_funct_1(k1_tmap_1(A_2008, '#skF_2', C_2010, '#skF_4', E_2006, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2006, k1_zfmisc_1(k2_zfmisc_1(C_2010, '#skF_2'))) | ~v1_funct_2(E_2006, C_2010, '#skF_2') | ~v1_funct_1(E_2006) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2008)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2010, k1_zfmisc_1(A_2008)) | v1_xboole_0(C_2010) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2008))), inference(resolution, [status(thm)], [c_68, c_23938])).
% 14.70/7.04  tff(c_23945, plain, (![A_2008, C_2010, E_2006]: (v1_funct_1(k1_tmap_1(A_2008, '#skF_2', C_2010, '#skF_4', E_2006, '#skF_6')) | ~m1_subset_1(E_2006, k1_zfmisc_1(k2_zfmisc_1(C_2010, '#skF_2'))) | ~v1_funct_2(E_2006, C_2010, '#skF_2') | ~v1_funct_1(E_2006) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2008)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2010, k1_zfmisc_1(A_2008)) | v1_xboole_0(C_2010) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2008))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_23940])).
% 14.70/7.04  tff(c_25339, plain, (![A_2096, C_2097, E_2098]: (v1_funct_1(k1_tmap_1(A_2096, '#skF_2', C_2097, '#skF_4', E_2098, '#skF_6')) | ~m1_subset_1(E_2098, k1_zfmisc_1(k2_zfmisc_1(C_2097, '#skF_2'))) | ~v1_funct_2(E_2098, C_2097, '#skF_2') | ~v1_funct_1(E_2098) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2096)) | ~m1_subset_1(C_2097, k1_zfmisc_1(A_2096)) | v1_xboole_0(C_2097) | v1_xboole_0(A_2096))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_23945])).
% 14.70/7.04  tff(c_25346, plain, (![A_2096]: (v1_funct_1(k1_tmap_1(A_2096, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2096)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2096)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2096))), inference(resolution, [status(thm)], [c_74, c_25339])).
% 14.70/7.04  tff(c_25356, plain, (![A_2096]: (v1_funct_1(k1_tmap_1(A_2096, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2096)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2096)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2096))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_25346])).
% 14.70/7.04  tff(c_25798, plain, (![A_2112]: (v1_funct_1(k1_tmap_1(A_2112, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2112)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2112)) | v1_xboole_0(A_2112))), inference(negUnitSimplification, [status(thm)], [c_88, c_25356])).
% 14.70/7.04  tff(c_25801, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_25798])).
% 14.70/7.04  tff(c_25804, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_25801])).
% 14.70/7.04  tff(c_25805, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_92, c_25804])).
% 14.70/7.04  tff(c_21697, plain, (![A_1787, B_1788, C_1789, D_1790]: (k2_partfun1(A_1787, B_1788, C_1789, D_1790)=k7_relat_1(C_1789, D_1790) | ~m1_subset_1(C_1789, k1_zfmisc_1(k2_zfmisc_1(A_1787, B_1788))) | ~v1_funct_1(C_1789))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.70/7.04  tff(c_21701, plain, (![D_1790]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1790)=k7_relat_1('#skF_5', D_1790) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_21697])).
% 14.70/7.04  tff(c_21707, plain, (![D_1790]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1790)=k7_relat_1('#skF_5', D_1790))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_21701])).
% 14.70/7.04  tff(c_21699, plain, (![D_1790]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1790)=k7_relat_1('#skF_6', D_1790) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_68, c_21697])).
% 14.70/7.04  tff(c_21704, plain, (![D_1790]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1790)=k7_relat_1('#skF_6', D_1790))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_21699])).
% 14.70/7.04  tff(c_62, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (v1_funct_2(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k4_subset_1(A_172, C_174, D_175), B_173) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_211])).
% 14.70/7.04  tff(c_60, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (m1_subset_1(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172, C_174, D_175), B_173))) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_211])).
% 14.70/7.04  tff(c_24201, plain, (![D_2035, B_2039, A_2036, E_2037, F_2040, C_2038]: (k2_partfun1(k4_subset_1(A_2036, C_2038, D_2035), B_2039, k1_tmap_1(A_2036, B_2039, C_2038, D_2035, E_2037, F_2040), C_2038)=E_2037 | ~m1_subset_1(k1_tmap_1(A_2036, B_2039, C_2038, D_2035, E_2037, F_2040), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2036, C_2038, D_2035), B_2039))) | ~v1_funct_2(k1_tmap_1(A_2036, B_2039, C_2038, D_2035, E_2037, F_2040), k4_subset_1(A_2036, C_2038, D_2035), B_2039) | ~v1_funct_1(k1_tmap_1(A_2036, B_2039, C_2038, D_2035, E_2037, F_2040)) | k2_partfun1(D_2035, B_2039, F_2040, k9_subset_1(A_2036, C_2038, D_2035))!=k2_partfun1(C_2038, B_2039, E_2037, k9_subset_1(A_2036, C_2038, D_2035)) | ~m1_subset_1(F_2040, k1_zfmisc_1(k2_zfmisc_1(D_2035, B_2039))) | ~v1_funct_2(F_2040, D_2035, B_2039) | ~v1_funct_1(F_2040) | ~m1_subset_1(E_2037, k1_zfmisc_1(k2_zfmisc_1(C_2038, B_2039))) | ~v1_funct_2(E_2037, C_2038, B_2039) | ~v1_funct_1(E_2037) | ~m1_subset_1(D_2035, k1_zfmisc_1(A_2036)) | v1_xboole_0(D_2035) | ~m1_subset_1(C_2038, k1_zfmisc_1(A_2036)) | v1_xboole_0(C_2038) | v1_xboole_0(B_2039) | v1_xboole_0(A_2036))), inference(cnfTransformation, [status(thm)], [f_177])).
% 14.70/7.04  tff(c_35069, plain, (![D_2578, C_2581, F_2580, B_2576, A_2579, E_2577]: (k2_partfun1(k4_subset_1(A_2579, C_2581, D_2578), B_2576, k1_tmap_1(A_2579, B_2576, C_2581, D_2578, E_2577, F_2580), C_2581)=E_2577 | ~v1_funct_2(k1_tmap_1(A_2579, B_2576, C_2581, D_2578, E_2577, F_2580), k4_subset_1(A_2579, C_2581, D_2578), B_2576) | ~v1_funct_1(k1_tmap_1(A_2579, B_2576, C_2581, D_2578, E_2577, F_2580)) | k2_partfun1(D_2578, B_2576, F_2580, k9_subset_1(A_2579, C_2581, D_2578))!=k2_partfun1(C_2581, B_2576, E_2577, k9_subset_1(A_2579, C_2581, D_2578)) | ~m1_subset_1(F_2580, k1_zfmisc_1(k2_zfmisc_1(D_2578, B_2576))) | ~v1_funct_2(F_2580, D_2578, B_2576) | ~v1_funct_1(F_2580) | ~m1_subset_1(E_2577, k1_zfmisc_1(k2_zfmisc_1(C_2581, B_2576))) | ~v1_funct_2(E_2577, C_2581, B_2576) | ~v1_funct_1(E_2577) | ~m1_subset_1(D_2578, k1_zfmisc_1(A_2579)) | v1_xboole_0(D_2578) | ~m1_subset_1(C_2581, k1_zfmisc_1(A_2579)) | v1_xboole_0(C_2581) | v1_xboole_0(B_2576) | v1_xboole_0(A_2579))), inference(resolution, [status(thm)], [c_60, c_24201])).
% 14.70/7.04  tff(c_37611, plain, (![D_2691, F_2693, B_2689, A_2692, E_2690, C_2694]: (k2_partfun1(k4_subset_1(A_2692, C_2694, D_2691), B_2689, k1_tmap_1(A_2692, B_2689, C_2694, D_2691, E_2690, F_2693), C_2694)=E_2690 | ~v1_funct_1(k1_tmap_1(A_2692, B_2689, C_2694, D_2691, E_2690, F_2693)) | k2_partfun1(D_2691, B_2689, F_2693, k9_subset_1(A_2692, C_2694, D_2691))!=k2_partfun1(C_2694, B_2689, E_2690, k9_subset_1(A_2692, C_2694, D_2691)) | ~m1_subset_1(F_2693, k1_zfmisc_1(k2_zfmisc_1(D_2691, B_2689))) | ~v1_funct_2(F_2693, D_2691, B_2689) | ~v1_funct_1(F_2693) | ~m1_subset_1(E_2690, k1_zfmisc_1(k2_zfmisc_1(C_2694, B_2689))) | ~v1_funct_2(E_2690, C_2694, B_2689) | ~v1_funct_1(E_2690) | ~m1_subset_1(D_2691, k1_zfmisc_1(A_2692)) | v1_xboole_0(D_2691) | ~m1_subset_1(C_2694, k1_zfmisc_1(A_2692)) | v1_xboole_0(C_2694) | v1_xboole_0(B_2689) | v1_xboole_0(A_2692))), inference(resolution, [status(thm)], [c_62, c_35069])).
% 14.70/7.04  tff(c_37615, plain, (![A_2692, C_2694, E_2690]: (k2_partfun1(k4_subset_1(A_2692, C_2694, '#skF_4'), '#skF_2', k1_tmap_1(A_2692, '#skF_2', C_2694, '#skF_4', E_2690, '#skF_6'), C_2694)=E_2690 | ~v1_funct_1(k1_tmap_1(A_2692, '#skF_2', C_2694, '#skF_4', E_2690, '#skF_6')) | k2_partfun1(C_2694, '#skF_2', E_2690, k9_subset_1(A_2692, C_2694, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_2692, C_2694, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2690, k1_zfmisc_1(k2_zfmisc_1(C_2694, '#skF_2'))) | ~v1_funct_2(E_2690, C_2694, '#skF_2') | ~v1_funct_1(E_2690) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2692)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2694, k1_zfmisc_1(A_2692)) | v1_xboole_0(C_2694) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2692))), inference(resolution, [status(thm)], [c_68, c_37611])).
% 14.70/7.04  tff(c_37621, plain, (![A_2692, C_2694, E_2690]: (k2_partfun1(k4_subset_1(A_2692, C_2694, '#skF_4'), '#skF_2', k1_tmap_1(A_2692, '#skF_2', C_2694, '#skF_4', E_2690, '#skF_6'), C_2694)=E_2690 | ~v1_funct_1(k1_tmap_1(A_2692, '#skF_2', C_2694, '#skF_4', E_2690, '#skF_6')) | k2_partfun1(C_2694, '#skF_2', E_2690, k9_subset_1(A_2692, C_2694, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2692, C_2694, '#skF_4')) | ~m1_subset_1(E_2690, k1_zfmisc_1(k2_zfmisc_1(C_2694, '#skF_2'))) | ~v1_funct_2(E_2690, C_2694, '#skF_2') | ~v1_funct_1(E_2690) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2692)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2694, k1_zfmisc_1(A_2692)) | v1_xboole_0(C_2694) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2692))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_21704, c_37615])).
% 14.70/7.04  tff(c_40479, plain, (![A_2774, C_2775, E_2776]: (k2_partfun1(k4_subset_1(A_2774, C_2775, '#skF_4'), '#skF_2', k1_tmap_1(A_2774, '#skF_2', C_2775, '#skF_4', E_2776, '#skF_6'), C_2775)=E_2776 | ~v1_funct_1(k1_tmap_1(A_2774, '#skF_2', C_2775, '#skF_4', E_2776, '#skF_6')) | k2_partfun1(C_2775, '#skF_2', E_2776, k9_subset_1(A_2774, C_2775, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2774, C_2775, '#skF_4')) | ~m1_subset_1(E_2776, k1_zfmisc_1(k2_zfmisc_1(C_2775, '#skF_2'))) | ~v1_funct_2(E_2776, C_2775, '#skF_2') | ~v1_funct_1(E_2776) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2774)) | ~m1_subset_1(C_2775, k1_zfmisc_1(A_2774)) | v1_xboole_0(C_2775) | v1_xboole_0(A_2774))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_37621])).
% 14.70/7.04  tff(c_40486, plain, (![A_2774]: (k2_partfun1(k4_subset_1(A_2774, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2774, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2774, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2774, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2774, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2774)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2774)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2774))), inference(resolution, [status(thm)], [c_74, c_40479])).
% 14.70/7.04  tff(c_40496, plain, (![A_2774]: (k2_partfun1(k4_subset_1(A_2774, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2774, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2774, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2774, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2774, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2774)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2774)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2774))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_21707, c_40486])).
% 14.70/7.04  tff(c_41664, plain, (![A_2790]: (k2_partfun1(k4_subset_1(A_2790, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2790, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2790, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2790, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2790, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2790)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2790)) | v1_xboole_0(A_2790))), inference(negUnitSimplification, [status(thm)], [c_88, c_40496])).
% 14.70/7.04  tff(c_6815, plain, (![B_888, A_889]: (k1_relat_1(B_888)=A_889 | ~v1_partfun1(B_888, A_889) | ~v4_relat_1(B_888, A_889) | ~v1_relat_1(B_888))), inference(cnfTransformation, [status(thm)], [f_123])).
% 14.70/7.04  tff(c_6821, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5799, c_6815])).
% 14.70/7.04  tff(c_6830, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_6821])).
% 14.70/7.04  tff(c_6834, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_6830])).
% 14.70/7.04  tff(c_7648, plain, (![C_967, A_968, B_969]: (v1_partfun1(C_967, A_968) | ~v1_funct_2(C_967, A_968, B_969) | ~v1_funct_1(C_967) | ~m1_subset_1(C_967, k1_zfmisc_1(k2_zfmisc_1(A_968, B_969))) | v1_xboole_0(B_969))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.70/7.04  tff(c_7654, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_7648])).
% 14.70/7.04  tff(c_7661, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_7654])).
% 14.70/7.04  tff(c_7663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_6834, c_7661])).
% 14.70/7.04  tff(c_7664, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_6830])).
% 14.70/7.04  tff(c_7684, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7664, c_32])).
% 14.70/7.04  tff(c_7704, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_7684])).
% 14.70/7.04  tff(c_7669, plain, (![A_15]: (k9_relat_1('#skF_5', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7664, c_18])).
% 14.70/7.04  tff(c_8463, plain, (![A_1024]: (k9_relat_1('#skF_5', A_1024)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_1024))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_7669])).
% 14.70/7.04  tff(c_8479, plain, (![A_25]: (k9_relat_1('#skF_5', A_25)=k1_xboole_0 | k7_relat_1('#skF_5', A_25)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7704, c_8463])).
% 14.70/7.04  tff(c_7672, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k9_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7664, c_20])).
% 14.70/7.04  tff(c_8419, plain, (![A_1022]: (r1_xboole_0('#skF_3', A_1022) | k9_relat_1('#skF_5', A_1022)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_7672])).
% 14.70/7.04  tff(c_8451, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_8419, c_6529])).
% 14.70/7.04  tff(c_9839, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8451])).
% 14.70/7.04  tff(c_9848, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8479, c_9839])).
% 14.70/7.04  tff(c_6660, plain, (![B_876, A_877]: (r1_xboole_0(k1_relat_1(B_876), A_877) | k9_relat_1(B_876, A_877)!=k1_xboole_0 | ~v1_relat_1(B_876))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.70/7.04  tff(c_6677, plain, (![A_877]: (r1_xboole_0(k1_xboole_0, A_877) | k9_relat_1(k1_xboole_0, A_877)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6660])).
% 14.70/7.04  tff(c_6683, plain, (![A_877]: (r1_xboole_0(k1_xboole_0, A_877) | k9_relat_1(k1_xboole_0, A_877)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6463, c_6677])).
% 14.70/7.04  tff(c_7681, plain, (![B_24]: (k7_relat_1('#skF_5', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7664, c_24])).
% 14.70/7.04  tff(c_8171, plain, (![B_1010]: (k7_relat_1('#skF_5', B_1010)=k1_xboole_0 | ~r1_xboole_0(B_1010, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_7681])).
% 14.70/7.04  tff(c_8196, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6683, c_8171])).
% 14.70/7.04  tff(c_10070, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_9848, c_8196])).
% 14.70/7.04  tff(c_6824, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5798, c_6815])).
% 14.70/7.04  tff(c_6833, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_6824])).
% 14.70/7.04  tff(c_7711, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_6833])).
% 14.70/7.04  tff(c_8034, plain, (![C_998, A_999, B_1000]: (v1_partfun1(C_998, A_999) | ~v1_funct_2(C_998, A_999, B_1000) | ~v1_funct_1(C_998) | ~m1_subset_1(C_998, k1_zfmisc_1(k2_zfmisc_1(A_999, B_1000))) | v1_xboole_0(B_1000))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.70/7.04  tff(c_8037, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_8034])).
% 14.70/7.04  tff(c_8043, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_8037])).
% 14.70/7.04  tff(c_8045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_7711, c_8043])).
% 14.70/7.04  tff(c_8046, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_6833])).
% 14.70/7.04  tff(c_8051, plain, (![A_15]: (k9_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8046, c_18])).
% 14.70/7.04  tff(c_8398, plain, (![A_1021]: (k9_relat_1('#skF_6', A_1021)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_1021))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_8051])).
% 14.70/7.04  tff(c_8783, plain, (![B_1066]: (k9_relat_1('#skF_6', B_1066)=k1_xboole_0 | k3_xboole_0('#skF_4', B_1066)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_8398])).
% 14.70/7.04  tff(c_8054, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8046, c_20])).
% 14.70/7.04  tff(c_8252, plain, (![A_1014]: (r1_xboole_0('#skF_4', A_1014) | k9_relat_1('#skF_6', A_1014)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_8054])).
% 14.70/7.04  tff(c_7702, plain, (![B_24]: (k7_relat_1('#skF_5', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_7681])).
% 14.70/7.04  tff(c_8271, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8252, c_7702])).
% 14.70/7.04  tff(c_8485, plain, (k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8271])).
% 14.70/7.04  tff(c_8806, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8783, c_8485])).
% 14.70/7.04  tff(c_8363, plain, (![A_1020]: (r1_xboole_0('#skF_3', A_1020) | k7_relat_1('#skF_5', A_1020)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_7684])).
% 14.70/7.04  tff(c_8063, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8046, c_24])).
% 14.70/7.04  tff(c_8084, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_8063])).
% 14.70/7.04  tff(c_8389, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8363, c_8084])).
% 14.70/7.04  tff(c_8588, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8389])).
% 14.70/7.04  tff(c_8473, plain, (![B_28]: (k9_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_8463])).
% 14.70/7.04  tff(c_8680, plain, (![B_1057]: (k9_relat_1('#skF_5', B_1057)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_1057) | v1_xboole_0(B_1057))), inference(negUnitSimplification, [status(thm)], [c_88, c_8473])).
% 14.70/7.04  tff(c_8686, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_8680])).
% 14.70/7.04  tff(c_8690, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_8686])).
% 14.70/7.04  tff(c_7675, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7664, c_30])).
% 14.70/7.04  tff(c_7698, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_7675])).
% 14.70/7.04  tff(c_8718, plain, (![A_1059]: (k7_relat_1('#skF_5', A_1059)=k1_xboole_0 | k9_relat_1('#skF_5', A_1059)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8419, c_7698])).
% 14.70/7.04  tff(c_8721, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8690, c_8718])).
% 14.70/7.04  tff(c_8731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8588, c_8721])).
% 14.70/7.04  tff(c_8732, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8389])).
% 14.70/7.04  tff(c_8066, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8046, c_32])).
% 14.70/7.04  tff(c_8226, plain, (![A_1013]: (r1_xboole_0('#skF_4', A_1013) | k7_relat_1('#skF_6', A_1013)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_8066])).
% 14.70/7.04  tff(c_8876, plain, (![A_1082]: (k3_xboole_0('#skF_4', A_1082)=k1_xboole_0 | k7_relat_1('#skF_6', A_1082)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8226, c_2])).
% 14.70/7.04  tff(c_8879, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8732, c_8876])).
% 14.70/7.04  tff(c_8886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8806, c_8879])).
% 14.70/7.04  tff(c_8888, plain, (k9_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8271])).
% 14.70/7.04  tff(c_7690, plain, (![A_11]: (r1_tarski('#skF_3', A_11) | ~v4_relat_1('#skF_5', A_11) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7664, c_14])).
% 14.70/7.04  tff(c_8093, plain, (![A_1001]: (r1_tarski('#skF_3', A_1001) | ~v4_relat_1('#skF_5', A_1001))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_7690])).
% 14.70/7.04  tff(c_8097, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_5799, c_8093])).
% 14.70/7.04  tff(c_8299, plain, (![B_1016]: (k7_relat_1('#skF_6', B_1016)=k1_xboole_0 | ~r1_xboole_0(B_1016, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_8063])).
% 14.70/7.04  tff(c_8319, plain, (![A_27]: (k7_relat_1('#skF_6', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_36, c_8299])).
% 14.70/7.04  tff(c_8907, plain, (![A_1083]: (k7_relat_1('#skF_6', A_1083)=k1_xboole_0 | ~r1_subset_1(A_1083, '#skF_4') | v1_xboole_0(A_1083))), inference(negUnitSimplification, [status(thm)], [c_84, c_8319])).
% 14.70/7.04  tff(c_8910, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_8907])).
% 14.70/7.04  tff(c_8913, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_88, c_8910])).
% 14.70/7.04  tff(c_8917, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_6', B_20) | ~r1_tarski(B_20, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8913, c_22])).
% 14.70/7.04  tff(c_10302, plain, (![B_1211]: (k9_relat_1(k1_xboole_0, B_1211)=k9_relat_1('#skF_6', B_1211) | ~r1_tarski(B_1211, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_8917])).
% 14.70/7.04  tff(c_10305, plain, (k9_relat_1(k1_xboole_0, '#skF_3')=k9_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_8097, c_10302])).
% 14.70/7.04  tff(c_10311, plain, (k9_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8888, c_10305])).
% 14.70/7.04  tff(c_10313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10070, c_10311])).
% 14.70/7.04  tff(c_10315, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_8451])).
% 14.70/7.04  tff(c_10409, plain, (![A_1220]: (k7_relat_1('#skF_5', A_1220)=k1_xboole_0 | k9_relat_1('#skF_5', A_1220)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8419, c_7698])).
% 14.70/7.04  tff(c_10419, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10315, c_10409])).
% 14.70/7.04  tff(c_8334, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6683, c_8299])).
% 14.70/7.04  tff(c_9024, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8334])).
% 14.70/7.04  tff(c_9216, plain, (![B_1119]: (k9_relat_1('#skF_5', B_1119)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_1119) | v1_xboole_0(B_1119))), inference(negUnitSimplification, [status(thm)], [c_88, c_8473])).
% 14.70/7.04  tff(c_9219, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_9216])).
% 14.70/7.04  tff(c_9222, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_9219])).
% 14.70/7.04  tff(c_8072, plain, (![A_11]: (r1_tarski('#skF_4', A_11) | ~v4_relat_1('#skF_6', A_11) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8046, c_14])).
% 14.70/7.04  tff(c_8098, plain, (![A_1002]: (r1_tarski('#skF_4', A_1002) | ~v4_relat_1('#skF_6', A_1002))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_8072])).
% 14.70/7.04  tff(c_8102, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_5798, c_8098])).
% 14.70/7.04  tff(c_8887, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8271])).
% 14.70/7.04  tff(c_8892, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_5', B_20) | ~r1_tarski(B_20, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8887, c_22])).
% 14.70/7.04  tff(c_9583, plain, (![B_1150]: (k9_relat_1(k1_xboole_0, B_1150)=k9_relat_1('#skF_5', B_1150) | ~r1_tarski(B_1150, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5790, c_8892])).
% 14.70/7.04  tff(c_9586, plain, (k9_relat_1(k1_xboole_0, '#skF_4')=k9_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_8102, c_9583])).
% 14.70/7.04  tff(c_9592, plain, (k9_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9222, c_9586])).
% 14.70/7.04  tff(c_9594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9024, c_9592])).
% 14.70/7.04  tff(c_9595, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_8334])).
% 14.70/7.04  tff(c_10388, plain, (![A_1218]: (k3_xboole_0('#skF_3', A_1218)=k1_xboole_0 | k7_relat_1('#skF_5', A_1218)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8363, c_2])).
% 14.70/7.04  tff(c_10392, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8887, c_10388])).
% 14.70/7.04  tff(c_8139, plain, (![A_1005, B_1006, C_1007]: (k9_subset_1(A_1005, B_1006, C_1007)=k3_xboole_0(B_1006, C_1007) | ~m1_subset_1(C_1007, k1_zfmisc_1(A_1005)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.70/7.04  tff(c_8151, plain, (![B_1006]: (k9_subset_1('#skF_1', B_1006, '#skF_4')=k3_xboole_0(B_1006, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_8139])).
% 14.70/7.04  tff(c_9792, plain, (![F_1163, B_1159, D_1161, C_1164, A_1162, E_1160]: (v1_funct_1(k1_tmap_1(A_1162, B_1159, C_1164, D_1161, E_1160, F_1163)) | ~m1_subset_1(F_1163, k1_zfmisc_1(k2_zfmisc_1(D_1161, B_1159))) | ~v1_funct_2(F_1163, D_1161, B_1159) | ~v1_funct_1(F_1163) | ~m1_subset_1(E_1160, k1_zfmisc_1(k2_zfmisc_1(C_1164, B_1159))) | ~v1_funct_2(E_1160, C_1164, B_1159) | ~v1_funct_1(E_1160) | ~m1_subset_1(D_1161, k1_zfmisc_1(A_1162)) | v1_xboole_0(D_1161) | ~m1_subset_1(C_1164, k1_zfmisc_1(A_1162)) | v1_xboole_0(C_1164) | v1_xboole_0(B_1159) | v1_xboole_0(A_1162))), inference(cnfTransformation, [status(thm)], [f_211])).
% 14.70/7.04  tff(c_9794, plain, (![A_1162, C_1164, E_1160]: (v1_funct_1(k1_tmap_1(A_1162, '#skF_2', C_1164, '#skF_4', E_1160, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1160, k1_zfmisc_1(k2_zfmisc_1(C_1164, '#skF_2'))) | ~v1_funct_2(E_1160, C_1164, '#skF_2') | ~v1_funct_1(E_1160) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1162)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1164, k1_zfmisc_1(A_1162)) | v1_xboole_0(C_1164) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1162))), inference(resolution, [status(thm)], [c_68, c_9792])).
% 14.70/7.04  tff(c_9799, plain, (![A_1162, C_1164, E_1160]: (v1_funct_1(k1_tmap_1(A_1162, '#skF_2', C_1164, '#skF_4', E_1160, '#skF_6')) | ~m1_subset_1(E_1160, k1_zfmisc_1(k2_zfmisc_1(C_1164, '#skF_2'))) | ~v1_funct_2(E_1160, C_1164, '#skF_2') | ~v1_funct_1(E_1160) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1162)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1164, k1_zfmisc_1(A_1162)) | v1_xboole_0(C_1164) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1162))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_9794])).
% 14.70/7.04  tff(c_10851, plain, (![A_1253, C_1254, E_1255]: (v1_funct_1(k1_tmap_1(A_1253, '#skF_2', C_1254, '#skF_4', E_1255, '#skF_6')) | ~m1_subset_1(E_1255, k1_zfmisc_1(k2_zfmisc_1(C_1254, '#skF_2'))) | ~v1_funct_2(E_1255, C_1254, '#skF_2') | ~v1_funct_1(E_1255) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1253)) | ~m1_subset_1(C_1254, k1_zfmisc_1(A_1253)) | v1_xboole_0(C_1254) | v1_xboole_0(A_1253))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_9799])).
% 14.70/7.04  tff(c_10858, plain, (![A_1253]: (v1_funct_1(k1_tmap_1(A_1253, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1253)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1253)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1253))), inference(resolution, [status(thm)], [c_74, c_10851])).
% 14.70/7.04  tff(c_10868, plain, (![A_1253]: (v1_funct_1(k1_tmap_1(A_1253, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1253)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1253)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1253))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_10858])).
% 14.70/7.04  tff(c_11282, plain, (![A_1283]: (v1_funct_1(k1_tmap_1(A_1283, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1283)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1283)) | v1_xboole_0(A_1283))), inference(negUnitSimplification, [status(thm)], [c_88, c_10868])).
% 14.70/7.04  tff(c_11285, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_11282])).
% 14.70/7.04  tff(c_11288, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_11285])).
% 14.70/7.04  tff(c_11289, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_92, c_11288])).
% 14.70/7.04  tff(c_8977, plain, (![A_1087, B_1088, C_1089, D_1090]: (k2_partfun1(A_1087, B_1088, C_1089, D_1090)=k7_relat_1(C_1089, D_1090) | ~m1_subset_1(C_1089, k1_zfmisc_1(k2_zfmisc_1(A_1087, B_1088))) | ~v1_funct_1(C_1089))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.70/7.04  tff(c_8981, plain, (![D_1090]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1090)=k7_relat_1('#skF_5', D_1090) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_8977])).
% 14.70/7.04  tff(c_8987, plain, (![D_1090]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1090)=k7_relat_1('#skF_5', D_1090))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8981])).
% 14.70/7.04  tff(c_8979, plain, (![D_1090]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1090)=k7_relat_1('#skF_6', D_1090) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_68, c_8977])).
% 14.70/7.04  tff(c_8984, plain, (![D_1090]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1090)=k7_relat_1('#skF_6', D_1090))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_8979])).
% 14.70/7.04  tff(c_10807, plain, (![C_1247, F_1249, A_1245, B_1248, E_1246, D_1244]: (k2_partfun1(k4_subset_1(A_1245, C_1247, D_1244), B_1248, k1_tmap_1(A_1245, B_1248, C_1247, D_1244, E_1246, F_1249), D_1244)=F_1249 | ~m1_subset_1(k1_tmap_1(A_1245, B_1248, C_1247, D_1244, E_1246, F_1249), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1245, C_1247, D_1244), B_1248))) | ~v1_funct_2(k1_tmap_1(A_1245, B_1248, C_1247, D_1244, E_1246, F_1249), k4_subset_1(A_1245, C_1247, D_1244), B_1248) | ~v1_funct_1(k1_tmap_1(A_1245, B_1248, C_1247, D_1244, E_1246, F_1249)) | k2_partfun1(D_1244, B_1248, F_1249, k9_subset_1(A_1245, C_1247, D_1244))!=k2_partfun1(C_1247, B_1248, E_1246, k9_subset_1(A_1245, C_1247, D_1244)) | ~m1_subset_1(F_1249, k1_zfmisc_1(k2_zfmisc_1(D_1244, B_1248))) | ~v1_funct_2(F_1249, D_1244, B_1248) | ~v1_funct_1(F_1249) | ~m1_subset_1(E_1246, k1_zfmisc_1(k2_zfmisc_1(C_1247, B_1248))) | ~v1_funct_2(E_1246, C_1247, B_1248) | ~v1_funct_1(E_1246) | ~m1_subset_1(D_1244, k1_zfmisc_1(A_1245)) | v1_xboole_0(D_1244) | ~m1_subset_1(C_1247, k1_zfmisc_1(A_1245)) | v1_xboole_0(C_1247) | v1_xboole_0(B_1248) | v1_xboole_0(A_1245))), inference(cnfTransformation, [status(thm)], [f_177])).
% 14.70/7.04  tff(c_14597, plain, (![D_1469, C_1472, E_1468, A_1470, B_1467, F_1471]: (k2_partfun1(k4_subset_1(A_1470, C_1472, D_1469), B_1467, k1_tmap_1(A_1470, B_1467, C_1472, D_1469, E_1468, F_1471), D_1469)=F_1471 | ~v1_funct_2(k1_tmap_1(A_1470, B_1467, C_1472, D_1469, E_1468, F_1471), k4_subset_1(A_1470, C_1472, D_1469), B_1467) | ~v1_funct_1(k1_tmap_1(A_1470, B_1467, C_1472, D_1469, E_1468, F_1471)) | k2_partfun1(D_1469, B_1467, F_1471, k9_subset_1(A_1470, C_1472, D_1469))!=k2_partfun1(C_1472, B_1467, E_1468, k9_subset_1(A_1470, C_1472, D_1469)) | ~m1_subset_1(F_1471, k1_zfmisc_1(k2_zfmisc_1(D_1469, B_1467))) | ~v1_funct_2(F_1471, D_1469, B_1467) | ~v1_funct_1(F_1471) | ~m1_subset_1(E_1468, k1_zfmisc_1(k2_zfmisc_1(C_1472, B_1467))) | ~v1_funct_2(E_1468, C_1472, B_1467) | ~v1_funct_1(E_1468) | ~m1_subset_1(D_1469, k1_zfmisc_1(A_1470)) | v1_xboole_0(D_1469) | ~m1_subset_1(C_1472, k1_zfmisc_1(A_1470)) | v1_xboole_0(C_1472) | v1_xboole_0(B_1467) | v1_xboole_0(A_1470))), inference(resolution, [status(thm)], [c_60, c_10807])).
% 14.70/7.04  tff(c_18301, plain, (![D_1597, F_1599, C_1600, B_1595, A_1598, E_1596]: (k2_partfun1(k4_subset_1(A_1598, C_1600, D_1597), B_1595, k1_tmap_1(A_1598, B_1595, C_1600, D_1597, E_1596, F_1599), D_1597)=F_1599 | ~v1_funct_1(k1_tmap_1(A_1598, B_1595, C_1600, D_1597, E_1596, F_1599)) | k2_partfun1(D_1597, B_1595, F_1599, k9_subset_1(A_1598, C_1600, D_1597))!=k2_partfun1(C_1600, B_1595, E_1596, k9_subset_1(A_1598, C_1600, D_1597)) | ~m1_subset_1(F_1599, k1_zfmisc_1(k2_zfmisc_1(D_1597, B_1595))) | ~v1_funct_2(F_1599, D_1597, B_1595) | ~v1_funct_1(F_1599) | ~m1_subset_1(E_1596, k1_zfmisc_1(k2_zfmisc_1(C_1600, B_1595))) | ~v1_funct_2(E_1596, C_1600, B_1595) | ~v1_funct_1(E_1596) | ~m1_subset_1(D_1597, k1_zfmisc_1(A_1598)) | v1_xboole_0(D_1597) | ~m1_subset_1(C_1600, k1_zfmisc_1(A_1598)) | v1_xboole_0(C_1600) | v1_xboole_0(B_1595) | v1_xboole_0(A_1598))), inference(resolution, [status(thm)], [c_62, c_14597])).
% 14.70/7.04  tff(c_18305, plain, (![A_1598, C_1600, E_1596]: (k2_partfun1(k4_subset_1(A_1598, C_1600, '#skF_4'), '#skF_2', k1_tmap_1(A_1598, '#skF_2', C_1600, '#skF_4', E_1596, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1598, '#skF_2', C_1600, '#skF_4', E_1596, '#skF_6')) | k2_partfun1(C_1600, '#skF_2', E_1596, k9_subset_1(A_1598, C_1600, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1598, C_1600, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1596, k1_zfmisc_1(k2_zfmisc_1(C_1600, '#skF_2'))) | ~v1_funct_2(E_1596, C_1600, '#skF_2') | ~v1_funct_1(E_1596) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1598)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1600, k1_zfmisc_1(A_1598)) | v1_xboole_0(C_1600) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1598))), inference(resolution, [status(thm)], [c_68, c_18301])).
% 14.70/7.04  tff(c_18311, plain, (![A_1598, C_1600, E_1596]: (k2_partfun1(k4_subset_1(A_1598, C_1600, '#skF_4'), '#skF_2', k1_tmap_1(A_1598, '#skF_2', C_1600, '#skF_4', E_1596, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1598, '#skF_2', C_1600, '#skF_4', E_1596, '#skF_6')) | k2_partfun1(C_1600, '#skF_2', E_1596, k9_subset_1(A_1598, C_1600, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1598, C_1600, '#skF_4')) | ~m1_subset_1(E_1596, k1_zfmisc_1(k2_zfmisc_1(C_1600, '#skF_2'))) | ~v1_funct_2(E_1596, C_1600, '#skF_2') | ~v1_funct_1(E_1596) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1598)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1600, k1_zfmisc_1(A_1598)) | v1_xboole_0(C_1600) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1598))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_8984, c_18305])).
% 14.70/7.04  tff(c_19160, plain, (![A_1634, C_1635, E_1636]: (k2_partfun1(k4_subset_1(A_1634, C_1635, '#skF_4'), '#skF_2', k1_tmap_1(A_1634, '#skF_2', C_1635, '#skF_4', E_1636, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1634, '#skF_2', C_1635, '#skF_4', E_1636, '#skF_6')) | k2_partfun1(C_1635, '#skF_2', E_1636, k9_subset_1(A_1634, C_1635, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1634, C_1635, '#skF_4')) | ~m1_subset_1(E_1636, k1_zfmisc_1(k2_zfmisc_1(C_1635, '#skF_2'))) | ~v1_funct_2(E_1636, C_1635, '#skF_2') | ~v1_funct_1(E_1636) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1634)) | ~m1_subset_1(C_1635, k1_zfmisc_1(A_1634)) | v1_xboole_0(C_1635) | v1_xboole_0(A_1634))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_18311])).
% 14.70/7.04  tff(c_19167, plain, (![A_1634]: (k2_partfun1(k4_subset_1(A_1634, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1634, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1634, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1634, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1634, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1634)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1634)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1634))), inference(resolution, [status(thm)], [c_74, c_19160])).
% 14.70/7.04  tff(c_19177, plain, (![A_1634]: (k2_partfun1(k4_subset_1(A_1634, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1634, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1634, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1634, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1634, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1634)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1634)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1634))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_8987, c_19167])).
% 14.70/7.04  tff(c_19976, plain, (![A_1654]: (k2_partfun1(k4_subset_1(A_1654, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1654, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1654, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1654, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1654, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1654)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1654)) | v1_xboole_0(A_1654))), inference(negUnitSimplification, [status(thm)], [c_88, c_19177])).
% 14.70/7.04  tff(c_139, plain, (![C_245, A_246, B_247]: (v1_relat_1(C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.70/7.04  tff(c_146, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_139])).
% 14.70/7.04  tff(c_1664, plain, (![C_412, A_413, B_414]: (v4_relat_1(C_412, A_413) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.70/7.04  tff(c_1671, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_1664])).
% 14.70/7.04  tff(c_2076, plain, (![B_455, A_456]: (k1_relat_1(B_455)=A_456 | ~v1_partfun1(B_455, A_456) | ~v4_relat_1(B_455, A_456) | ~v1_relat_1(B_455))), inference(cnfTransformation, [status(thm)], [f_123])).
% 14.70/7.04  tff(c_2082, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1671, c_2076])).
% 14.70/7.04  tff(c_2091, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2082])).
% 14.70/7.04  tff(c_2667, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2091])).
% 14.70/7.04  tff(c_2942, plain, (![C_540, A_541, B_542]: (v1_partfun1(C_540, A_541) | ~v1_funct_2(C_540, A_541, B_542) | ~v1_funct_1(C_540) | ~m1_subset_1(C_540, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))) | v1_xboole_0(B_542))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.70/7.04  tff(c_2945, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2942])).
% 14.70/7.04  tff(c_2951, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2945])).
% 14.70/7.04  tff(c_2953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2667, c_2951])).
% 14.70/7.04  tff(c_2954, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_2091])).
% 14.70/7.04  tff(c_2968, plain, (![A_15]: (k9_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_18])).
% 14.70/7.04  tff(c_3171, plain, (![A_555]: (k9_relat_1('#skF_6', A_555)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_555))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2968])).
% 14.70/7.04  tff(c_3187, plain, (![B_2]: (k9_relat_1('#skF_6', B_2)=k1_xboole_0 | k3_xboole_0('#skF_4', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_3171])).
% 14.70/7.04  tff(c_2974, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_20])).
% 14.70/7.04  tff(c_3267, plain, (![A_563]: (r1_xboole_0('#skF_4', A_563) | k9_relat_1('#skF_6', A_563)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2974])).
% 14.70/7.04  tff(c_148, plain, (![B_248, A_249]: (v4_relat_1(B_248, A_249) | ~r1_tarski(k1_relat_1(B_248), A_249) | ~v1_relat_1(B_248))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.70/7.04  tff(c_151, plain, (![A_249]: (v4_relat_1(k1_xboole_0, A_249) | ~r1_tarski(k1_xboole_0, A_249) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_148])).
% 14.70/7.04  tff(c_152, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_151])).
% 14.70/7.04  tff(c_153, plain, (![C_250, A_251, B_252]: (v4_relat_1(C_250, A_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.70/7.04  tff(c_160, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_153])).
% 14.70/7.04  tff(c_370, plain, (![B_285, A_286]: (k1_relat_1(B_285)=A_286 | ~v1_partfun1(B_285, A_286) | ~v4_relat_1(B_285, A_286) | ~v1_relat_1(B_285))), inference(cnfTransformation, [status(thm)], [f_123])).
% 14.70/7.04  tff(c_376, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_160, c_370])).
% 14.70/7.04  tff(c_382, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_376])).
% 14.70/7.04  tff(c_940, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_382])).
% 14.70/7.04  tff(c_1171, plain, (![C_373, A_374, B_375]: (v1_partfun1(C_373, A_374) | ~v1_funct_2(C_373, A_374, B_375) | ~v1_funct_1(C_373) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))) | v1_xboole_0(B_375))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.70/7.04  tff(c_1174, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_1171])).
% 14.70/7.04  tff(c_1180, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1174])).
% 14.70/7.04  tff(c_1182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_940, c_1180])).
% 14.70/7.04  tff(c_1183, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_382])).
% 14.70/7.04  tff(c_1200, plain, (![A_25]: (k7_relat_1('#skF_6', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_25) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1183, c_30])).
% 14.70/7.04  tff(c_1287, plain, (![A_383]: (k7_relat_1('#skF_6', A_383)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_383))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1200])).
% 14.70/7.04  tff(c_1574, plain, (![B_403]: (k7_relat_1('#skF_6', B_403)=k1_xboole_0 | k3_xboole_0('#skF_4', B_403)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1287])).
% 14.70/7.04  tff(c_1583, plain, (![B_403]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6') | k3_xboole_0('#skF_4', B_403)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1574, c_16])).
% 14.70/7.04  tff(c_1591, plain, (![B_403]: (v1_relat_1(k1_xboole_0) | k3_xboole_0('#skF_4', B_403)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1583])).
% 14.70/7.04  tff(c_1592, plain, (![B_403]: (k3_xboole_0('#skF_4', B_403)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_152, c_1591])).
% 14.70/7.04  tff(c_1191, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1183, c_32])).
% 14.70/7.04  tff(c_1317, plain, (![A_386]: (r1_xboole_0('#skF_4', A_386) | k7_relat_1('#skF_6', A_386)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1191])).
% 14.70/7.04  tff(c_1336, plain, (![A_386]: (k3_xboole_0('#skF_4', A_386)=k1_xboole_0 | k7_relat_1('#skF_6', A_386)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1317, c_2])).
% 14.70/7.04  tff(c_1610, plain, (![A_386]: (k7_relat_1('#skF_6', A_386)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1592, c_1336])).
% 14.70/7.04  tff(c_1197, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1183, c_24])).
% 14.70/7.04  tff(c_1219, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1197])).
% 14.70/7.04  tff(c_1615, plain, (![B_409]: (~r1_xboole_0(B_409, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1610, c_1219])).
% 14.70/7.04  tff(c_1635, plain, (![A_27]: (~r1_subset_1(A_27, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_36, c_1615])).
% 14.70/7.04  tff(c_1653, plain, (![A_410]: (~r1_subset_1(A_410, '#skF_4') | v1_xboole_0(A_410))), inference(negUnitSimplification, [status(thm)], [c_84, c_1635])).
% 14.70/7.04  tff(c_1656, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1653])).
% 14.70/7.04  tff(c_1660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1656])).
% 14.70/7.04  tff(c_1662, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_151])).
% 14.70/7.04  tff(c_1718, plain, (![A_427, B_428]: (k7_relat_1(A_427, B_428)=k1_xboole_0 | ~r1_xboole_0(B_428, k1_relat_1(A_427)) | ~v1_relat_1(A_427))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.70/7.04  tff(c_1737, plain, (![B_428]: (k7_relat_1(k1_xboole_0, B_428)=k1_xboole_0 | ~r1_xboole_0(B_428, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1718])).
% 14.70/7.04  tff(c_1743, plain, (![B_428]: (k7_relat_1(k1_xboole_0, B_428)=k1_xboole_0 | ~r1_xboole_0(B_428, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1662, c_1737])).
% 14.70/7.04  tff(c_3298, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_3267, c_1743])).
% 14.70/7.04  tff(c_4212, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3298])).
% 14.70/7.04  tff(c_4225, plain, (k3_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3187, c_4212])).
% 14.70/7.04  tff(c_2965, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_32])).
% 14.70/7.04  tff(c_3068, plain, (![A_550]: (r1_xboole_0('#skF_4', A_550) | k7_relat_1('#skF_6', A_550)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2965])).
% 14.70/7.04  tff(c_3086, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_3068, c_1743])).
% 14.70/7.04  tff(c_4419, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3086])).
% 14.70/7.04  tff(c_1692, plain, (![B_420, A_421]: (r1_xboole_0(k1_relat_1(B_420), A_421) | k9_relat_1(B_420, A_421)!=k1_xboole_0 | ~v1_relat_1(B_420))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.70/7.04  tff(c_1698, plain, (![A_421]: (r1_xboole_0(k1_xboole_0, A_421) | k9_relat_1(k1_xboole_0, A_421)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1692])).
% 14.70/7.04  tff(c_1701, plain, (![A_421]: (r1_xboole_0(k1_xboole_0, A_421) | k9_relat_1(k1_xboole_0, A_421)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1662, c_1698])).
% 14.70/7.04  tff(c_2971, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_24])).
% 14.70/7.04  tff(c_3089, plain, (![B_551]: (k7_relat_1('#skF_6', B_551)=k1_xboole_0 | ~r1_xboole_0(B_551, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2971])).
% 14.70/7.04  tff(c_3124, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1701, c_3089])).
% 14.70/7.04  tff(c_4471, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4419, c_3124])).
% 14.70/7.04  tff(c_147, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_139])).
% 14.70/7.04  tff(c_1672, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_1664])).
% 14.70/7.04  tff(c_2079, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1672, c_2076])).
% 14.70/7.04  tff(c_2088, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2079])).
% 14.70/7.04  tff(c_2095, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_2088])).
% 14.70/7.04  tff(c_2595, plain, (![C_512, A_513, B_514]: (v1_partfun1(C_512, A_513) | ~v1_funct_2(C_512, A_513, B_514) | ~v1_funct_1(C_512) | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(A_513, B_514))) | v1_xboole_0(B_514))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.70/7.04  tff(c_2601, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_2595])).
% 14.70/7.04  tff(c_2608, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2601])).
% 14.70/7.04  tff(c_2610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2095, c_2608])).
% 14.70/7.04  tff(c_2611, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_2088])).
% 14.70/7.04  tff(c_2625, plain, (![A_15]: (k9_relat_1('#skF_5', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2611, c_18])).
% 14.70/7.04  tff(c_3214, plain, (![A_557]: (k9_relat_1('#skF_5', A_557)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_557))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2625])).
% 14.70/7.04  tff(c_3224, plain, (![B_28]: (k9_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_3214])).
% 14.70/7.04  tff(c_4058, plain, (![B_634]: (k9_relat_1('#skF_5', B_634)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_634) | v1_xboole_0(B_634))), inference(negUnitSimplification, [status(thm)], [c_88, c_3224])).
% 14.70/7.04  tff(c_4061, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_4058])).
% 14.70/7.04  tff(c_4064, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_4061])).
% 14.70/7.04  tff(c_2977, plain, (![A_11]: (r1_tarski('#skF_4', A_11) | ~v4_relat_1('#skF_6', A_11) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_14])).
% 14.70/7.04  tff(c_3029, plain, (![A_545]: (r1_tarski('#skF_4', A_545) | ~v4_relat_1('#skF_6', A_545))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2977])).
% 14.70/7.04  tff(c_3037, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1671, c_3029])).
% 14.70/7.04  tff(c_2616, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2611, c_30])).
% 14.70/7.04  tff(c_3246, plain, (![A_562]: (k7_relat_1('#skF_5', A_562)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_562))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2616])).
% 14.70/7.04  tff(c_3256, plain, (![B_28]: (k7_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_3246])).
% 14.70/7.04  tff(c_3354, plain, (![B_565]: (k7_relat_1('#skF_5', B_565)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_565) | v1_xboole_0(B_565))), inference(negUnitSimplification, [status(thm)], [c_88, c_3256])).
% 14.70/7.04  tff(c_3357, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_3354])).
% 14.70/7.04  tff(c_3360, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_3357])).
% 14.70/7.04  tff(c_3364, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_5', B_20) | ~r1_tarski(B_20, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3360, c_22])).
% 14.70/7.04  tff(c_4630, plain, (![B_686]: (k9_relat_1(k1_xboole_0, B_686)=k9_relat_1('#skF_5', B_686) | ~r1_tarski(B_686, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_3364])).
% 14.70/7.04  tff(c_4633, plain, (k9_relat_1(k1_xboole_0, '#skF_4')=k9_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3037, c_4630])).
% 14.70/7.04  tff(c_4639, plain, (k9_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4064, c_4633])).
% 14.70/7.04  tff(c_4641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4471, c_4639])).
% 14.70/7.04  tff(c_4643, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3086])).
% 14.70/7.04  tff(c_3088, plain, (![A_550]: (k3_xboole_0('#skF_4', A_550)=k1_xboole_0 | k7_relat_1('#skF_6', A_550)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3068, c_2])).
% 14.70/7.04  tff(c_4680, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4643, c_3088])).
% 14.70/7.04  tff(c_4704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4225, c_4680])).
% 14.70/7.04  tff(c_4706, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3298])).
% 14.70/7.04  tff(c_2959, plain, (![A_25]: (k7_relat_1('#skF_6', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_25) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2954, c_30])).
% 14.70/7.04  tff(c_2984, plain, (![A_25]: (k7_relat_1('#skF_6', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_25))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2959])).
% 14.70/7.04  tff(c_4908, plain, (![A_703]: (k7_relat_1('#skF_6', A_703)=k1_xboole_0 | k9_relat_1('#skF_6', A_703)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3267, c_2984])).
% 14.70/7.04  tff(c_4915, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4706, c_4908])).
% 14.70/7.04  tff(c_2622, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2611, c_32])).
% 14.70/7.04  tff(c_3128, plain, (![A_553]: (r1_xboole_0('#skF_3', A_553) | k7_relat_1('#skF_5', A_553)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2622])).
% 14.70/7.04  tff(c_2992, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2971])).
% 14.70/7.04  tff(c_3147, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3128, c_2992])).
% 14.70/7.04  tff(c_3816, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3360, c_3147])).
% 14.70/7.04  tff(c_2988, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_2965])).
% 14.70/7.04  tff(c_3183, plain, (![A_25]: (k9_relat_1('#skF_6', A_25)=k1_xboole_0 | k7_relat_1('#skF_6', A_25)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2988, c_3171])).
% 14.70/7.04  tff(c_2634, plain, (![A_11]: (r1_tarski('#skF_3', A_11) | ~v4_relat_1('#skF_5', A_11) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2611, c_14])).
% 14.70/7.04  tff(c_3038, plain, (![A_546]: (r1_tarski('#skF_3', A_546) | ~v4_relat_1('#skF_5', A_546))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2634])).
% 14.70/7.04  tff(c_3046, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1672, c_3038])).
% 14.70/7.04  tff(c_3829, plain, (![B_20]: (k9_relat_1(k1_xboole_0, B_20)=k9_relat_1('#skF_6', B_20) | ~r1_tarski(B_20, '#skF_3') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3816, c_22])).
% 14.70/7.04  tff(c_3975, plain, (![B_628]: (k9_relat_1(k1_xboole_0, B_628)=k9_relat_1('#skF_6', B_628) | ~r1_tarski(B_628, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_3829])).
% 14.70/7.04  tff(c_3983, plain, (k9_relat_1(k1_xboole_0, '#skF_3')=k9_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_3046, c_3975])).
% 14.70/7.04  tff(c_2645, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2622])).
% 14.70/7.04  tff(c_3557, plain, (![A_587]: (k9_relat_1('#skF_5', A_587)=k1_xboole_0 | k7_relat_1('#skF_5', A_587)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2645, c_3214])).
% 14.70/7.04  tff(c_2631, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k9_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2611, c_20])).
% 14.70/7.04  tff(c_3188, plain, (![A_556]: (r1_xboole_0('#skF_3', A_556) | k9_relat_1('#skF_5', A_556)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2631])).
% 14.70/7.04  tff(c_3211, plain, (k7_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_3188, c_1743])).
% 14.70/7.04  tff(c_3485, plain, (k9_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3211])).
% 14.70/7.04  tff(c_3580, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3557, c_3485])).
% 14.70/7.04  tff(c_2628, plain, (![B_24]: (k7_relat_1('#skF_5', B_24)=k1_xboole_0 | ~r1_xboole_0(B_24, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2611, c_24])).
% 14.70/7.04  tff(c_3301, plain, (![B_564]: (k7_relat_1('#skF_5', B_564)=k1_xboole_0 | ~r1_xboole_0(B_564, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2628])).
% 14.70/7.04  tff(c_3351, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1701, c_3301])).
% 14.70/7.04  tff(c_3647, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3580, c_3351])).
% 14.70/7.04  tff(c_3986, plain, (k9_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3983, c_3647])).
% 14.70/7.04  tff(c_4013, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3183, c_3986])).
% 14.70/7.04  tff(c_4020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3816, c_4013])).
% 14.70/7.04  tff(c_4022, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3211])).
% 14.70/7.04  tff(c_2651, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k9_relat_1('#skF_5', A_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2631])).
% 14.70/7.04  tff(c_3261, plain, (![A_15]: (k7_relat_1('#skF_5', A_15)=k1_xboole_0 | k9_relat_1('#skF_5', A_15)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2651, c_3246])).
% 14.70/7.04  tff(c_4081, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4022, c_3261])).
% 14.70/7.04  tff(c_3235, plain, (![A_558, B_559, C_560, D_561]: (k2_partfun1(A_558, B_559, C_560, D_561)=k7_relat_1(C_560, D_561) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(A_558, B_559))) | ~v1_funct_1(C_560))), inference(cnfTransformation, [status(thm)], [f_129])).
% 14.70/7.04  tff(c_3239, plain, (![D_561]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_561)=k7_relat_1('#skF_5', D_561) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_74, c_3235])).
% 14.70/7.04  tff(c_3245, plain, (![D_561]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_561)=k7_relat_1('#skF_5', D_561))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3239])).
% 14.70/7.04  tff(c_3213, plain, (![A_556]: (k3_xboole_0('#skF_3', A_556)=k1_xboole_0 | k9_relat_1('#skF_5', A_556)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3188, c_2])).
% 14.70/7.04  tff(c_4104, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4064, c_3213])).
% 14.70/7.04  tff(c_3237, plain, (![D_561]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_561)=k7_relat_1('#skF_6', D_561) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_68, c_3235])).
% 14.70/7.04  tff(c_3242, plain, (![D_561]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_561)=k7_relat_1('#skF_6', D_561))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3237])).
% 14.70/7.04  tff(c_1990, plain, (![A_445, B_446, C_447]: (k9_subset_1(A_445, B_446, C_447)=k3_xboole_0(B_446, C_447) | ~m1_subset_1(C_447, k1_zfmisc_1(A_445)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.70/7.04  tff(c_2002, plain, (![B_446]: (k9_subset_1('#skF_1', B_446, '#skF_4')=k3_xboole_0(B_446, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_1990])).
% 14.70/7.04  tff(c_66, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 14.70/7.04  tff(c_117, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 14.70/7.04  tff(c_2012, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2002, c_2002, c_117])).
% 14.70/7.04  tff(c_3375, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3242, c_2012])).
% 14.70/7.04  tff(c_5758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4915, c_4081, c_3245, c_4104, c_4104, c_3375])).
% 14.70/7.04  tff(c_5759, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 14.70/7.04  tff(c_6580, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_5759])).
% 14.70/7.04  tff(c_19987, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19976, c_6580])).
% 14.70/7.04  tff(c_20001, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_10419, c_9595, c_10392, c_10392, c_8151, c_8151, c_11289, c_19987])).
% 14.70/7.04  tff(c_20003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_20001])).
% 14.70/7.04  tff(c_20004, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_5759])).
% 14.70/7.04  tff(c_41676, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_41664, c_20004])).
% 14.70/7.04  tff(c_41690, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_22583, c_24022, c_20327, c_23582, c_24022, c_20327, c_25805, c_41676])).
% 14.70/7.04  tff(c_41692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_41690])).
% 14.70/7.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.70/7.04  
% 14.70/7.04  Inference rules
% 14.70/7.04  ----------------------
% 14.70/7.04  #Ref     : 0
% 14.70/7.04  #Sup     : 8725
% 14.70/7.04  #Fact    : 0
% 14.70/7.04  #Define  : 0
% 14.70/7.04  #Split   : 90
% 14.70/7.04  #Chain   : 0
% 14.70/7.04  #Close   : 0
% 14.70/7.04  
% 14.70/7.04  Ordering : KBO
% 14.70/7.04  
% 14.70/7.04  Simplification rules
% 14.70/7.04  ----------------------
% 14.70/7.04  #Subsume      : 2511
% 14.70/7.04  #Demod        : 6723
% 14.70/7.04  #Tautology    : 3798
% 14.70/7.04  #SimpNegUnit  : 783
% 14.70/7.04  #BackRed      : 34
% 14.70/7.04  
% 14.70/7.04  #Partial instantiations: 0
% 14.70/7.04  #Strategies tried      : 1
% 14.70/7.04  
% 14.70/7.04  Timing (in seconds)
% 14.70/7.04  ----------------------
% 14.70/7.05  Preprocessing        : 0.42
% 14.70/7.05  Parsing              : 0.21
% 14.70/7.05  CNF conversion       : 0.06
% 14.70/7.05  Main loop            : 5.72
% 14.70/7.05  Inferencing          : 1.64
% 14.70/7.05  Reduction            : 1.92
% 14.70/7.05  Demodulation         : 1.33
% 14.70/7.05  BG Simplification    : 0.13
% 14.70/7.05  Subsumption          : 1.68
% 14.70/7.05  Abstraction          : 0.17
% 14.70/7.05  MUC search           : 0.00
% 14.70/7.05  Cooper               : 0.00
% 14.70/7.05  Total                : 6.32
% 14.70/7.05  Index Insertion      : 0.00
% 14.70/7.05  Index Deletion       : 0.00
% 14.70/7.05  Index Matching       : 0.00
% 14.70/7.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
