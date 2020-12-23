%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:11 EST 2020

% Result     : Theorem 29.88s
% Output     : CNFRefutation 30.48s
% Verified   : 
% Statistics : Number of formulae       :  541 (3800 expanded)
%              Number of leaves         :   55 (1297 expanded)
%              Depth                    :   17
%              Number of atoms          : 1637 (16022 expanded)
%              Number of equality atoms :  377 (3806 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_264,negated_conjecture,(
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

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_92,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_222,axiom,(
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

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_188,axiom,(
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

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_7145,plain,(
    ! [C_868,A_869,B_870] :
      ( v1_relat_1(C_868)
      | ~ m1_subset_1(C_868,k1_zfmisc_1(k2_zfmisc_1(A_869,B_870))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7153,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_7145])).

tff(c_6734,plain,(
    ! [C_813,A_814,B_815] :
      ( v1_relat_1(C_813)
      | ~ m1_subset_1(C_813,k1_zfmisc_1(k2_zfmisc_1(A_814,B_815))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6742,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_6734])).

tff(c_24,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6766,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6742,c_24])).

tff(c_6781,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6766])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,(
    ! [A_239] :
      ( k7_relat_1(A_239,k1_relat_1(A_239)) = A_239
      | ~ v1_relat_1(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_115,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_106])).

tff(c_6660,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_42,plain,(
    ! [A_33] :
      ( r1_xboole_0('#skF_1'(A_33),A_33)
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6801,plain,(
    ! [A_826,B_827] :
      ( k7_relat_1(A_826,B_827) = k1_xboole_0
      | ~ r1_xboole_0(B_827,k1_relat_1(A_826))
      | ~ v1_relat_1(A_826) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6949,plain,(
    ! [A_850] :
      ( k7_relat_1(A_850,'#skF_1'(k1_relat_1(A_850))) = k1_xboole_0
      | ~ v1_relat_1(A_850)
      | k1_relat_1(A_850) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_6801])).

tff(c_6897,plain,(
    ! [B_839,A_840] :
      ( k3_xboole_0(B_839,k2_zfmisc_1(A_840,k2_relat_1(B_839))) = k7_relat_1(B_839,A_840)
      | ~ v1_relat_1(B_839) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k3_xboole_0(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6903,plain,(
    ! [B_839,A_840] :
      ( v1_relat_1(k7_relat_1(B_839,A_840))
      | ~ v1_relat_1(B_839)
      | ~ v1_relat_1(B_839) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6897,c_12])).

tff(c_6955,plain,(
    ! [A_850] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_850)
      | ~ v1_relat_1(A_850)
      | ~ v1_relat_1(A_850)
      | k1_relat_1(A_850) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6949,c_6903])).

tff(c_7014,plain,(
    ! [A_854] :
      ( ~ v1_relat_1(A_854)
      | ~ v1_relat_1(A_854)
      | ~ v1_relat_1(A_854)
      | k1_relat_1(A_854) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_6660,c_6955])).

tff(c_7018,plain,
    ( ~ v1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6742,c_7014])).

tff(c_7026,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_7018])).

tff(c_7028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6781,c_7026])).

tff(c_7029,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6766])).

tff(c_7040,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7029,c_6660])).

tff(c_7047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_7040])).

tff(c_7048,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_7154,plain,(
    ! [C_871,A_872,B_873] :
      ( v4_relat_1(C_871,A_872)
      | ~ m1_subset_1(C_871,k1_zfmisc_1(k2_zfmisc_1(A_872,B_873))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_7162,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_7154])).

tff(c_44428,plain,(
    ! [B_1545,A_1546] :
      ( k1_relat_1(B_1545) = A_1546
      | ~ v1_partfun1(B_1545,A_1546)
      | ~ v4_relat_1(B_1545,A_1546)
      | ~ v1_relat_1(B_1545) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44431,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7162,c_44428])).

tff(c_44437,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_44431])).

tff(c_44441,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44437])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_45274,plain,(
    ! [C_1598,A_1599,B_1600] :
      ( v1_partfun1(C_1598,A_1599)
      | ~ v1_funct_2(C_1598,A_1599,B_1600)
      | ~ v1_funct_1(C_1598)
      | ~ m1_subset_1(C_1598,k1_zfmisc_1(k2_zfmisc_1(A_1599,B_1600)))
      | v1_xboole_0(B_1600) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_45280,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_45274])).

tff(c_45287,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_45280])).

tff(c_45289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_44441,c_45287])).

tff(c_45290,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44437])).

tff(c_7177,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7153,c_24])).

tff(c_44271,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7177])).

tff(c_45292,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45290,c_44271])).

tff(c_16,plain,(
    ! [A_16,B_18] :
      ( k7_relat_1(A_16,B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,k1_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_45296,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45290,c_16])).

tff(c_45845,plain,(
    ! [B_1631] :
      ( k7_relat_1('#skF_6',B_1631) = k1_xboole_0
      | ~ r1_xboole_0(B_1631,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_45296])).

tff(c_45857,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_45845])).

tff(c_45864,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_45292,c_45857])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,A_20)),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_45884,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_45864,c_26])).

tff(c_45888,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_20,c_45884])).

tff(c_45904,plain,(
    ! [C_1634,B_1635,A_1636] :
      ( k7_relat_1(k7_relat_1(C_1634,B_1635),A_1636) = k7_relat_1(C_1634,A_1636)
      | ~ r1_tarski(A_1636,B_1635)
      | ~ v1_relat_1(C_1634) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45926,plain,(
    ! [A_1636] :
      ( k7_relat_1(k1_xboole_0,A_1636) = k7_relat_1('#skF_6',A_1636)
      | ~ r1_tarski(A_1636,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45864,c_45904])).

tff(c_46437,plain,(
    ! [A_1667] :
      ( k7_relat_1(k1_xboole_0,A_1667) = k7_relat_1('#skF_6',A_1667)
      | ~ r1_tarski(A_1667,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_45926])).

tff(c_46448,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_45888,c_46437])).

tff(c_46462,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7048,c_46448])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_82,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_44283,plain,(
    ! [A_1529,B_1530] :
      ( r1_xboole_0(A_1529,B_1530)
      | ~ r1_subset_1(A_1529,B_1530)
      | v1_xboole_0(B_1530)
      | v1_xboole_0(A_1529) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46575,plain,(
    ! [A_1679,B_1680] :
      ( k3_xboole_0(A_1679,B_1680) = k1_xboole_0
      | ~ r1_subset_1(A_1679,B_1680)
      | v1_xboole_0(B_1680)
      | v1_xboole_0(A_1679) ) ),
    inference(resolution,[status(thm)],[c_44283,c_2])).

tff(c_46581,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_46575])).

tff(c_46585,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_46581])).

tff(c_44387,plain,(
    ! [A_1539,B_1540,C_1541] :
      ( k9_subset_1(A_1539,B_1540,C_1541) = k3_xboole_0(B_1540,C_1541)
      | ~ m1_subset_1(C_1541,k1_zfmisc_1(A_1539)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44398,plain,(
    ! [B_1540] : k9_subset_1('#skF_2',B_1540,'#skF_5') = k3_xboole_0(B_1540,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_44387])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_7152,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_7145])).

tff(c_34,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | ~ r1_subset_1(A_25,B_26)
      | v1_xboole_0(B_26)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7161,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_7154])).

tff(c_44434,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7161,c_44428])).

tff(c_44440,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_44434])).

tff(c_45342,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44440])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_45740,plain,(
    ! [C_1625,A_1626,B_1627] :
      ( v1_partfun1(C_1625,A_1626)
      | ~ v1_funct_2(C_1625,A_1626,B_1627)
      | ~ v1_funct_1(C_1625)
      | ~ m1_subset_1(C_1625,k1_zfmisc_1(k2_zfmisc_1(A_1626,B_1627)))
      | v1_xboole_0(B_1627) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_45743,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_45740])).

tff(c_45749,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_45743])).

tff(c_45751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_45342,c_45749])).

tff(c_45752,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44440])).

tff(c_45758,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_7',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45752,c_16])).

tff(c_45799,plain,(
    ! [B_1628] :
      ( k7_relat_1('#skF_7',B_1628) = k1_xboole_0
      | ~ r1_xboole_0(B_1628,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_45758])).

tff(c_45803,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_7',A_25) = k1_xboole_0
      | ~ r1_subset_1(A_25,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_34,c_45799])).

tff(c_45865,plain,(
    ! [A_1632] :
      ( k7_relat_1('#skF_7',A_1632) = k1_xboole_0
      | ~ r1_subset_1(A_1632,'#skF_5')
      | v1_xboole_0(A_1632) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_45803])).

tff(c_45868,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_45865])).

tff(c_45871,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_45868])).

tff(c_45875,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_45871,c_26])).

tff(c_45879,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_20,c_45875])).

tff(c_45929,plain,(
    ! [A_1636] :
      ( k7_relat_1(k1_xboole_0,A_1636) = k7_relat_1('#skF_7',A_1636)
      | ~ r1_tarski(A_1636,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45871,c_45904])).

tff(c_46135,plain,(
    ! [A_1649] :
      ( k7_relat_1(k1_xboole_0,A_1649) = k7_relat_1('#skF_7',A_1649)
      | ~ r1_tarski(A_1649,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_45929])).

tff(c_46142,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_45879,c_46135])).

tff(c_46157,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7048,c_46142])).

tff(c_46356,plain,(
    ! [E_1657,B_1656,C_1661,F_1660,A_1659,D_1658] :
      ( v1_funct_1(k1_tmap_1(A_1659,B_1656,C_1661,D_1658,E_1657,F_1660))
      | ~ m1_subset_1(F_1660,k1_zfmisc_1(k2_zfmisc_1(D_1658,B_1656)))
      | ~ v1_funct_2(F_1660,D_1658,B_1656)
      | ~ v1_funct_1(F_1660)
      | ~ m1_subset_1(E_1657,k1_zfmisc_1(k2_zfmisc_1(C_1661,B_1656)))
      | ~ v1_funct_2(E_1657,C_1661,B_1656)
      | ~ v1_funct_1(E_1657)
      | ~ m1_subset_1(D_1658,k1_zfmisc_1(A_1659))
      | v1_xboole_0(D_1658)
      | ~ m1_subset_1(C_1661,k1_zfmisc_1(A_1659))
      | v1_xboole_0(C_1661)
      | v1_xboole_0(B_1656)
      | v1_xboole_0(A_1659) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_46358,plain,(
    ! [A_1659,C_1661,E_1657] :
      ( v1_funct_1(k1_tmap_1(A_1659,'#skF_3',C_1661,'#skF_5',E_1657,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1657,k1_zfmisc_1(k2_zfmisc_1(C_1661,'#skF_3')))
      | ~ v1_funct_2(E_1657,C_1661,'#skF_3')
      | ~ v1_funct_1(E_1657)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1659))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1661,k1_zfmisc_1(A_1659))
      | v1_xboole_0(C_1661)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1659) ) ),
    inference(resolution,[status(thm)],[c_70,c_46356])).

tff(c_46363,plain,(
    ! [A_1659,C_1661,E_1657] :
      ( v1_funct_1(k1_tmap_1(A_1659,'#skF_3',C_1661,'#skF_5',E_1657,'#skF_7'))
      | ~ m1_subset_1(E_1657,k1_zfmisc_1(k2_zfmisc_1(C_1661,'#skF_3')))
      | ~ v1_funct_2(E_1657,C_1661,'#skF_3')
      | ~ v1_funct_1(E_1657)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1659))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1661,k1_zfmisc_1(A_1659))
      | v1_xboole_0(C_1661)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_46358])).

tff(c_47228,plain,(
    ! [A_1709,C_1710,E_1711] :
      ( v1_funct_1(k1_tmap_1(A_1709,'#skF_3',C_1710,'#skF_5',E_1711,'#skF_7'))
      | ~ m1_subset_1(E_1711,k1_zfmisc_1(k2_zfmisc_1(C_1710,'#skF_3')))
      | ~ v1_funct_2(E_1711,C_1710,'#skF_3')
      | ~ v1_funct_1(E_1711)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1709))
      | ~ m1_subset_1(C_1710,k1_zfmisc_1(A_1709))
      | v1_xboole_0(C_1710)
      | v1_xboole_0(A_1709) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_46363])).

tff(c_47235,plain,(
    ! [A_1709] :
      ( v1_funct_1(k1_tmap_1(A_1709,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1709))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1709))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1709) ) ),
    inference(resolution,[status(thm)],[c_76,c_47228])).

tff(c_47245,plain,(
    ! [A_1709] :
      ( v1_funct_1(k1_tmap_1(A_1709,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1709))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1709))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1709) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_47235])).

tff(c_47688,plain,(
    ! [A_1732] :
      ( v1_funct_1(k1_tmap_1(A_1732,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1732))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1732))
      | v1_xboole_0(A_1732) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_47245])).

tff(c_47691,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_47688])).

tff(c_47694,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_47691])).

tff(c_47695,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_47694])).

tff(c_46104,plain,(
    ! [A_1642,B_1643,C_1644,D_1645] :
      ( k2_partfun1(A_1642,B_1643,C_1644,D_1645) = k7_relat_1(C_1644,D_1645)
      | ~ m1_subset_1(C_1644,k1_zfmisc_1(k2_zfmisc_1(A_1642,B_1643)))
      | ~ v1_funct_1(C_1644) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_46108,plain,(
    ! [D_1645] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_1645) = k7_relat_1('#skF_6',D_1645)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_46104])).

tff(c_46114,plain,(
    ! [D_1645] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_1645) = k7_relat_1('#skF_6',D_1645) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_46108])).

tff(c_46106,plain,(
    ! [D_1645] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1645) = k7_relat_1('#skF_7',D_1645)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_46104])).

tff(c_46111,plain,(
    ! [D_1645] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1645) = k7_relat_1('#skF_7',D_1645) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46106])).

tff(c_64,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_62,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_46976,plain,(
    ! [E_1702,F_1705,B_1704,D_1700,A_1701,C_1703] :
      ( k2_partfun1(k4_subset_1(A_1701,C_1703,D_1700),B_1704,k1_tmap_1(A_1701,B_1704,C_1703,D_1700,E_1702,F_1705),C_1703) = E_1702
      | ~ m1_subset_1(k1_tmap_1(A_1701,B_1704,C_1703,D_1700,E_1702,F_1705),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1701,C_1703,D_1700),B_1704)))
      | ~ v1_funct_2(k1_tmap_1(A_1701,B_1704,C_1703,D_1700,E_1702,F_1705),k4_subset_1(A_1701,C_1703,D_1700),B_1704)
      | ~ v1_funct_1(k1_tmap_1(A_1701,B_1704,C_1703,D_1700,E_1702,F_1705))
      | k2_partfun1(D_1700,B_1704,F_1705,k9_subset_1(A_1701,C_1703,D_1700)) != k2_partfun1(C_1703,B_1704,E_1702,k9_subset_1(A_1701,C_1703,D_1700))
      | ~ m1_subset_1(F_1705,k1_zfmisc_1(k2_zfmisc_1(D_1700,B_1704)))
      | ~ v1_funct_2(F_1705,D_1700,B_1704)
      | ~ v1_funct_1(F_1705)
      | ~ m1_subset_1(E_1702,k1_zfmisc_1(k2_zfmisc_1(C_1703,B_1704)))
      | ~ v1_funct_2(E_1702,C_1703,B_1704)
      | ~ v1_funct_1(E_1702)
      | ~ m1_subset_1(D_1700,k1_zfmisc_1(A_1701))
      | v1_xboole_0(D_1700)
      | ~ m1_subset_1(C_1703,k1_zfmisc_1(A_1701))
      | v1_xboole_0(C_1703)
      | v1_xboole_0(B_1704)
      | v1_xboole_0(A_1701) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_84527,plain,(
    ! [F_2321,A_2320,B_2317,E_2318,D_2319,C_2322] :
      ( k2_partfun1(k4_subset_1(A_2320,C_2322,D_2319),B_2317,k1_tmap_1(A_2320,B_2317,C_2322,D_2319,E_2318,F_2321),C_2322) = E_2318
      | ~ v1_funct_2(k1_tmap_1(A_2320,B_2317,C_2322,D_2319,E_2318,F_2321),k4_subset_1(A_2320,C_2322,D_2319),B_2317)
      | ~ v1_funct_1(k1_tmap_1(A_2320,B_2317,C_2322,D_2319,E_2318,F_2321))
      | k2_partfun1(D_2319,B_2317,F_2321,k9_subset_1(A_2320,C_2322,D_2319)) != k2_partfun1(C_2322,B_2317,E_2318,k9_subset_1(A_2320,C_2322,D_2319))
      | ~ m1_subset_1(F_2321,k1_zfmisc_1(k2_zfmisc_1(D_2319,B_2317)))
      | ~ v1_funct_2(F_2321,D_2319,B_2317)
      | ~ v1_funct_1(F_2321)
      | ~ m1_subset_1(E_2318,k1_zfmisc_1(k2_zfmisc_1(C_2322,B_2317)))
      | ~ v1_funct_2(E_2318,C_2322,B_2317)
      | ~ v1_funct_1(E_2318)
      | ~ m1_subset_1(D_2319,k1_zfmisc_1(A_2320))
      | v1_xboole_0(D_2319)
      | ~ m1_subset_1(C_2322,k1_zfmisc_1(A_2320))
      | v1_xboole_0(C_2322)
      | v1_xboole_0(B_2317)
      | v1_xboole_0(A_2320) ) ),
    inference(resolution,[status(thm)],[c_62,c_46976])).

tff(c_100309,plain,(
    ! [C_2511,B_2506,E_2507,A_2509,F_2510,D_2508] :
      ( k2_partfun1(k4_subset_1(A_2509,C_2511,D_2508),B_2506,k1_tmap_1(A_2509,B_2506,C_2511,D_2508,E_2507,F_2510),C_2511) = E_2507
      | ~ v1_funct_1(k1_tmap_1(A_2509,B_2506,C_2511,D_2508,E_2507,F_2510))
      | k2_partfun1(D_2508,B_2506,F_2510,k9_subset_1(A_2509,C_2511,D_2508)) != k2_partfun1(C_2511,B_2506,E_2507,k9_subset_1(A_2509,C_2511,D_2508))
      | ~ m1_subset_1(F_2510,k1_zfmisc_1(k2_zfmisc_1(D_2508,B_2506)))
      | ~ v1_funct_2(F_2510,D_2508,B_2506)
      | ~ v1_funct_1(F_2510)
      | ~ m1_subset_1(E_2507,k1_zfmisc_1(k2_zfmisc_1(C_2511,B_2506)))
      | ~ v1_funct_2(E_2507,C_2511,B_2506)
      | ~ v1_funct_1(E_2507)
      | ~ m1_subset_1(D_2508,k1_zfmisc_1(A_2509))
      | v1_xboole_0(D_2508)
      | ~ m1_subset_1(C_2511,k1_zfmisc_1(A_2509))
      | v1_xboole_0(C_2511)
      | v1_xboole_0(B_2506)
      | v1_xboole_0(A_2509) ) ),
    inference(resolution,[status(thm)],[c_64,c_84527])).

tff(c_100313,plain,(
    ! [A_2509,C_2511,E_2507] :
      ( k2_partfun1(k4_subset_1(A_2509,C_2511,'#skF_5'),'#skF_3',k1_tmap_1(A_2509,'#skF_3',C_2511,'#skF_5',E_2507,'#skF_7'),C_2511) = E_2507
      | ~ v1_funct_1(k1_tmap_1(A_2509,'#skF_3',C_2511,'#skF_5',E_2507,'#skF_7'))
      | k2_partfun1(C_2511,'#skF_3',E_2507,k9_subset_1(A_2509,C_2511,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_2509,C_2511,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2507,k1_zfmisc_1(k2_zfmisc_1(C_2511,'#skF_3')))
      | ~ v1_funct_2(E_2507,C_2511,'#skF_3')
      | ~ v1_funct_1(E_2507)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2509))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2511,k1_zfmisc_1(A_2509))
      | v1_xboole_0(C_2511)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2509) ) ),
    inference(resolution,[status(thm)],[c_70,c_100309])).

tff(c_100319,plain,(
    ! [A_2509,C_2511,E_2507] :
      ( k2_partfun1(k4_subset_1(A_2509,C_2511,'#skF_5'),'#skF_3',k1_tmap_1(A_2509,'#skF_3',C_2511,'#skF_5',E_2507,'#skF_7'),C_2511) = E_2507
      | ~ v1_funct_1(k1_tmap_1(A_2509,'#skF_3',C_2511,'#skF_5',E_2507,'#skF_7'))
      | k2_partfun1(C_2511,'#skF_3',E_2507,k9_subset_1(A_2509,C_2511,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2509,C_2511,'#skF_5'))
      | ~ m1_subset_1(E_2507,k1_zfmisc_1(k2_zfmisc_1(C_2511,'#skF_3')))
      | ~ v1_funct_2(E_2507,C_2511,'#skF_3')
      | ~ v1_funct_1(E_2507)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2509))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2511,k1_zfmisc_1(A_2509))
      | v1_xboole_0(C_2511)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_46111,c_100313])).

tff(c_100841,plain,(
    ! [A_2515,C_2516,E_2517] :
      ( k2_partfun1(k4_subset_1(A_2515,C_2516,'#skF_5'),'#skF_3',k1_tmap_1(A_2515,'#skF_3',C_2516,'#skF_5',E_2517,'#skF_7'),C_2516) = E_2517
      | ~ v1_funct_1(k1_tmap_1(A_2515,'#skF_3',C_2516,'#skF_5',E_2517,'#skF_7'))
      | k2_partfun1(C_2516,'#skF_3',E_2517,k9_subset_1(A_2515,C_2516,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2515,C_2516,'#skF_5'))
      | ~ m1_subset_1(E_2517,k1_zfmisc_1(k2_zfmisc_1(C_2516,'#skF_3')))
      | ~ v1_funct_2(E_2517,C_2516,'#skF_3')
      | ~ v1_funct_1(E_2517)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2515))
      | ~ m1_subset_1(C_2516,k1_zfmisc_1(A_2515))
      | v1_xboole_0(C_2516)
      | v1_xboole_0(A_2515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_100319])).

tff(c_100848,plain,(
    ! [A_2515] :
      ( k2_partfun1(k4_subset_1(A_2515,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2515,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2515,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_2515,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2515,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2515))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2515))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2515) ) ),
    inference(resolution,[status(thm)],[c_76,c_100841])).

tff(c_100858,plain,(
    ! [A_2515] :
      ( k2_partfun1(k4_subset_1(A_2515,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2515,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2515,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2515,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2515,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2515))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2515))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_46114,c_100848])).

tff(c_103572,plain,(
    ! [A_2551] :
      ( k2_partfun1(k4_subset_1(A_2551,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2551,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2551,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2551,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2551,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2551))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2551))
      | v1_xboole_0(A_2551) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_100858])).

tff(c_7343,plain,(
    ! [B_892,A_893] :
      ( k1_relat_1(B_892) = A_893
      | ~ v1_partfun1(B_892,A_893)
      | ~ v4_relat_1(B_892,A_893)
      | ~ v1_relat_1(B_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7346,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7162,c_7343])).

tff(c_7352,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_7346])).

tff(c_7356,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7352])).

tff(c_8180,plain,(
    ! [C_951,A_952,B_953] :
      ( v1_partfun1(C_951,A_952)
      | ~ v1_funct_2(C_951,A_952,B_953)
      | ~ v1_funct_1(C_951)
      | ~ m1_subset_1(C_951,k1_zfmisc_1(k2_zfmisc_1(A_952,B_953)))
      | v1_xboole_0(B_953) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8186,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_8180])).

tff(c_8193,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_8186])).

tff(c_8195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_7356,c_8193])).

tff(c_8196,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7352])).

tff(c_7192,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7177])).

tff(c_8198,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8196,c_7192])).

tff(c_8202,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8196,c_16])).

tff(c_8765,plain,(
    ! [B_988] :
      ( k7_relat_1('#skF_6',B_988) = k1_xboole_0
      | ~ r1_xboole_0(B_988,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_8202])).

tff(c_8777,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_8765])).

tff(c_8784,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8198,c_8777])).

tff(c_8791,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8784,c_26])).

tff(c_8797,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_20,c_8791])).

tff(c_8799,plain,(
    ! [C_989,B_990,A_991] :
      ( k7_relat_1(k7_relat_1(C_989,B_990),A_991) = k7_relat_1(C_989,A_991)
      | ~ r1_tarski(A_991,B_990)
      | ~ v1_relat_1(C_989) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8824,plain,(
    ! [A_991] :
      ( k7_relat_1(k1_xboole_0,A_991) = k7_relat_1('#skF_6',A_991)
      | ~ r1_tarski(A_991,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8784,c_8799])).

tff(c_9324,plain,(
    ! [A_1025] :
      ( k7_relat_1(k1_xboole_0,A_1025) = k7_relat_1('#skF_6',A_1025)
      | ~ r1_tarski(A_1025,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_8824])).

tff(c_9335,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8797,c_9324])).

tff(c_9349,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7048,c_9335])).

tff(c_7204,plain,(
    ! [A_878,B_879] :
      ( r1_xboole_0(A_878,B_879)
      | ~ r1_subset_1(A_878,B_879)
      | v1_xboole_0(B_879)
      | v1_xboole_0(A_878) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9615,plain,(
    ! [A_1046,B_1047] :
      ( k3_xboole_0(A_1046,B_1047) = k1_xboole_0
      | ~ r1_subset_1(A_1046,B_1047)
      | v1_xboole_0(B_1047)
      | v1_xboole_0(A_1046) ) ),
    inference(resolution,[status(thm)],[c_7204,c_2])).

tff(c_9621,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_9615])).

tff(c_9625,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_9621])).

tff(c_7349,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7161,c_7343])).

tff(c_7355,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_7349])).

tff(c_8228,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_7355])).

tff(c_8623,plain,(
    ! [C_979,A_980,B_981] :
      ( v1_partfun1(C_979,A_980)
      | ~ v1_funct_2(C_979,A_980,B_981)
      | ~ v1_funct_1(C_979)
      | ~ m1_subset_1(C_979,k1_zfmisc_1(k2_zfmisc_1(A_980,B_981)))
      | v1_xboole_0(B_981) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8626,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_8623])).

tff(c_8632,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_8626])).

tff(c_8634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_8228,c_8632])).

tff(c_8635,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7355])).

tff(c_8641,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_7',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8635,c_16])).

tff(c_8731,plain,(
    ! [B_987] :
      ( k7_relat_1('#skF_7',B_987) = k1_xboole_0
      | ~ r1_xboole_0(B_987,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_8641])).

tff(c_8735,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_7',A_25) = k1_xboole_0
      | ~ r1_subset_1(A_25,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_34,c_8731])).

tff(c_9067,plain,(
    ! [A_1009] :
      ( k7_relat_1('#skF_7',A_1009) = k1_xboole_0
      | ~ r1_subset_1(A_1009,'#skF_5')
      | v1_xboole_0(A_1009) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_8735])).

tff(c_9070,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_9067])).

tff(c_9073,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_9070])).

tff(c_9086,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_9073,c_26])).

tff(c_9098,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_20,c_9086])).

tff(c_14,plain,(
    ! [C_15,B_14,A_13] :
      ( k7_relat_1(k7_relat_1(C_15,B_14),A_13) = k7_relat_1(C_15,A_13)
      | ~ r1_tarski(A_13,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9080,plain,(
    ! [A_13] :
      ( k7_relat_1(k1_xboole_0,A_13) = k7_relat_1('#skF_7',A_13)
      | ~ r1_tarski(A_13,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9073,c_14])).

tff(c_9149,plain,(
    ! [A_1019] :
      ( k7_relat_1(k1_xboole_0,A_1019) = k7_relat_1('#skF_7',A_1019)
      | ~ r1_tarski(A_1019,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_9080])).

tff(c_9152,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9098,c_9149])).

tff(c_9173,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7048,c_9152])).

tff(c_8671,plain,(
    ! [A_982,B_983,C_984] :
      ( k9_subset_1(A_982,B_983,C_984) = k3_xboole_0(B_983,C_984)
      | ~ m1_subset_1(C_984,k1_zfmisc_1(A_982)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8682,plain,(
    ! [B_983] : k9_subset_1('#skF_2',B_983,'#skF_5') = k3_xboole_0(B_983,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_8671])).

tff(c_9136,plain,(
    ! [E_1014,C_1018,A_1016,F_1017,D_1015,B_1013] :
      ( v1_funct_1(k1_tmap_1(A_1016,B_1013,C_1018,D_1015,E_1014,F_1017))
      | ~ m1_subset_1(F_1017,k1_zfmisc_1(k2_zfmisc_1(D_1015,B_1013)))
      | ~ v1_funct_2(F_1017,D_1015,B_1013)
      | ~ v1_funct_1(F_1017)
      | ~ m1_subset_1(E_1014,k1_zfmisc_1(k2_zfmisc_1(C_1018,B_1013)))
      | ~ v1_funct_2(E_1014,C_1018,B_1013)
      | ~ v1_funct_1(E_1014)
      | ~ m1_subset_1(D_1015,k1_zfmisc_1(A_1016))
      | v1_xboole_0(D_1015)
      | ~ m1_subset_1(C_1018,k1_zfmisc_1(A_1016))
      | v1_xboole_0(C_1018)
      | v1_xboole_0(B_1013)
      | v1_xboole_0(A_1016) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_9138,plain,(
    ! [A_1016,C_1018,E_1014] :
      ( v1_funct_1(k1_tmap_1(A_1016,'#skF_3',C_1018,'#skF_5',E_1014,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1014,k1_zfmisc_1(k2_zfmisc_1(C_1018,'#skF_3')))
      | ~ v1_funct_2(E_1014,C_1018,'#skF_3')
      | ~ v1_funct_1(E_1014)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1016))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1018,k1_zfmisc_1(A_1016))
      | v1_xboole_0(C_1018)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1016) ) ),
    inference(resolution,[status(thm)],[c_70,c_9136])).

tff(c_9143,plain,(
    ! [A_1016,C_1018,E_1014] :
      ( v1_funct_1(k1_tmap_1(A_1016,'#skF_3',C_1018,'#skF_5',E_1014,'#skF_7'))
      | ~ m1_subset_1(E_1014,k1_zfmisc_1(k2_zfmisc_1(C_1018,'#skF_3')))
      | ~ v1_funct_2(E_1014,C_1018,'#skF_3')
      | ~ v1_funct_1(E_1014)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1016))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1018,k1_zfmisc_1(A_1016))
      | v1_xboole_0(C_1018)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1016) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_9138])).

tff(c_10346,plain,(
    ! [A_1075,C_1076,E_1077] :
      ( v1_funct_1(k1_tmap_1(A_1075,'#skF_3',C_1076,'#skF_5',E_1077,'#skF_7'))
      | ~ m1_subset_1(E_1077,k1_zfmisc_1(k2_zfmisc_1(C_1076,'#skF_3')))
      | ~ v1_funct_2(E_1077,C_1076,'#skF_3')
      | ~ v1_funct_1(E_1077)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1075))
      | ~ m1_subset_1(C_1076,k1_zfmisc_1(A_1075))
      | v1_xboole_0(C_1076)
      | v1_xboole_0(A_1075) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_9143])).

tff(c_10353,plain,(
    ! [A_1075] :
      ( v1_funct_1(k1_tmap_1(A_1075,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1075))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1075))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1075) ) ),
    inference(resolution,[status(thm)],[c_76,c_10346])).

tff(c_10363,plain,(
    ! [A_1075] :
      ( v1_funct_1(k1_tmap_1(A_1075,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1075))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1075))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1075) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_10353])).

tff(c_10915,plain,(
    ! [A_1096] :
      ( v1_funct_1(k1_tmap_1(A_1096,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1096))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1096))
      | v1_xboole_0(A_1096) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_10363])).

tff(c_10918,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_10915])).

tff(c_10921,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10918])).

tff(c_10922,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_10921])).

tff(c_8961,plain,(
    ! [A_996,B_997,C_998,D_999] :
      ( k2_partfun1(A_996,B_997,C_998,D_999) = k7_relat_1(C_998,D_999)
      | ~ m1_subset_1(C_998,k1_zfmisc_1(k2_zfmisc_1(A_996,B_997)))
      | ~ v1_funct_1(C_998) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8965,plain,(
    ! [D_999] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_999) = k7_relat_1('#skF_6',D_999)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_8961])).

tff(c_8971,plain,(
    ! [D_999] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_999) = k7_relat_1('#skF_6',D_999) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8965])).

tff(c_8963,plain,(
    ! [D_999] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_999) = k7_relat_1('#skF_7',D_999)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_8961])).

tff(c_8968,plain,(
    ! [D_999] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_999) = k7_relat_1('#skF_7',D_999) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8963])).

tff(c_9748,plain,(
    ! [B_1058,C_1057,E_1056,F_1059,A_1055,D_1054] :
      ( k2_partfun1(k4_subset_1(A_1055,C_1057,D_1054),B_1058,k1_tmap_1(A_1055,B_1058,C_1057,D_1054,E_1056,F_1059),D_1054) = F_1059
      | ~ m1_subset_1(k1_tmap_1(A_1055,B_1058,C_1057,D_1054,E_1056,F_1059),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1055,C_1057,D_1054),B_1058)))
      | ~ v1_funct_2(k1_tmap_1(A_1055,B_1058,C_1057,D_1054,E_1056,F_1059),k4_subset_1(A_1055,C_1057,D_1054),B_1058)
      | ~ v1_funct_1(k1_tmap_1(A_1055,B_1058,C_1057,D_1054,E_1056,F_1059))
      | k2_partfun1(D_1054,B_1058,F_1059,k9_subset_1(A_1055,C_1057,D_1054)) != k2_partfun1(C_1057,B_1058,E_1056,k9_subset_1(A_1055,C_1057,D_1054))
      | ~ m1_subset_1(F_1059,k1_zfmisc_1(k2_zfmisc_1(D_1054,B_1058)))
      | ~ v1_funct_2(F_1059,D_1054,B_1058)
      | ~ v1_funct_1(F_1059)
      | ~ m1_subset_1(E_1056,k1_zfmisc_1(k2_zfmisc_1(C_1057,B_1058)))
      | ~ v1_funct_2(E_1056,C_1057,B_1058)
      | ~ v1_funct_1(E_1056)
      | ~ m1_subset_1(D_1054,k1_zfmisc_1(A_1055))
      | v1_xboole_0(D_1054)
      | ~ m1_subset_1(C_1057,k1_zfmisc_1(A_1055))
      | v1_xboole_0(C_1057)
      | v1_xboole_0(B_1058)
      | v1_xboole_0(A_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_19969,plain,(
    ! [A_1269,D_1268,C_1271,E_1267,B_1266,F_1270] :
      ( k2_partfun1(k4_subset_1(A_1269,C_1271,D_1268),B_1266,k1_tmap_1(A_1269,B_1266,C_1271,D_1268,E_1267,F_1270),D_1268) = F_1270
      | ~ v1_funct_2(k1_tmap_1(A_1269,B_1266,C_1271,D_1268,E_1267,F_1270),k4_subset_1(A_1269,C_1271,D_1268),B_1266)
      | ~ v1_funct_1(k1_tmap_1(A_1269,B_1266,C_1271,D_1268,E_1267,F_1270))
      | k2_partfun1(D_1268,B_1266,F_1270,k9_subset_1(A_1269,C_1271,D_1268)) != k2_partfun1(C_1271,B_1266,E_1267,k9_subset_1(A_1269,C_1271,D_1268))
      | ~ m1_subset_1(F_1270,k1_zfmisc_1(k2_zfmisc_1(D_1268,B_1266)))
      | ~ v1_funct_2(F_1270,D_1268,B_1266)
      | ~ v1_funct_1(F_1270)
      | ~ m1_subset_1(E_1267,k1_zfmisc_1(k2_zfmisc_1(C_1271,B_1266)))
      | ~ v1_funct_2(E_1267,C_1271,B_1266)
      | ~ v1_funct_1(E_1267)
      | ~ m1_subset_1(D_1268,k1_zfmisc_1(A_1269))
      | v1_xboole_0(D_1268)
      | ~ m1_subset_1(C_1271,k1_zfmisc_1(A_1269))
      | v1_xboole_0(C_1271)
      | v1_xboole_0(B_1266)
      | v1_xboole_0(A_1269) ) ),
    inference(resolution,[status(thm)],[c_62,c_9748])).

tff(c_40125,plain,(
    ! [F_1489,A_1488,B_1485,E_1486,D_1487,C_1490] :
      ( k2_partfun1(k4_subset_1(A_1488,C_1490,D_1487),B_1485,k1_tmap_1(A_1488,B_1485,C_1490,D_1487,E_1486,F_1489),D_1487) = F_1489
      | ~ v1_funct_1(k1_tmap_1(A_1488,B_1485,C_1490,D_1487,E_1486,F_1489))
      | k2_partfun1(D_1487,B_1485,F_1489,k9_subset_1(A_1488,C_1490,D_1487)) != k2_partfun1(C_1490,B_1485,E_1486,k9_subset_1(A_1488,C_1490,D_1487))
      | ~ m1_subset_1(F_1489,k1_zfmisc_1(k2_zfmisc_1(D_1487,B_1485)))
      | ~ v1_funct_2(F_1489,D_1487,B_1485)
      | ~ v1_funct_1(F_1489)
      | ~ m1_subset_1(E_1486,k1_zfmisc_1(k2_zfmisc_1(C_1490,B_1485)))
      | ~ v1_funct_2(E_1486,C_1490,B_1485)
      | ~ v1_funct_1(E_1486)
      | ~ m1_subset_1(D_1487,k1_zfmisc_1(A_1488))
      | v1_xboole_0(D_1487)
      | ~ m1_subset_1(C_1490,k1_zfmisc_1(A_1488))
      | v1_xboole_0(C_1490)
      | v1_xboole_0(B_1485)
      | v1_xboole_0(A_1488) ) ),
    inference(resolution,[status(thm)],[c_64,c_19969])).

tff(c_40129,plain,(
    ! [A_1488,C_1490,E_1486] :
      ( k2_partfun1(k4_subset_1(A_1488,C_1490,'#skF_5'),'#skF_3',k1_tmap_1(A_1488,'#skF_3',C_1490,'#skF_5',E_1486,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1488,'#skF_3',C_1490,'#skF_5',E_1486,'#skF_7'))
      | k2_partfun1(C_1490,'#skF_3',E_1486,k9_subset_1(A_1488,C_1490,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1488,C_1490,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1486,k1_zfmisc_1(k2_zfmisc_1(C_1490,'#skF_3')))
      | ~ v1_funct_2(E_1486,C_1490,'#skF_3')
      | ~ v1_funct_1(E_1486)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1488))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1490,k1_zfmisc_1(A_1488))
      | v1_xboole_0(C_1490)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1488) ) ),
    inference(resolution,[status(thm)],[c_70,c_40125])).

tff(c_40135,plain,(
    ! [A_1488,C_1490,E_1486] :
      ( k2_partfun1(k4_subset_1(A_1488,C_1490,'#skF_5'),'#skF_3',k1_tmap_1(A_1488,'#skF_3',C_1490,'#skF_5',E_1486,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1488,'#skF_3',C_1490,'#skF_5',E_1486,'#skF_7'))
      | k2_partfun1(C_1490,'#skF_3',E_1486,k9_subset_1(A_1488,C_1490,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1488,C_1490,'#skF_5'))
      | ~ m1_subset_1(E_1486,k1_zfmisc_1(k2_zfmisc_1(C_1490,'#skF_3')))
      | ~ v1_funct_2(E_1486,C_1490,'#skF_3')
      | ~ v1_funct_1(E_1486)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1488))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1490,k1_zfmisc_1(A_1488))
      | v1_xboole_0(C_1490)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1488) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_8968,c_40129])).

tff(c_41118,plain,(
    ! [A_1496,C_1497,E_1498] :
      ( k2_partfun1(k4_subset_1(A_1496,C_1497,'#skF_5'),'#skF_3',k1_tmap_1(A_1496,'#skF_3',C_1497,'#skF_5',E_1498,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1496,'#skF_3',C_1497,'#skF_5',E_1498,'#skF_7'))
      | k2_partfun1(C_1497,'#skF_3',E_1498,k9_subset_1(A_1496,C_1497,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1496,C_1497,'#skF_5'))
      | ~ m1_subset_1(E_1498,k1_zfmisc_1(k2_zfmisc_1(C_1497,'#skF_3')))
      | ~ v1_funct_2(E_1498,C_1497,'#skF_3')
      | ~ v1_funct_1(E_1498)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1496))
      | ~ m1_subset_1(C_1497,k1_zfmisc_1(A_1496))
      | v1_xboole_0(C_1497)
      | v1_xboole_0(A_1496) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_40135])).

tff(c_41125,plain,(
    ! [A_1496] :
      ( k2_partfun1(k4_subset_1(A_1496,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1496,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1496,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1496,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1496,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1496))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1496))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1496) ) ),
    inference(resolution,[status(thm)],[c_76,c_41118])).

tff(c_41135,plain,(
    ! [A_1496] :
      ( k2_partfun1(k4_subset_1(A_1496,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1496,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1496,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1496,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1496,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1496))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1496))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_8971,c_41125])).

tff(c_44201,plain,(
    ! [A_1525] :
      ( k2_partfun1(k4_subset_1(A_1525,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1525,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1525,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1525,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1525,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1525))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1525))
      | v1_xboole_0(A_1525) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_41135])).

tff(c_635,plain,(
    ! [C_313,A_314,B_315] :
      ( v1_relat_1(C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_642,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_635])).

tff(c_661,plain,(
    ! [C_316,A_317,B_318] :
      ( v4_relat_1(C_316,A_317)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_317,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_668,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_661])).

tff(c_4357,plain,(
    ! [B_608,A_609] :
      ( k1_relat_1(B_608) = A_609
      | ~ v1_partfun1(B_608,A_609)
      | ~ v4_relat_1(B_608,A_609)
      | ~ v1_relat_1(B_608) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4366,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_668,c_4357])).

tff(c_4375,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_4366])).

tff(c_5442,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4375])).

tff(c_5832,plain,(
    ! [C_728,A_729,B_730] :
      ( v1_partfun1(C_728,A_729)
      | ~ v1_funct_2(C_728,A_729,B_730)
      | ~ v1_funct_1(C_728)
      | ~ m1_subset_1(C_728,k1_zfmisc_1(k2_zfmisc_1(A_729,B_730)))
      | v1_xboole_0(B_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5838,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_5832])).

tff(c_5845,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5838])).

tff(c_5847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5442,c_5845])).

tff(c_5848,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4375])).

tff(c_643,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_635])).

tff(c_168,plain,(
    ! [C_252,A_253,B_254] :
      ( v1_relat_1(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_176,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_168])).

tff(c_192,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_176,c_24])).

tff(c_213,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_119,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_255,plain,(
    ! [A_267,B_268] :
      ( k7_relat_1(A_267,B_268) = k1_xboole_0
      | ~ r1_xboole_0(B_268,k1_relat_1(A_267))
      | ~ v1_relat_1(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_447,plain,(
    ! [A_292] :
      ( k7_relat_1(A_292,'#skF_1'(k1_relat_1(A_292))) = k1_xboole_0
      | ~ v1_relat_1(A_292)
      | k1_relat_1(A_292) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_255])).

tff(c_287,plain,(
    ! [B_271,A_272] :
      ( k3_xboole_0(B_271,k2_zfmisc_1(A_272,k2_relat_1(B_271))) = k7_relat_1(B_271,A_272)
      | ~ v1_relat_1(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_293,plain,(
    ! [B_271,A_272] :
      ( v1_relat_1(k7_relat_1(B_271,A_272))
      | ~ v1_relat_1(B_271)
      | ~ v1_relat_1(B_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_12])).

tff(c_460,plain,(
    ! [A_292] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_292)
      | ~ v1_relat_1(A_292)
      | ~ v1_relat_1(A_292)
      | k1_relat_1(A_292) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_293])).

tff(c_510,plain,(
    ! [A_299] :
      ( ~ v1_relat_1(A_299)
      | ~ v1_relat_1(A_299)
      | ~ v1_relat_1(A_299)
      | k1_relat_1(A_299) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_460])).

tff(c_514,plain,
    ( ~ v1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_176,c_510])).

tff(c_522,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_514])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_522])).

tff(c_525,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_534,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_119])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_534])).

tff(c_542,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_669,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_661])).

tff(c_882,plain,(
    ! [B_344,A_345] :
      ( k1_relat_1(B_344) = A_345
      | ~ v1_partfun1(B_344,A_345)
      | ~ v4_relat_1(B_344,A_345)
      | ~ v1_relat_1(B_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_885,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_669,c_882])).

tff(c_891,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_885])).

tff(c_895,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_891])).

tff(c_1483,plain,(
    ! [C_389,A_390,B_391] :
      ( v1_partfun1(C_389,A_390)
      | ~ v1_funct_2(C_389,A_390,B_391)
      | ~ v1_funct_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391)))
      | v1_xboole_0(B_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1489,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1483])).

tff(c_1496,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1489])).

tff(c_1498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_895,c_1496])).

tff(c_1499,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_891])).

tff(c_658,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_643,c_24])).

tff(c_672,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_658])).

tff(c_1501,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_672])).

tff(c_1505,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1499,c_16])).

tff(c_1850,plain,(
    ! [B_412] :
      ( k7_relat_1('#skF_6',B_412) = k1_xboole_0
      | ~ r1_xboole_0(B_412,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_1505])).

tff(c_1862,plain,
    ( k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_1850])).

tff(c_1869,plain,(
    k7_relat_1('#skF_6','#skF_1'('#skF_4')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1501,c_1862])).

tff(c_1876,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_1'('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1869,c_26])).

tff(c_1882,plain,(
    r1_tarski(k1_xboole_0,'#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_20,c_1876])).

tff(c_1884,plain,(
    ! [C_413,B_414,A_415] :
      ( k7_relat_1(k7_relat_1(C_413,B_414),A_415) = k7_relat_1(C_413,A_415)
      | ~ r1_tarski(A_415,B_414)
      | ~ v1_relat_1(C_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1909,plain,(
    ! [A_415] :
      ( k7_relat_1(k1_xboole_0,A_415) = k7_relat_1('#skF_6',A_415)
      | ~ r1_tarski(A_415,'#skF_1'('#skF_4'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1869,c_1884])).

tff(c_2397,plain,(
    ! [A_447] :
      ( k7_relat_1(k1_xboole_0,A_447) = k7_relat_1('#skF_6',A_447)
      | ~ r1_tarski(A_447,'#skF_1'('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_1909])).

tff(c_2408,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1882,c_2397])).

tff(c_2422,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_2408])).

tff(c_693,plain,(
    ! [A_323,B_324] :
      ( r1_xboole_0(A_323,B_324)
      | ~ r1_subset_1(A_323,B_324)
      | v1_xboole_0(B_324)
      | v1_xboole_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2522,plain,(
    ! [A_457,B_458] :
      ( k3_xboole_0(A_457,B_458) = k1_xboole_0
      | ~ r1_subset_1(A_457,B_458)
      | v1_xboole_0(B_458)
      | v1_xboole_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_693,c_2])).

tff(c_2525,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2522])).

tff(c_2528,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_2525])).

tff(c_888,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_668,c_882])).

tff(c_894,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_888])).

tff(c_1547,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_894])).

tff(c_1790,plain,(
    ! [C_409,A_410,B_411] :
      ( v1_partfun1(C_409,A_410)
      | ~ v1_funct_2(C_409,A_410,B_411)
      | ~ v1_funct_1(C_409)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411)))
      | v1_xboole_0(B_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1793,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1790])).

tff(c_1799,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1793])).

tff(c_1801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1547,c_1799])).

tff(c_1802,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_894])).

tff(c_1808,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_7',B_18) = k1_xboole_0
      | ~ r1_xboole_0(B_18,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1802,c_16])).

tff(c_1946,plain,(
    ! [B_416] :
      ( k7_relat_1('#skF_7',B_416) = k1_xboole_0
      | ~ r1_xboole_0(B_416,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_1808])).

tff(c_1950,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_7',A_25) = k1_xboole_0
      | ~ r1_subset_1(A_25,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_34,c_1946])).

tff(c_2083,plain,(
    ! [A_425] :
      ( k7_relat_1('#skF_7',A_425) = k1_xboole_0
      | ~ r1_subset_1(A_425,'#skF_5')
      | v1_xboole_0(A_425) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1950])).

tff(c_2086,plain,
    ( k7_relat_1('#skF_7','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2083])).

tff(c_2089,plain,(
    k7_relat_1('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2086])).

tff(c_2102,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),'#skF_4')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_26])).

tff(c_2114,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_20,c_2102])).

tff(c_2096,plain,(
    ! [A_13] :
      ( k7_relat_1(k1_xboole_0,A_13) = k7_relat_1('#skF_7',A_13)
      | ~ r1_tarski(A_13,'#skF_4')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_14])).

tff(c_2203,plain,(
    ! [A_433] :
      ( k7_relat_1(k1_xboole_0,A_433) = k7_relat_1('#skF_7',A_433)
      | ~ r1_tarski(A_433,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_2096])).

tff(c_2210,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2114,c_2203])).

tff(c_2225,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_2210])).

tff(c_2072,plain,(
    ! [A_421,B_422,C_423,D_424] :
      ( k2_partfun1(A_421,B_422,C_423,D_424) = k7_relat_1(C_423,D_424)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_421,B_422)))
      | ~ v1_funct_1(C_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2076,plain,(
    ! [D_424] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_424) = k7_relat_1('#skF_6',D_424)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_2072])).

tff(c_2082,plain,(
    ! [D_424] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_424) = k7_relat_1('#skF_6',D_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2076])).

tff(c_2074,plain,(
    ! [D_424] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_424) = k7_relat_1('#skF_7',D_424)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_2072])).

tff(c_2079,plain,(
    ! [D_424] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_424) = k7_relat_1('#skF_7',D_424) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2074])).

tff(c_739,plain,(
    ! [A_330,B_331,C_332] :
      ( k9_subset_1(A_330,B_331,C_332) = k3_xboole_0(B_331,C_332)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(A_330)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_750,plain,(
    ! [B_331] : k9_subset_1('#skF_2',B_331,'#skF_5') = k3_xboole_0(B_331,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_739])).

tff(c_68,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_118,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_769,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_750,c_118])).

tff(c_2118,plain,(
    k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) != k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2079,c_769])).

tff(c_2954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_2528,c_2225,c_2528,c_2082,c_2118])).

tff(c_2955,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_658])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2971,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_2955,c_18])).

tff(c_22,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_659,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_643,c_22])).

tff(c_670,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_2958,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_670])).

tff(c_3002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2971,c_2958])).

tff(c_3003,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_3016,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_3003,c_20])).

tff(c_4363,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_669,c_4357])).

tff(c_4372,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_3016,c_4363])).

tff(c_4376,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4372])).

tff(c_5332,plain,(
    ! [C_686,A_687,B_688] :
      ( v1_partfun1(C_686,A_687)
      | ~ v1_funct_2(C_686,A_687,B_688)
      | ~ v1_funct_1(C_686)
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1(A_687,B_688)))
      | v1_xboole_0(B_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5338,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_5332])).

tff(c_5345,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_5338])).

tff(c_5347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4376,c_5345])).

tff(c_5348,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4372])).

tff(c_4233,plain,(
    ! [A_16,B_18] :
      ( k7_relat_1(A_16,B_18) = '#skF_6'
      | ~ r1_xboole_0(B_18,k1_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_16])).

tff(c_6267,plain,(
    ! [A_765,B_766] :
      ( k7_relat_1(A_765,B_766) = '#skF_4'
      | ~ r1_xboole_0(B_766,k1_relat_1(A_765))
      | ~ v1_relat_1(A_765) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5348,c_4233])).

tff(c_6278,plain,(
    ! [B_766] :
      ( k7_relat_1('#skF_7',B_766) = '#skF_4'
      | ~ r1_xboole_0(B_766,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5848,c_6267])).

tff(c_6293,plain,(
    ! [B_767] :
      ( k7_relat_1('#skF_7',B_767) = '#skF_4'
      | ~ r1_xboole_0(B_767,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_6278])).

tff(c_6305,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_7',A_25) = '#skF_4'
      | ~ r1_subset_1(A_25,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_34,c_6293])).

tff(c_6401,plain,(
    ! [A_772] :
      ( k7_relat_1('#skF_7',A_772) = '#skF_4'
      | ~ r1_subset_1(A_772,'#skF_5')
      | v1_xboole_0(A_772) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6305])).

tff(c_6404,plain,
    ( k7_relat_1('#skF_7','#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_6401])).

tff(c_6407,plain,(
    k7_relat_1('#skF_7','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_6404])).

tff(c_3011,plain,(
    k7_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_3003,c_3003,c_542])).

tff(c_5363,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5348,c_5348,c_5348,c_3011])).

tff(c_4278,plain,(
    ! [A_602,B_603] :
      ( r1_xboole_0(A_602,B_603)
      | ~ r1_subset_1(A_602,B_603)
      | v1_xboole_0(B_603)
      | v1_xboole_0(A_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3013,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_6'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_2])).

tff(c_4289,plain,(
    ! [A_602,B_603] :
      ( k3_xboole_0(A_602,B_603) = '#skF_6'
      | ~ r1_subset_1(A_602,B_603)
      | v1_xboole_0(B_603)
      | v1_xboole_0(A_602) ) ),
    inference(resolution,[status(thm)],[c_4278,c_3013])).

tff(c_6643,plain,(
    ! [A_797,B_798] :
      ( k3_xboole_0(A_797,B_798) = '#skF_4'
      | ~ r1_subset_1(A_797,B_798)
      | v1_xboole_0(B_798)
      | v1_xboole_0(A_797) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5348,c_4289])).

tff(c_6649,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_6643])).

tff(c_6653,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_6649])).

tff(c_5376,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5348,c_80])).

tff(c_5374,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5348,c_76])).

tff(c_6194,plain,(
    ! [A_756,B_757,C_758,D_759] :
      ( k2_partfun1(A_756,B_757,C_758,D_759) = k7_relat_1(C_758,D_759)
      | ~ m1_subset_1(C_758,k1_zfmisc_1(k2_zfmisc_1(A_756,B_757)))
      | ~ v1_funct_1(C_758) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6196,plain,(
    ! [D_759] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_4',D_759) = k7_relat_1('#skF_4',D_759)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5374,c_6194])).

tff(c_6201,plain,(
    ! [D_759] : k2_partfun1('#skF_4','#skF_3','#skF_4',D_759) = k7_relat_1('#skF_4',D_759) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5376,c_6196])).

tff(c_6198,plain,(
    ! [D_759] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_759) = k7_relat_1('#skF_7',D_759)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_6194])).

tff(c_6204,plain,(
    ! [D_759] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_759) = k7_relat_1('#skF_7',D_759) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6198])).

tff(c_5414,plain,(
    ! [A_689,B_690,C_691] :
      ( k9_subset_1(A_689,B_690,C_691) = k3_xboole_0(B_690,C_691)
      | ~ m1_subset_1(C_691,k1_zfmisc_1(A_689)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5422,plain,(
    ! [B_690] : k9_subset_1('#skF_2',B_690,'#skF_5') = k3_xboole_0(B_690,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_5414])).

tff(c_5373,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_4',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5348,c_118])).

tff(c_6232,plain,(
    k7_relat_1('#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k7_relat_1('#skF_4',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6201,c_6204,c_5422,c_5422,c_5373])).

tff(c_6654,plain,(
    k7_relat_1('#skF_7','#skF_4') != k7_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6653,c_6653,c_6232])).

tff(c_6657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6407,c_5363,c_6654])).

tff(c_6658,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_7191,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_6658])).

tff(c_44212,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44201,c_7191])).

tff(c_44226,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_9349,c_9625,c_9173,c_9625,c_8682,c_8682,c_10922,c_44212])).

tff(c_44228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_44226])).

tff(c_44229,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7177])).

tff(c_44245,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44229,c_44229,c_18])).

tff(c_7178,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7153,c_22])).

tff(c_7181,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7178])).

tff(c_44231,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44229,c_7181])).

tff(c_44268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44245,c_44231])).

tff(c_44269,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6658])).

tff(c_103584,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103572,c_44269])).

tff(c_103598,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_46462,c_46585,c_44398,c_46157,c_46585,c_44398,c_47695,c_103584])).

tff(c_103600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_103598])).

tff(c_103601,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7177])).

tff(c_103603,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103601,c_7181])).

tff(c_103617,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103601,c_103601,c_18])).

tff(c_103634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103603,c_103617])).

tff(c_103635,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7178])).

tff(c_103658,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103635,c_103635,c_20])).

tff(c_137662,plain,(
    ! [B_3388,A_3389] :
      ( k1_relat_1(B_3388) = A_3389
      | ~ v1_partfun1(B_3388,A_3389)
      | ~ v4_relat_1(B_3388,A_3389)
      | ~ v1_relat_1(B_3388) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_137668,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7162,c_137662])).

tff(c_137677,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_103658,c_137668])).

tff(c_137681,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_137677])).

tff(c_138375,plain,(
    ! [C_3444,A_3445,B_3446] :
      ( v1_partfun1(C_3444,A_3445)
      | ~ v1_funct_2(C_3444,A_3445,B_3446)
      | ~ v1_funct_1(C_3444)
      | ~ m1_subset_1(C_3444,k1_zfmisc_1(k2_zfmisc_1(A_3445,B_3446)))
      | v1_xboole_0(B_3446) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_138381,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_138375])).

tff(c_138388,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_138381])).

tff(c_138390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_137681,c_138388])).

tff(c_138391,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_137677])).

tff(c_103654,plain,(
    k7_relat_1('#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103635,c_103635,c_103635,c_7048])).

tff(c_138411,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138391,c_138391,c_138391,c_103654])).

tff(c_103653,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = '#skF_6'
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103635,c_2])).

tff(c_138890,plain,(
    ! [A_3486,B_3487] :
      ( k3_xboole_0(A_3486,B_3487) = '#skF_4'
      | ~ r1_xboole_0(A_3486,B_3487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138391,c_103653])).

tff(c_139586,plain,(
    ! [A_3552,B_3553] :
      ( k3_xboole_0(A_3552,B_3553) = '#skF_4'
      | ~ r1_subset_1(A_3552,B_3553)
      | v1_xboole_0(B_3553)
      | v1_xboole_0(A_3552) ) ),
    inference(resolution,[status(thm)],[c_34,c_138890])).

tff(c_139592,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_139586])).

tff(c_139596,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_139592])).

tff(c_137671,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7161,c_137662])).

tff(c_137680,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_137671])).

tff(c_138584,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_137680])).

tff(c_138728,plain,(
    ! [C_3473,A_3474,B_3475] :
      ( v1_partfun1(C_3473,A_3474)
      | ~ v1_funct_2(C_3473,A_3474,B_3475)
      | ~ v1_funct_1(C_3473)
      | ~ m1_subset_1(C_3473,k1_zfmisc_1(k2_zfmisc_1(A_3474,B_3475)))
      | v1_xboole_0(B_3475) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_138734,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_138728])).

tff(c_138741,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_138734])).

tff(c_138743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_138584,c_138741])).

tff(c_138744,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_137680])).

tff(c_136115,plain,(
    ! [A_16,B_18] :
      ( k7_relat_1(A_16,B_18) = '#skF_6'
      | ~ r1_xboole_0(B_18,k1_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103635,c_16])).

tff(c_139083,plain,(
    ! [A_3509,B_3510] :
      ( k7_relat_1(A_3509,B_3510) = '#skF_4'
      | ~ r1_xboole_0(B_3510,k1_relat_1(A_3509))
      | ~ v1_relat_1(A_3509) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138391,c_136115])).

tff(c_139094,plain,(
    ! [B_3510] :
      ( k7_relat_1('#skF_7',B_3510) = '#skF_4'
      | ~ r1_xboole_0(B_3510,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138744,c_139083])).

tff(c_139122,plain,(
    ! [B_3514] :
      ( k7_relat_1('#skF_7',B_3514) = '#skF_4'
      | ~ r1_xboole_0(B_3514,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_139094])).

tff(c_139134,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_7',A_25) = '#skF_4'
      | ~ r1_subset_1(A_25,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_34,c_139122])).

tff(c_139213,plain,(
    ! [A_3522] :
      ( k7_relat_1('#skF_7',A_3522) = '#skF_4'
      | ~ r1_subset_1(A_3522,'#skF_5')
      | v1_xboole_0(A_3522) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_139134])).

tff(c_139216,plain,
    ( k7_relat_1('#skF_7','#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_139213])).

tff(c_139219,plain,(
    k7_relat_1('#skF_7','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_139216])).

tff(c_138465,plain,(
    ! [A_3447,B_3448,C_3449] :
      ( k9_subset_1(A_3447,B_3448,C_3449) = k3_xboole_0(B_3448,C_3449)
      | ~ m1_subset_1(C_3449,k1_zfmisc_1(A_3447)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138473,plain,(
    ! [B_3448] : k9_subset_1('#skF_2',B_3448,'#skF_5') = k3_xboole_0(B_3448,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_138465])).

tff(c_138425,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138391,c_80])).

tff(c_138424,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138391,c_78])).

tff(c_138423,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138391,c_76])).

tff(c_139070,plain,(
    ! [A_3506,E_3504,C_3508,B_3503,D_3505,F_3507] :
      ( v1_funct_1(k1_tmap_1(A_3506,B_3503,C_3508,D_3505,E_3504,F_3507))
      | ~ m1_subset_1(F_3507,k1_zfmisc_1(k2_zfmisc_1(D_3505,B_3503)))
      | ~ v1_funct_2(F_3507,D_3505,B_3503)
      | ~ v1_funct_1(F_3507)
      | ~ m1_subset_1(E_3504,k1_zfmisc_1(k2_zfmisc_1(C_3508,B_3503)))
      | ~ v1_funct_2(E_3504,C_3508,B_3503)
      | ~ v1_funct_1(E_3504)
      | ~ m1_subset_1(D_3505,k1_zfmisc_1(A_3506))
      | v1_xboole_0(D_3505)
      | ~ m1_subset_1(C_3508,k1_zfmisc_1(A_3506))
      | v1_xboole_0(C_3508)
      | v1_xboole_0(B_3503)
      | v1_xboole_0(A_3506) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_139074,plain,(
    ! [A_3506,C_3508,E_3504] :
      ( v1_funct_1(k1_tmap_1(A_3506,'#skF_3',C_3508,'#skF_5',E_3504,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3504,k1_zfmisc_1(k2_zfmisc_1(C_3508,'#skF_3')))
      | ~ v1_funct_2(E_3504,C_3508,'#skF_3')
      | ~ v1_funct_1(E_3504)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3506))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3508,k1_zfmisc_1(A_3506))
      | v1_xboole_0(C_3508)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3506) ) ),
    inference(resolution,[status(thm)],[c_70,c_139070])).

tff(c_139081,plain,(
    ! [A_3506,C_3508,E_3504] :
      ( v1_funct_1(k1_tmap_1(A_3506,'#skF_3',C_3508,'#skF_5',E_3504,'#skF_7'))
      | ~ m1_subset_1(E_3504,k1_zfmisc_1(k2_zfmisc_1(C_3508,'#skF_3')))
      | ~ v1_funct_2(E_3504,C_3508,'#skF_3')
      | ~ v1_funct_1(E_3504)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3506))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3508,k1_zfmisc_1(A_3506))
      | v1_xboole_0(C_3508)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3506) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_139074])).

tff(c_139109,plain,(
    ! [A_3511,C_3512,E_3513] :
      ( v1_funct_1(k1_tmap_1(A_3511,'#skF_3',C_3512,'#skF_5',E_3513,'#skF_7'))
      | ~ m1_subset_1(E_3513,k1_zfmisc_1(k2_zfmisc_1(C_3512,'#skF_3')))
      | ~ v1_funct_2(E_3513,C_3512,'#skF_3')
      | ~ v1_funct_1(E_3513)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3511))
      | ~ m1_subset_1(C_3512,k1_zfmisc_1(A_3511))
      | v1_xboole_0(C_3512)
      | v1_xboole_0(A_3511) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_139081])).

tff(c_139111,plain,(
    ! [A_3511] :
      ( v1_funct_1(k1_tmap_1(A_3511,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3511))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3511))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3511) ) ),
    inference(resolution,[status(thm)],[c_138423,c_139109])).

tff(c_139116,plain,(
    ! [A_3511] :
      ( v1_funct_1(k1_tmap_1(A_3511,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3511))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3511))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138425,c_138424,c_139111])).

tff(c_139578,plain,(
    ! [A_3551] :
      ( v1_funct_1(k1_tmap_1(A_3551,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3551))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3551))
      | v1_xboole_0(A_3551) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_139116])).

tff(c_139581,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_139578])).

tff(c_139584,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_139581])).

tff(c_139585,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_139584])).

tff(c_138807,plain,(
    ! [A_3478,B_3479,C_3480,D_3481] :
      ( k2_partfun1(A_3478,B_3479,C_3480,D_3481) = k7_relat_1(C_3480,D_3481)
      | ~ m1_subset_1(C_3480,k1_zfmisc_1(k2_zfmisc_1(A_3478,B_3479)))
      | ~ v1_funct_1(C_3480) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_138809,plain,(
    ! [D_3481] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_4',D_3481) = k7_relat_1('#skF_4',D_3481)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_138423,c_138807])).

tff(c_138814,plain,(
    ! [D_3481] : k2_partfun1('#skF_4','#skF_3','#skF_4',D_3481) = k7_relat_1('#skF_4',D_3481) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138425,c_138809])).

tff(c_138811,plain,(
    ! [D_3481] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_3481) = k7_relat_1('#skF_7',D_3481)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_138807])).

tff(c_138817,plain,(
    ! [D_3481] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_3481) = k7_relat_1('#skF_7',D_3481) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_138811])).

tff(c_139617,plain,(
    ! [E_3556,D_3554,F_3559,B_3558,A_3555,C_3557] :
      ( k2_partfun1(k4_subset_1(A_3555,C_3557,D_3554),B_3558,k1_tmap_1(A_3555,B_3558,C_3557,D_3554,E_3556,F_3559),C_3557) = E_3556
      | ~ m1_subset_1(k1_tmap_1(A_3555,B_3558,C_3557,D_3554,E_3556,F_3559),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3555,C_3557,D_3554),B_3558)))
      | ~ v1_funct_2(k1_tmap_1(A_3555,B_3558,C_3557,D_3554,E_3556,F_3559),k4_subset_1(A_3555,C_3557,D_3554),B_3558)
      | ~ v1_funct_1(k1_tmap_1(A_3555,B_3558,C_3557,D_3554,E_3556,F_3559))
      | k2_partfun1(D_3554,B_3558,F_3559,k9_subset_1(A_3555,C_3557,D_3554)) != k2_partfun1(C_3557,B_3558,E_3556,k9_subset_1(A_3555,C_3557,D_3554))
      | ~ m1_subset_1(F_3559,k1_zfmisc_1(k2_zfmisc_1(D_3554,B_3558)))
      | ~ v1_funct_2(F_3559,D_3554,B_3558)
      | ~ v1_funct_1(F_3559)
      | ~ m1_subset_1(E_3556,k1_zfmisc_1(k2_zfmisc_1(C_3557,B_3558)))
      | ~ v1_funct_2(E_3556,C_3557,B_3558)
      | ~ v1_funct_1(E_3556)
      | ~ m1_subset_1(D_3554,k1_zfmisc_1(A_3555))
      | v1_xboole_0(D_3554)
      | ~ m1_subset_1(C_3557,k1_zfmisc_1(A_3555))
      | v1_xboole_0(C_3557)
      | v1_xboole_0(B_3558)
      | v1_xboole_0(A_3555) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_146287,plain,(
    ! [B_3731,A_3734,F_3735,D_3733,C_3736,E_3732] :
      ( k2_partfun1(k4_subset_1(A_3734,C_3736,D_3733),B_3731,k1_tmap_1(A_3734,B_3731,C_3736,D_3733,E_3732,F_3735),C_3736) = E_3732
      | ~ v1_funct_2(k1_tmap_1(A_3734,B_3731,C_3736,D_3733,E_3732,F_3735),k4_subset_1(A_3734,C_3736,D_3733),B_3731)
      | ~ v1_funct_1(k1_tmap_1(A_3734,B_3731,C_3736,D_3733,E_3732,F_3735))
      | k2_partfun1(D_3733,B_3731,F_3735,k9_subset_1(A_3734,C_3736,D_3733)) != k2_partfun1(C_3736,B_3731,E_3732,k9_subset_1(A_3734,C_3736,D_3733))
      | ~ m1_subset_1(F_3735,k1_zfmisc_1(k2_zfmisc_1(D_3733,B_3731)))
      | ~ v1_funct_2(F_3735,D_3733,B_3731)
      | ~ v1_funct_1(F_3735)
      | ~ m1_subset_1(E_3732,k1_zfmisc_1(k2_zfmisc_1(C_3736,B_3731)))
      | ~ v1_funct_2(E_3732,C_3736,B_3731)
      | ~ v1_funct_1(E_3732)
      | ~ m1_subset_1(D_3733,k1_zfmisc_1(A_3734))
      | v1_xboole_0(D_3733)
      | ~ m1_subset_1(C_3736,k1_zfmisc_1(A_3734))
      | v1_xboole_0(C_3736)
      | v1_xboole_0(B_3731)
      | v1_xboole_0(A_3734) ) ),
    inference(resolution,[status(thm)],[c_62,c_139617])).

tff(c_155574,plain,(
    ! [B_3880,D_3882,A_3883,E_3881,F_3884,C_3885] :
      ( k2_partfun1(k4_subset_1(A_3883,C_3885,D_3882),B_3880,k1_tmap_1(A_3883,B_3880,C_3885,D_3882,E_3881,F_3884),C_3885) = E_3881
      | ~ v1_funct_1(k1_tmap_1(A_3883,B_3880,C_3885,D_3882,E_3881,F_3884))
      | k2_partfun1(D_3882,B_3880,F_3884,k9_subset_1(A_3883,C_3885,D_3882)) != k2_partfun1(C_3885,B_3880,E_3881,k9_subset_1(A_3883,C_3885,D_3882))
      | ~ m1_subset_1(F_3884,k1_zfmisc_1(k2_zfmisc_1(D_3882,B_3880)))
      | ~ v1_funct_2(F_3884,D_3882,B_3880)
      | ~ v1_funct_1(F_3884)
      | ~ m1_subset_1(E_3881,k1_zfmisc_1(k2_zfmisc_1(C_3885,B_3880)))
      | ~ v1_funct_2(E_3881,C_3885,B_3880)
      | ~ v1_funct_1(E_3881)
      | ~ m1_subset_1(D_3882,k1_zfmisc_1(A_3883))
      | v1_xboole_0(D_3882)
      | ~ m1_subset_1(C_3885,k1_zfmisc_1(A_3883))
      | v1_xboole_0(C_3885)
      | v1_xboole_0(B_3880)
      | v1_xboole_0(A_3883) ) ),
    inference(resolution,[status(thm)],[c_64,c_146287])).

tff(c_155580,plain,(
    ! [A_3883,C_3885,E_3881] :
      ( k2_partfun1(k4_subset_1(A_3883,C_3885,'#skF_5'),'#skF_3',k1_tmap_1(A_3883,'#skF_3',C_3885,'#skF_5',E_3881,'#skF_7'),C_3885) = E_3881
      | ~ v1_funct_1(k1_tmap_1(A_3883,'#skF_3',C_3885,'#skF_5',E_3881,'#skF_7'))
      | k2_partfun1(C_3885,'#skF_3',E_3881,k9_subset_1(A_3883,C_3885,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_3883,C_3885,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3881,k1_zfmisc_1(k2_zfmisc_1(C_3885,'#skF_3')))
      | ~ v1_funct_2(E_3881,C_3885,'#skF_3')
      | ~ v1_funct_1(E_3881)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3883))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3885,k1_zfmisc_1(A_3883))
      | v1_xboole_0(C_3885)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3883) ) ),
    inference(resolution,[status(thm)],[c_70,c_155574])).

tff(c_155588,plain,(
    ! [A_3883,C_3885,E_3881] :
      ( k2_partfun1(k4_subset_1(A_3883,C_3885,'#skF_5'),'#skF_3',k1_tmap_1(A_3883,'#skF_3',C_3885,'#skF_5',E_3881,'#skF_7'),C_3885) = E_3881
      | ~ v1_funct_1(k1_tmap_1(A_3883,'#skF_3',C_3885,'#skF_5',E_3881,'#skF_7'))
      | k2_partfun1(C_3885,'#skF_3',E_3881,k9_subset_1(A_3883,C_3885,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3883,C_3885,'#skF_5'))
      | ~ m1_subset_1(E_3881,k1_zfmisc_1(k2_zfmisc_1(C_3885,'#skF_3')))
      | ~ v1_funct_2(E_3881,C_3885,'#skF_3')
      | ~ v1_funct_1(E_3881)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3883))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3885,k1_zfmisc_1(A_3883))
      | v1_xboole_0(C_3885)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3883) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_138817,c_155580])).

tff(c_167544,plain,(
    ! [A_3988,C_3989,E_3990] :
      ( k2_partfun1(k4_subset_1(A_3988,C_3989,'#skF_5'),'#skF_3',k1_tmap_1(A_3988,'#skF_3',C_3989,'#skF_5',E_3990,'#skF_7'),C_3989) = E_3990
      | ~ v1_funct_1(k1_tmap_1(A_3988,'#skF_3',C_3989,'#skF_5',E_3990,'#skF_7'))
      | k2_partfun1(C_3989,'#skF_3',E_3990,k9_subset_1(A_3988,C_3989,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3988,C_3989,'#skF_5'))
      | ~ m1_subset_1(E_3990,k1_zfmisc_1(k2_zfmisc_1(C_3989,'#skF_3')))
      | ~ v1_funct_2(E_3990,C_3989,'#skF_3')
      | ~ v1_funct_1(E_3990)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3988))
      | ~ m1_subset_1(C_3989,k1_zfmisc_1(A_3988))
      | v1_xboole_0(C_3989)
      | v1_xboole_0(A_3988) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_155588])).

tff(c_167549,plain,(
    ! [A_3988] :
      ( k2_partfun1(k4_subset_1(A_3988,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3988,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') = '#skF_4'
      | ~ v1_funct_1(k1_tmap_1(A_3988,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_4',k9_subset_1(A_3988,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3988,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3988))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3988))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3988) ) ),
    inference(resolution,[status(thm)],[c_138423,c_167544])).

tff(c_167557,plain,(
    ! [A_3988] :
      ( k2_partfun1(k4_subset_1(A_3988,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3988,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') = '#skF_4'
      | ~ v1_funct_1(k1_tmap_1(A_3988,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_3988,'#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1(A_3988,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3988))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3988))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3988) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138425,c_138424,c_138814,c_167549])).

tff(c_168734,plain,(
    ! [A_3998] :
      ( k2_partfun1(k4_subset_1(A_3998,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3998,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') = '#skF_4'
      | ~ v1_funct_1(k1_tmap_1(A_3998,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_3998,'#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1(A_3998,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3998))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3998))
      | v1_xboole_0(A_3998) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_167557])).

tff(c_104772,plain,(
    ! [B_2648,A_2649] :
      ( k1_relat_1(B_2648) = A_2649
      | ~ v1_partfun1(B_2648,A_2649)
      | ~ v4_relat_1(B_2648,A_2649)
      | ~ v1_relat_1(B_2648) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_104778,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7162,c_104772])).

tff(c_104787,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_103658,c_104778])).

tff(c_104791,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_104787])).

tff(c_105714,plain,(
    ! [C_2714,A_2715,B_2716] :
      ( v1_partfun1(C_2714,A_2715)
      | ~ v1_funct_2(C_2714,A_2715,B_2716)
      | ~ v1_funct_1(C_2714)
      | ~ m1_subset_1(C_2714,k1_zfmisc_1(k2_zfmisc_1(A_2715,B_2716)))
      | v1_xboole_0(B_2716) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_105720,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_105714])).

tff(c_105727,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_105720])).

tff(c_105729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_104791,c_105727])).

tff(c_105730,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_104787])).

tff(c_105749,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105730,c_105730,c_105730,c_103654])).

tff(c_104645,plain,(
    ! [A_2638,B_2639] :
      ( r1_xboole_0(A_2638,B_2639)
      | ~ r1_subset_1(A_2638,B_2639)
      | v1_xboole_0(B_2639)
      | v1_xboole_0(A_2638) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_104662,plain,(
    ! [A_2638,B_2639] :
      ( k3_xboole_0(A_2638,B_2639) = '#skF_6'
      | ~ r1_subset_1(A_2638,B_2639)
      | v1_xboole_0(B_2639)
      | v1_xboole_0(A_2638) ) ),
    inference(resolution,[status(thm)],[c_104645,c_103653])).

tff(c_106853,plain,(
    ! [A_2823,B_2824] :
      ( k3_xboole_0(A_2823,B_2824) = '#skF_4'
      | ~ r1_subset_1(A_2823,B_2824)
      | v1_xboole_0(B_2824)
      | v1_xboole_0(A_2823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105730,c_104662])).

tff(c_106862,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_106853])).

tff(c_106867,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_106862])).

tff(c_104781,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7161,c_104772])).

tff(c_104790,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_104781])).

tff(c_105926,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_104790])).

tff(c_106081,plain,(
    ! [C_2744,A_2745,B_2746] :
      ( v1_partfun1(C_2744,A_2745)
      | ~ v1_funct_2(C_2744,A_2745,B_2746)
      | ~ v1_funct_1(C_2744)
      | ~ m1_subset_1(C_2744,k1_zfmisc_1(k2_zfmisc_1(A_2745,B_2746)))
      | v1_xboole_0(B_2746) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_106087,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_106081])).

tff(c_106094,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_106087])).

tff(c_106096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_105926,c_106094])).

tff(c_106097,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_104790])).

tff(c_103681,plain,(
    ! [A_16,B_18] :
      ( k7_relat_1(A_16,B_18) = '#skF_6'
      | ~ r1_xboole_0(B_18,k1_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103635,c_16])).

tff(c_106433,plain,(
    ! [A_2779,B_2780] :
      ( k7_relat_1(A_2779,B_2780) = '#skF_4'
      | ~ r1_xboole_0(B_2780,k1_relat_1(A_2779))
      | ~ v1_relat_1(A_2779) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105730,c_103681])).

tff(c_106440,plain,(
    ! [B_2780] :
      ( k7_relat_1('#skF_7',B_2780) = '#skF_4'
      | ~ r1_xboole_0(B_2780,'#skF_5')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106097,c_106433])).

tff(c_106472,plain,(
    ! [B_2784] :
      ( k7_relat_1('#skF_7',B_2784) = '#skF_4'
      | ~ r1_xboole_0(B_2784,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7152,c_106440])).

tff(c_106484,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_7',A_25) = '#skF_4'
      | ~ r1_subset_1(A_25,'#skF_5')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_34,c_106472])).

tff(c_106563,plain,(
    ! [A_2792] :
      ( k7_relat_1('#skF_7',A_2792) = '#skF_4'
      | ~ r1_subset_1(A_2792,'#skF_5')
      | v1_xboole_0(A_2792) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_106484])).

tff(c_106566,plain,
    ( k7_relat_1('#skF_7','#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_106563])).

tff(c_106569,plain,(
    k7_relat_1('#skF_7','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_106566])).

tff(c_105788,plain,(
    ! [A_2717,B_2718,C_2719] :
      ( k9_subset_1(A_2717,B_2718,C_2719) = k3_xboole_0(B_2718,C_2719)
      | ~ m1_subset_1(C_2719,k1_zfmisc_1(A_2717)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105796,plain,(
    ! [B_2718] : k9_subset_1('#skF_2',B_2718,'#skF_5') = k3_xboole_0(B_2718,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_105788])).

tff(c_105763,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105730,c_80])).

tff(c_105762,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105730,c_78])).

tff(c_105761,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105730,c_76])).

tff(c_106403,plain,(
    ! [C_2777,D_2774,F_2776,A_2775,B_2772,E_2773] :
      ( v1_funct_1(k1_tmap_1(A_2775,B_2772,C_2777,D_2774,E_2773,F_2776))
      | ~ m1_subset_1(F_2776,k1_zfmisc_1(k2_zfmisc_1(D_2774,B_2772)))
      | ~ v1_funct_2(F_2776,D_2774,B_2772)
      | ~ v1_funct_1(F_2776)
      | ~ m1_subset_1(E_2773,k1_zfmisc_1(k2_zfmisc_1(C_2777,B_2772)))
      | ~ v1_funct_2(E_2773,C_2777,B_2772)
      | ~ v1_funct_1(E_2773)
      | ~ m1_subset_1(D_2774,k1_zfmisc_1(A_2775))
      | v1_xboole_0(D_2774)
      | ~ m1_subset_1(C_2777,k1_zfmisc_1(A_2775))
      | v1_xboole_0(C_2777)
      | v1_xboole_0(B_2772)
      | v1_xboole_0(A_2775) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_106407,plain,(
    ! [A_2775,C_2777,E_2773] :
      ( v1_funct_1(k1_tmap_1(A_2775,'#skF_3',C_2777,'#skF_5',E_2773,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2773,k1_zfmisc_1(k2_zfmisc_1(C_2777,'#skF_3')))
      | ~ v1_funct_2(E_2773,C_2777,'#skF_3')
      | ~ v1_funct_1(E_2773)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2775))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2777,k1_zfmisc_1(A_2775))
      | v1_xboole_0(C_2777)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2775) ) ),
    inference(resolution,[status(thm)],[c_70,c_106403])).

tff(c_106414,plain,(
    ! [A_2775,C_2777,E_2773] :
      ( v1_funct_1(k1_tmap_1(A_2775,'#skF_3',C_2777,'#skF_5',E_2773,'#skF_7'))
      | ~ m1_subset_1(E_2773,k1_zfmisc_1(k2_zfmisc_1(C_2777,'#skF_3')))
      | ~ v1_funct_2(E_2773,C_2777,'#skF_3')
      | ~ v1_funct_1(E_2773)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2775))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2777,k1_zfmisc_1(A_2775))
      | v1_xboole_0(C_2777)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2775) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_106407])).

tff(c_106459,plain,(
    ! [A_2781,C_2782,E_2783] :
      ( v1_funct_1(k1_tmap_1(A_2781,'#skF_3',C_2782,'#skF_5',E_2783,'#skF_7'))
      | ~ m1_subset_1(E_2783,k1_zfmisc_1(k2_zfmisc_1(C_2782,'#skF_3')))
      | ~ v1_funct_2(E_2783,C_2782,'#skF_3')
      | ~ v1_funct_1(E_2783)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2781))
      | ~ m1_subset_1(C_2782,k1_zfmisc_1(A_2781))
      | v1_xboole_0(C_2782)
      | v1_xboole_0(A_2781) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_106414])).

tff(c_106461,plain,(
    ! [A_2781] :
      ( v1_funct_1(k1_tmap_1(A_2781,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2781))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2781))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2781) ) ),
    inference(resolution,[status(thm)],[c_105761,c_106459])).

tff(c_106466,plain,(
    ! [A_2781] :
      ( v1_funct_1(k1_tmap_1(A_2781,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2781))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2781))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2781) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105763,c_105762,c_106461])).

tff(c_106844,plain,(
    ! [A_2822] :
      ( v1_funct_1(k1_tmap_1(A_2822,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2822))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2822))
      | v1_xboole_0(A_2822) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_106466])).

tff(c_106847,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_106844])).

tff(c_106850,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_106847])).

tff(c_106851,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_106850])).

tff(c_106157,plain,(
    ! [A_2748,B_2749,C_2750,D_2751] :
      ( k2_partfun1(A_2748,B_2749,C_2750,D_2751) = k7_relat_1(C_2750,D_2751)
      | ~ m1_subset_1(C_2750,k1_zfmisc_1(k2_zfmisc_1(A_2748,B_2749)))
      | ~ v1_funct_1(C_2750) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_106159,plain,(
    ! [D_2751] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_4',D_2751) = k7_relat_1('#skF_4',D_2751)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_105761,c_106157])).

tff(c_106164,plain,(
    ! [D_2751] : k2_partfun1('#skF_4','#skF_3','#skF_4',D_2751) = k7_relat_1('#skF_4',D_2751) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105763,c_106159])).

tff(c_106161,plain,(
    ! [D_2751] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_2751) = k7_relat_1('#skF_7',D_2751)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_106157])).

tff(c_106167,plain,(
    ! [D_2751] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_2751) = k7_relat_1('#skF_7',D_2751) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_106161])).

tff(c_106887,plain,(
    ! [A_2826,F_2830,D_2825,E_2827,B_2829,C_2828] :
      ( k2_partfun1(k4_subset_1(A_2826,C_2828,D_2825),B_2829,k1_tmap_1(A_2826,B_2829,C_2828,D_2825,E_2827,F_2830),D_2825) = F_2830
      | ~ m1_subset_1(k1_tmap_1(A_2826,B_2829,C_2828,D_2825,E_2827,F_2830),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2826,C_2828,D_2825),B_2829)))
      | ~ v1_funct_2(k1_tmap_1(A_2826,B_2829,C_2828,D_2825,E_2827,F_2830),k4_subset_1(A_2826,C_2828,D_2825),B_2829)
      | ~ v1_funct_1(k1_tmap_1(A_2826,B_2829,C_2828,D_2825,E_2827,F_2830))
      | k2_partfun1(D_2825,B_2829,F_2830,k9_subset_1(A_2826,C_2828,D_2825)) != k2_partfun1(C_2828,B_2829,E_2827,k9_subset_1(A_2826,C_2828,D_2825))
      | ~ m1_subset_1(F_2830,k1_zfmisc_1(k2_zfmisc_1(D_2825,B_2829)))
      | ~ v1_funct_2(F_2830,D_2825,B_2829)
      | ~ v1_funct_1(F_2830)
      | ~ m1_subset_1(E_2827,k1_zfmisc_1(k2_zfmisc_1(C_2828,B_2829)))
      | ~ v1_funct_2(E_2827,C_2828,B_2829)
      | ~ v1_funct_1(E_2827)
      | ~ m1_subset_1(D_2825,k1_zfmisc_1(A_2826))
      | v1_xboole_0(D_2825)
      | ~ m1_subset_1(C_2828,k1_zfmisc_1(A_2826))
      | v1_xboole_0(C_2828)
      | v1_xboole_0(B_2829)
      | v1_xboole_0(A_2826) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_114699,plain,(
    ! [A_3018,E_3016,B_3015,C_3020,F_3019,D_3017] :
      ( k2_partfun1(k4_subset_1(A_3018,C_3020,D_3017),B_3015,k1_tmap_1(A_3018,B_3015,C_3020,D_3017,E_3016,F_3019),D_3017) = F_3019
      | ~ v1_funct_2(k1_tmap_1(A_3018,B_3015,C_3020,D_3017,E_3016,F_3019),k4_subset_1(A_3018,C_3020,D_3017),B_3015)
      | ~ v1_funct_1(k1_tmap_1(A_3018,B_3015,C_3020,D_3017,E_3016,F_3019))
      | k2_partfun1(D_3017,B_3015,F_3019,k9_subset_1(A_3018,C_3020,D_3017)) != k2_partfun1(C_3020,B_3015,E_3016,k9_subset_1(A_3018,C_3020,D_3017))
      | ~ m1_subset_1(F_3019,k1_zfmisc_1(k2_zfmisc_1(D_3017,B_3015)))
      | ~ v1_funct_2(F_3019,D_3017,B_3015)
      | ~ v1_funct_1(F_3019)
      | ~ m1_subset_1(E_3016,k1_zfmisc_1(k2_zfmisc_1(C_3020,B_3015)))
      | ~ v1_funct_2(E_3016,C_3020,B_3015)
      | ~ v1_funct_1(E_3016)
      | ~ m1_subset_1(D_3017,k1_zfmisc_1(A_3018))
      | v1_xboole_0(D_3017)
      | ~ m1_subset_1(C_3020,k1_zfmisc_1(A_3018))
      | v1_xboole_0(C_3020)
      | v1_xboole_0(B_3015)
      | v1_xboole_0(A_3018) ) ),
    inference(resolution,[status(thm)],[c_62,c_106887])).

tff(c_123683,plain,(
    ! [A_3168,C_3170,F_3169,D_3167,B_3165,E_3166] :
      ( k2_partfun1(k4_subset_1(A_3168,C_3170,D_3167),B_3165,k1_tmap_1(A_3168,B_3165,C_3170,D_3167,E_3166,F_3169),D_3167) = F_3169
      | ~ v1_funct_1(k1_tmap_1(A_3168,B_3165,C_3170,D_3167,E_3166,F_3169))
      | k2_partfun1(D_3167,B_3165,F_3169,k9_subset_1(A_3168,C_3170,D_3167)) != k2_partfun1(C_3170,B_3165,E_3166,k9_subset_1(A_3168,C_3170,D_3167))
      | ~ m1_subset_1(F_3169,k1_zfmisc_1(k2_zfmisc_1(D_3167,B_3165)))
      | ~ v1_funct_2(F_3169,D_3167,B_3165)
      | ~ v1_funct_1(F_3169)
      | ~ m1_subset_1(E_3166,k1_zfmisc_1(k2_zfmisc_1(C_3170,B_3165)))
      | ~ v1_funct_2(E_3166,C_3170,B_3165)
      | ~ v1_funct_1(E_3166)
      | ~ m1_subset_1(D_3167,k1_zfmisc_1(A_3168))
      | v1_xboole_0(D_3167)
      | ~ m1_subset_1(C_3170,k1_zfmisc_1(A_3168))
      | v1_xboole_0(C_3170)
      | v1_xboole_0(B_3165)
      | v1_xboole_0(A_3168) ) ),
    inference(resolution,[status(thm)],[c_64,c_114699])).

tff(c_123689,plain,(
    ! [A_3168,C_3170,E_3166] :
      ( k2_partfun1(k4_subset_1(A_3168,C_3170,'#skF_5'),'#skF_3',k1_tmap_1(A_3168,'#skF_3',C_3170,'#skF_5',E_3166,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3168,'#skF_3',C_3170,'#skF_5',E_3166,'#skF_7'))
      | k2_partfun1(C_3170,'#skF_3',E_3166,k9_subset_1(A_3168,C_3170,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_3168,C_3170,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_3166,k1_zfmisc_1(k2_zfmisc_1(C_3170,'#skF_3')))
      | ~ v1_funct_2(E_3166,C_3170,'#skF_3')
      | ~ v1_funct_1(E_3166)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3168))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3170,k1_zfmisc_1(A_3168))
      | v1_xboole_0(C_3170)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3168) ) ),
    inference(resolution,[status(thm)],[c_70,c_123683])).

tff(c_123697,plain,(
    ! [A_3168,C_3170,E_3166] :
      ( k2_partfun1(k4_subset_1(A_3168,C_3170,'#skF_5'),'#skF_3',k1_tmap_1(A_3168,'#skF_3',C_3170,'#skF_5',E_3166,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3168,'#skF_3',C_3170,'#skF_5',E_3166,'#skF_7'))
      | k2_partfun1(C_3170,'#skF_3',E_3166,k9_subset_1(A_3168,C_3170,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3168,C_3170,'#skF_5'))
      | ~ m1_subset_1(E_3166,k1_zfmisc_1(k2_zfmisc_1(C_3170,'#skF_3')))
      | ~ v1_funct_2(E_3166,C_3170,'#skF_3')
      | ~ v1_funct_1(E_3166)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3168))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_3170,k1_zfmisc_1(A_3168))
      | v1_xboole_0(C_3170)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_106167,c_123689])).

tff(c_134880,plain,(
    ! [A_3257,C_3258,E_3259] :
      ( k2_partfun1(k4_subset_1(A_3257,C_3258,'#skF_5'),'#skF_3',k1_tmap_1(A_3257,'#skF_3',C_3258,'#skF_5',E_3259,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3257,'#skF_3',C_3258,'#skF_5',E_3259,'#skF_7'))
      | k2_partfun1(C_3258,'#skF_3',E_3259,k9_subset_1(A_3257,C_3258,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3257,C_3258,'#skF_5'))
      | ~ m1_subset_1(E_3259,k1_zfmisc_1(k2_zfmisc_1(C_3258,'#skF_3')))
      | ~ v1_funct_2(E_3259,C_3258,'#skF_3')
      | ~ v1_funct_1(E_3259)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3257))
      | ~ m1_subset_1(C_3258,k1_zfmisc_1(A_3257))
      | v1_xboole_0(C_3258)
      | v1_xboole_0(A_3257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_123697])).

tff(c_134885,plain,(
    ! [A_3257] :
      ( k2_partfun1(k4_subset_1(A_3257,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3257,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3257,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_4',k9_subset_1(A_3257,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_3257,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_4','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3257))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3257))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3257) ) ),
    inference(resolution,[status(thm)],[c_105761,c_134880])).

tff(c_134893,plain,(
    ! [A_3257] :
      ( k2_partfun1(k4_subset_1(A_3257,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3257,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3257,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_3257,'#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1(A_3257,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3257))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3257))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_3257) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105763,c_105762,c_106164,c_134885])).

tff(c_136073,plain,(
    ! [A_3267] :
      ( k2_partfun1(k4_subset_1(A_3267,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_3267,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_3267,'#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_3267,'#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1(A_3267,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_3267))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3267))
      | v1_xboole_0(A_3267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_134893])).

tff(c_103665,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_6658])).

tff(c_105740,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105730,c_103665])).

tff(c_136082,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_136073,c_105740])).

tff(c_136095,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_105749,c_106867,c_106569,c_106867,c_105796,c_105796,c_106851,c_136082])).

tff(c_136097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_136095])).

tff(c_136098,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6658])).

tff(c_138395,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138391,c_138391,c_136098])).

tff(c_168743,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_4','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_4',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_168734,c_138395])).

tff(c_168754,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_138411,c_139596,c_139219,c_139596,c_138473,c_138473,c_139585,c_168743])).

tff(c_168756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_168754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:47:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.88/20.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.03/20.16  
% 30.03/20.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.03/20.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 30.03/20.16  
% 30.03/20.16  %Foreground sorts:
% 30.03/20.16  
% 30.03/20.16  
% 30.03/20.16  %Background operators:
% 30.03/20.16  
% 30.03/20.16  
% 30.03/20.16  %Foreground operators:
% 30.03/20.16  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 30.03/20.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 30.03/20.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.03/20.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.03/20.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 30.03/20.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 30.03/20.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.03/20.16  tff('#skF_7', type, '#skF_7': $i).
% 30.03/20.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.03/20.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.03/20.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 30.03/20.16  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 30.03/20.16  tff('#skF_5', type, '#skF_5': $i).
% 30.03/20.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 30.03/20.16  tff('#skF_6', type, '#skF_6': $i).
% 30.03/20.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 30.03/20.16  tff('#skF_2', type, '#skF_2': $i).
% 30.03/20.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 30.03/20.16  tff('#skF_3', type, '#skF_3': $i).
% 30.03/20.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 30.03/20.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.03/20.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.03/20.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.03/20.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 30.03/20.16  tff('#skF_4', type, '#skF_4': $i).
% 30.03/20.16  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 30.03/20.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.03/20.16  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 30.03/20.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 30.03/20.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 30.03/20.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 30.03/20.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.03/20.16  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 30.03/20.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.03/20.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 30.03/20.16  
% 30.48/20.21  tff(f_264, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 30.48/20.21  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 30.48/20.21  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 30.48/20.21  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 30.48/20.21  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 30.48/20.21  tff(f_112, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 30.48/20.21  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 30.48/20.21  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 30.48/20.21  tff(f_46, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 30.48/20.21  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 30.48/20.21  tff(f_134, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 30.48/20.21  tff(f_126, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 30.48/20.21  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 30.48/20.21  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 30.48/20.21  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 30.48/20.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 30.48/20.21  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 30.48/20.21  tff(f_222, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 30.48/20.21  tff(f_140, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 30.48/20.21  tff(f_188, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 30.48/20.21  tff(c_94, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_92, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_7145, plain, (![C_868, A_869, B_870]: (v1_relat_1(C_868) | ~m1_subset_1(C_868, k1_zfmisc_1(k2_zfmisc_1(A_869, B_870))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 30.48/20.21  tff(c_7153, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_7145])).
% 30.48/20.21  tff(c_6734, plain, (![C_813, A_814, B_815]: (v1_relat_1(C_813) | ~m1_subset_1(C_813, k1_zfmisc_1(k2_zfmisc_1(A_814, B_815))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 30.48/20.21  tff(c_6742, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_6734])).
% 30.48/20.21  tff(c_24, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 30.48/20.21  tff(c_6766, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6742, c_24])).
% 30.48/20.21  tff(c_6781, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6766])).
% 30.48/20.21  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 30.48/20.21  tff(c_106, plain, (![A_239]: (k7_relat_1(A_239, k1_relat_1(A_239))=A_239 | ~v1_relat_1(A_239))), inference(cnfTransformation, [status(thm)], [f_82])).
% 30.48/20.21  tff(c_115, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_106])).
% 30.48/20.21  tff(c_6660, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_115])).
% 30.48/20.21  tff(c_42, plain, (![A_33]: (r1_xboole_0('#skF_1'(A_33), A_33) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_112])).
% 30.48/20.21  tff(c_6801, plain, (![A_826, B_827]: (k7_relat_1(A_826, B_827)=k1_xboole_0 | ~r1_xboole_0(B_827, k1_relat_1(A_826)) | ~v1_relat_1(A_826))), inference(cnfTransformation, [status(thm)], [f_59])).
% 30.48/20.21  tff(c_6949, plain, (![A_850]: (k7_relat_1(A_850, '#skF_1'(k1_relat_1(A_850)))=k1_xboole_0 | ~v1_relat_1(A_850) | k1_relat_1(A_850)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_6801])).
% 30.48/20.21  tff(c_6897, plain, (![B_839, A_840]: (k3_xboole_0(B_839, k2_zfmisc_1(A_840, k2_relat_1(B_839)))=k7_relat_1(B_839, A_840) | ~v1_relat_1(B_839))), inference(cnfTransformation, [status(thm)], [f_78])).
% 30.48/20.21  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k3_xboole_0(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 30.48/20.21  tff(c_6903, plain, (![B_839, A_840]: (v1_relat_1(k7_relat_1(B_839, A_840)) | ~v1_relat_1(B_839) | ~v1_relat_1(B_839))), inference(superposition, [status(thm), theory('equality')], [c_6897, c_12])).
% 30.48/20.21  tff(c_6955, plain, (![A_850]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_850) | ~v1_relat_1(A_850) | ~v1_relat_1(A_850) | k1_relat_1(A_850)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6949, c_6903])).
% 30.48/20.21  tff(c_7014, plain, (![A_854]: (~v1_relat_1(A_854) | ~v1_relat_1(A_854) | ~v1_relat_1(A_854) | k1_relat_1(A_854)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_6660, c_6955])).
% 30.48/20.21  tff(c_7018, plain, (~v1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_6742, c_7014])).
% 30.48/20.21  tff(c_7026, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_7018])).
% 30.48/20.21  tff(c_7028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6781, c_7026])).
% 30.48/20.21  tff(c_7029, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_6766])).
% 30.48/20.21  tff(c_7040, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7029, c_6660])).
% 30.48/20.21  tff(c_7047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6742, c_7040])).
% 30.48/20.21  tff(c_7048, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_115])).
% 30.48/20.21  tff(c_7154, plain, (![C_871, A_872, B_873]: (v4_relat_1(C_871, A_872) | ~m1_subset_1(C_871, k1_zfmisc_1(k2_zfmisc_1(A_872, B_873))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 30.48/20.21  tff(c_7162, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_7154])).
% 30.48/20.21  tff(c_44428, plain, (![B_1545, A_1546]: (k1_relat_1(B_1545)=A_1546 | ~v1_partfun1(B_1545, A_1546) | ~v4_relat_1(B_1545, A_1546) | ~v1_relat_1(B_1545))), inference(cnfTransformation, [status(thm)], [f_134])).
% 30.48/20.21  tff(c_44431, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7162, c_44428])).
% 30.48/20.21  tff(c_44437, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_44431])).
% 30.48/20.21  tff(c_44441, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_44437])).
% 30.48/20.21  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_45274, plain, (![C_1598, A_1599, B_1600]: (v1_partfun1(C_1598, A_1599) | ~v1_funct_2(C_1598, A_1599, B_1600) | ~v1_funct_1(C_1598) | ~m1_subset_1(C_1598, k1_zfmisc_1(k2_zfmisc_1(A_1599, B_1600))) | v1_xboole_0(B_1600))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.21  tff(c_45280, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_45274])).
% 30.48/20.21  tff(c_45287, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_45280])).
% 30.48/20.21  tff(c_45289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_44441, c_45287])).
% 30.48/20.21  tff(c_45290, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_44437])).
% 30.48/20.21  tff(c_7177, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_7153, c_24])).
% 30.48/20.21  tff(c_44271, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7177])).
% 30.48/20.21  tff(c_45292, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45290, c_44271])).
% 30.48/20.21  tff(c_16, plain, (![A_16, B_18]: (k7_relat_1(A_16, B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, k1_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 30.48/20.21  tff(c_45296, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_45290, c_16])).
% 30.48/20.21  tff(c_45845, plain, (![B_1631]: (k7_relat_1('#skF_6', B_1631)=k1_xboole_0 | ~r1_xboole_0(B_1631, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_45296])).
% 30.48/20.21  tff(c_45857, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_45845])).
% 30.48/20.21  tff(c_45864, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_45292, c_45857])).
% 30.48/20.21  tff(c_26, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, A_20)), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 30.48/20.21  tff(c_45884, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_45864, c_26])).
% 30.48/20.21  tff(c_45888, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_20, c_45884])).
% 30.48/20.21  tff(c_45904, plain, (![C_1634, B_1635, A_1636]: (k7_relat_1(k7_relat_1(C_1634, B_1635), A_1636)=k7_relat_1(C_1634, A_1636) | ~r1_tarski(A_1636, B_1635) | ~v1_relat_1(C_1634))), inference(cnfTransformation, [status(thm)], [f_52])).
% 30.48/20.21  tff(c_45926, plain, (![A_1636]: (k7_relat_1(k1_xboole_0, A_1636)=k7_relat_1('#skF_6', A_1636) | ~r1_tarski(A_1636, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_45864, c_45904])).
% 30.48/20.21  tff(c_46437, plain, (![A_1667]: (k7_relat_1(k1_xboole_0, A_1667)=k7_relat_1('#skF_6', A_1667) | ~r1_tarski(A_1667, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_45926])).
% 30.48/20.21  tff(c_46448, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_45888, c_46437])).
% 30.48/20.21  tff(c_46462, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7048, c_46448])).
% 30.48/20.21  tff(c_90, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_86, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_82, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_44283, plain, (![A_1529, B_1530]: (r1_xboole_0(A_1529, B_1530) | ~r1_subset_1(A_1529, B_1530) | v1_xboole_0(B_1530) | v1_xboole_0(A_1529))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.48/20.21  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 30.48/20.21  tff(c_46575, plain, (![A_1679, B_1680]: (k3_xboole_0(A_1679, B_1680)=k1_xboole_0 | ~r1_subset_1(A_1679, B_1680) | v1_xboole_0(B_1680) | v1_xboole_0(A_1679))), inference(resolution, [status(thm)], [c_44283, c_2])).
% 30.48/20.21  tff(c_46581, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_46575])).
% 30.48/20.21  tff(c_46585, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_46581])).
% 30.48/20.21  tff(c_44387, plain, (![A_1539, B_1540, C_1541]: (k9_subset_1(A_1539, B_1540, C_1541)=k3_xboole_0(B_1540, C_1541) | ~m1_subset_1(C_1541, k1_zfmisc_1(A_1539)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.48/20.21  tff(c_44398, plain, (![B_1540]: (k9_subset_1('#skF_2', B_1540, '#skF_5')=k3_xboole_0(B_1540, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_44387])).
% 30.48/20.21  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_7152, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_7145])).
% 30.48/20.21  tff(c_34, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | ~r1_subset_1(A_25, B_26) | v1_xboole_0(B_26) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.48/20.21  tff(c_7161, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_7154])).
% 30.48/20.21  tff(c_44434, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7161, c_44428])).
% 30.48/20.21  tff(c_44440, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_44434])).
% 30.48/20.21  tff(c_45342, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_44440])).
% 30.48/20.21  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_45740, plain, (![C_1625, A_1626, B_1627]: (v1_partfun1(C_1625, A_1626) | ~v1_funct_2(C_1625, A_1626, B_1627) | ~v1_funct_1(C_1625) | ~m1_subset_1(C_1625, k1_zfmisc_1(k2_zfmisc_1(A_1626, B_1627))) | v1_xboole_0(B_1627))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.21  tff(c_45743, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_45740])).
% 30.48/20.21  tff(c_45749, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_45743])).
% 30.48/20.21  tff(c_45751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_45342, c_45749])).
% 30.48/20.21  tff(c_45752, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_44440])).
% 30.48/20.21  tff(c_45758, plain, (![B_18]: (k7_relat_1('#skF_7', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_45752, c_16])).
% 30.48/20.21  tff(c_45799, plain, (![B_1628]: (k7_relat_1('#skF_7', B_1628)=k1_xboole_0 | ~r1_xboole_0(B_1628, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_45758])).
% 30.48/20.21  tff(c_45803, plain, (![A_25]: (k7_relat_1('#skF_7', A_25)=k1_xboole_0 | ~r1_subset_1(A_25, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_34, c_45799])).
% 30.48/20.21  tff(c_45865, plain, (![A_1632]: (k7_relat_1('#skF_7', A_1632)=k1_xboole_0 | ~r1_subset_1(A_1632, '#skF_5') | v1_xboole_0(A_1632))), inference(negUnitSimplification, [status(thm)], [c_86, c_45803])).
% 30.48/20.21  tff(c_45868, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_45865])).
% 30.48/20.21  tff(c_45871, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_45868])).
% 30.48/20.21  tff(c_45875, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_45871, c_26])).
% 30.48/20.21  tff(c_45879, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_20, c_45875])).
% 30.48/20.21  tff(c_45929, plain, (![A_1636]: (k7_relat_1(k1_xboole_0, A_1636)=k7_relat_1('#skF_7', A_1636) | ~r1_tarski(A_1636, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_45871, c_45904])).
% 30.48/20.21  tff(c_46135, plain, (![A_1649]: (k7_relat_1(k1_xboole_0, A_1649)=k7_relat_1('#skF_7', A_1649) | ~r1_tarski(A_1649, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_45929])).
% 30.48/20.21  tff(c_46142, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_45879, c_46135])).
% 30.48/20.21  tff(c_46157, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7048, c_46142])).
% 30.48/20.21  tff(c_46356, plain, (![E_1657, B_1656, C_1661, F_1660, A_1659, D_1658]: (v1_funct_1(k1_tmap_1(A_1659, B_1656, C_1661, D_1658, E_1657, F_1660)) | ~m1_subset_1(F_1660, k1_zfmisc_1(k2_zfmisc_1(D_1658, B_1656))) | ~v1_funct_2(F_1660, D_1658, B_1656) | ~v1_funct_1(F_1660) | ~m1_subset_1(E_1657, k1_zfmisc_1(k2_zfmisc_1(C_1661, B_1656))) | ~v1_funct_2(E_1657, C_1661, B_1656) | ~v1_funct_1(E_1657) | ~m1_subset_1(D_1658, k1_zfmisc_1(A_1659)) | v1_xboole_0(D_1658) | ~m1_subset_1(C_1661, k1_zfmisc_1(A_1659)) | v1_xboole_0(C_1661) | v1_xboole_0(B_1656) | v1_xboole_0(A_1659))), inference(cnfTransformation, [status(thm)], [f_222])).
% 30.48/20.21  tff(c_46358, plain, (![A_1659, C_1661, E_1657]: (v1_funct_1(k1_tmap_1(A_1659, '#skF_3', C_1661, '#skF_5', E_1657, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1657, k1_zfmisc_1(k2_zfmisc_1(C_1661, '#skF_3'))) | ~v1_funct_2(E_1657, C_1661, '#skF_3') | ~v1_funct_1(E_1657) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1659)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1661, k1_zfmisc_1(A_1659)) | v1_xboole_0(C_1661) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1659))), inference(resolution, [status(thm)], [c_70, c_46356])).
% 30.48/20.21  tff(c_46363, plain, (![A_1659, C_1661, E_1657]: (v1_funct_1(k1_tmap_1(A_1659, '#skF_3', C_1661, '#skF_5', E_1657, '#skF_7')) | ~m1_subset_1(E_1657, k1_zfmisc_1(k2_zfmisc_1(C_1661, '#skF_3'))) | ~v1_funct_2(E_1657, C_1661, '#skF_3') | ~v1_funct_1(E_1657) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1659)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1661, k1_zfmisc_1(A_1659)) | v1_xboole_0(C_1661) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1659))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_46358])).
% 30.48/20.21  tff(c_47228, plain, (![A_1709, C_1710, E_1711]: (v1_funct_1(k1_tmap_1(A_1709, '#skF_3', C_1710, '#skF_5', E_1711, '#skF_7')) | ~m1_subset_1(E_1711, k1_zfmisc_1(k2_zfmisc_1(C_1710, '#skF_3'))) | ~v1_funct_2(E_1711, C_1710, '#skF_3') | ~v1_funct_1(E_1711) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1709)) | ~m1_subset_1(C_1710, k1_zfmisc_1(A_1709)) | v1_xboole_0(C_1710) | v1_xboole_0(A_1709))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_46363])).
% 30.48/20.21  tff(c_47235, plain, (![A_1709]: (v1_funct_1(k1_tmap_1(A_1709, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1709)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1709)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1709))), inference(resolution, [status(thm)], [c_76, c_47228])).
% 30.48/20.21  tff(c_47245, plain, (![A_1709]: (v1_funct_1(k1_tmap_1(A_1709, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1709)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1709)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1709))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_47235])).
% 30.48/20.21  tff(c_47688, plain, (![A_1732]: (v1_funct_1(k1_tmap_1(A_1732, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1732)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1732)) | v1_xboole_0(A_1732))), inference(negUnitSimplification, [status(thm)], [c_90, c_47245])).
% 30.48/20.21  tff(c_47691, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_47688])).
% 30.48/20.21  tff(c_47694, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_47691])).
% 30.48/20.21  tff(c_47695, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_47694])).
% 30.48/20.21  tff(c_46104, plain, (![A_1642, B_1643, C_1644, D_1645]: (k2_partfun1(A_1642, B_1643, C_1644, D_1645)=k7_relat_1(C_1644, D_1645) | ~m1_subset_1(C_1644, k1_zfmisc_1(k2_zfmisc_1(A_1642, B_1643))) | ~v1_funct_1(C_1644))), inference(cnfTransformation, [status(thm)], [f_140])).
% 30.48/20.21  tff(c_46108, plain, (![D_1645]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1645)=k7_relat_1('#skF_6', D_1645) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_46104])).
% 30.48/20.21  tff(c_46114, plain, (![D_1645]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1645)=k7_relat_1('#skF_6', D_1645))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_46108])).
% 30.48/20.21  tff(c_46106, plain, (![D_1645]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1645)=k7_relat_1('#skF_7', D_1645) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_46104])).
% 30.48/20.21  tff(c_46111, plain, (![D_1645]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1645)=k7_relat_1('#skF_7', D_1645))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46106])).
% 30.48/20.21  tff(c_64, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (v1_funct_2(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k4_subset_1(A_172, C_174, D_175), B_173) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_222])).
% 30.48/20.21  tff(c_62, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (m1_subset_1(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172, C_174, D_175), B_173))) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_222])).
% 30.48/20.21  tff(c_46976, plain, (![E_1702, F_1705, B_1704, D_1700, A_1701, C_1703]: (k2_partfun1(k4_subset_1(A_1701, C_1703, D_1700), B_1704, k1_tmap_1(A_1701, B_1704, C_1703, D_1700, E_1702, F_1705), C_1703)=E_1702 | ~m1_subset_1(k1_tmap_1(A_1701, B_1704, C_1703, D_1700, E_1702, F_1705), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1701, C_1703, D_1700), B_1704))) | ~v1_funct_2(k1_tmap_1(A_1701, B_1704, C_1703, D_1700, E_1702, F_1705), k4_subset_1(A_1701, C_1703, D_1700), B_1704) | ~v1_funct_1(k1_tmap_1(A_1701, B_1704, C_1703, D_1700, E_1702, F_1705)) | k2_partfun1(D_1700, B_1704, F_1705, k9_subset_1(A_1701, C_1703, D_1700))!=k2_partfun1(C_1703, B_1704, E_1702, k9_subset_1(A_1701, C_1703, D_1700)) | ~m1_subset_1(F_1705, k1_zfmisc_1(k2_zfmisc_1(D_1700, B_1704))) | ~v1_funct_2(F_1705, D_1700, B_1704) | ~v1_funct_1(F_1705) | ~m1_subset_1(E_1702, k1_zfmisc_1(k2_zfmisc_1(C_1703, B_1704))) | ~v1_funct_2(E_1702, C_1703, B_1704) | ~v1_funct_1(E_1702) | ~m1_subset_1(D_1700, k1_zfmisc_1(A_1701)) | v1_xboole_0(D_1700) | ~m1_subset_1(C_1703, k1_zfmisc_1(A_1701)) | v1_xboole_0(C_1703) | v1_xboole_0(B_1704) | v1_xboole_0(A_1701))), inference(cnfTransformation, [status(thm)], [f_188])).
% 30.48/20.21  tff(c_84527, plain, (![F_2321, A_2320, B_2317, E_2318, D_2319, C_2322]: (k2_partfun1(k4_subset_1(A_2320, C_2322, D_2319), B_2317, k1_tmap_1(A_2320, B_2317, C_2322, D_2319, E_2318, F_2321), C_2322)=E_2318 | ~v1_funct_2(k1_tmap_1(A_2320, B_2317, C_2322, D_2319, E_2318, F_2321), k4_subset_1(A_2320, C_2322, D_2319), B_2317) | ~v1_funct_1(k1_tmap_1(A_2320, B_2317, C_2322, D_2319, E_2318, F_2321)) | k2_partfun1(D_2319, B_2317, F_2321, k9_subset_1(A_2320, C_2322, D_2319))!=k2_partfun1(C_2322, B_2317, E_2318, k9_subset_1(A_2320, C_2322, D_2319)) | ~m1_subset_1(F_2321, k1_zfmisc_1(k2_zfmisc_1(D_2319, B_2317))) | ~v1_funct_2(F_2321, D_2319, B_2317) | ~v1_funct_1(F_2321) | ~m1_subset_1(E_2318, k1_zfmisc_1(k2_zfmisc_1(C_2322, B_2317))) | ~v1_funct_2(E_2318, C_2322, B_2317) | ~v1_funct_1(E_2318) | ~m1_subset_1(D_2319, k1_zfmisc_1(A_2320)) | v1_xboole_0(D_2319) | ~m1_subset_1(C_2322, k1_zfmisc_1(A_2320)) | v1_xboole_0(C_2322) | v1_xboole_0(B_2317) | v1_xboole_0(A_2320))), inference(resolution, [status(thm)], [c_62, c_46976])).
% 30.48/20.21  tff(c_100309, plain, (![C_2511, B_2506, E_2507, A_2509, F_2510, D_2508]: (k2_partfun1(k4_subset_1(A_2509, C_2511, D_2508), B_2506, k1_tmap_1(A_2509, B_2506, C_2511, D_2508, E_2507, F_2510), C_2511)=E_2507 | ~v1_funct_1(k1_tmap_1(A_2509, B_2506, C_2511, D_2508, E_2507, F_2510)) | k2_partfun1(D_2508, B_2506, F_2510, k9_subset_1(A_2509, C_2511, D_2508))!=k2_partfun1(C_2511, B_2506, E_2507, k9_subset_1(A_2509, C_2511, D_2508)) | ~m1_subset_1(F_2510, k1_zfmisc_1(k2_zfmisc_1(D_2508, B_2506))) | ~v1_funct_2(F_2510, D_2508, B_2506) | ~v1_funct_1(F_2510) | ~m1_subset_1(E_2507, k1_zfmisc_1(k2_zfmisc_1(C_2511, B_2506))) | ~v1_funct_2(E_2507, C_2511, B_2506) | ~v1_funct_1(E_2507) | ~m1_subset_1(D_2508, k1_zfmisc_1(A_2509)) | v1_xboole_0(D_2508) | ~m1_subset_1(C_2511, k1_zfmisc_1(A_2509)) | v1_xboole_0(C_2511) | v1_xboole_0(B_2506) | v1_xboole_0(A_2509))), inference(resolution, [status(thm)], [c_64, c_84527])).
% 30.48/20.21  tff(c_100313, plain, (![A_2509, C_2511, E_2507]: (k2_partfun1(k4_subset_1(A_2509, C_2511, '#skF_5'), '#skF_3', k1_tmap_1(A_2509, '#skF_3', C_2511, '#skF_5', E_2507, '#skF_7'), C_2511)=E_2507 | ~v1_funct_1(k1_tmap_1(A_2509, '#skF_3', C_2511, '#skF_5', E_2507, '#skF_7')) | k2_partfun1(C_2511, '#skF_3', E_2507, k9_subset_1(A_2509, C_2511, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_2509, C_2511, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2507, k1_zfmisc_1(k2_zfmisc_1(C_2511, '#skF_3'))) | ~v1_funct_2(E_2507, C_2511, '#skF_3') | ~v1_funct_1(E_2507) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2509)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2511, k1_zfmisc_1(A_2509)) | v1_xboole_0(C_2511) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2509))), inference(resolution, [status(thm)], [c_70, c_100309])).
% 30.48/20.21  tff(c_100319, plain, (![A_2509, C_2511, E_2507]: (k2_partfun1(k4_subset_1(A_2509, C_2511, '#skF_5'), '#skF_3', k1_tmap_1(A_2509, '#skF_3', C_2511, '#skF_5', E_2507, '#skF_7'), C_2511)=E_2507 | ~v1_funct_1(k1_tmap_1(A_2509, '#skF_3', C_2511, '#skF_5', E_2507, '#skF_7')) | k2_partfun1(C_2511, '#skF_3', E_2507, k9_subset_1(A_2509, C_2511, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2509, C_2511, '#skF_5')) | ~m1_subset_1(E_2507, k1_zfmisc_1(k2_zfmisc_1(C_2511, '#skF_3'))) | ~v1_funct_2(E_2507, C_2511, '#skF_3') | ~v1_funct_1(E_2507) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2509)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2511, k1_zfmisc_1(A_2509)) | v1_xboole_0(C_2511) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2509))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_46111, c_100313])).
% 30.48/20.21  tff(c_100841, plain, (![A_2515, C_2516, E_2517]: (k2_partfun1(k4_subset_1(A_2515, C_2516, '#skF_5'), '#skF_3', k1_tmap_1(A_2515, '#skF_3', C_2516, '#skF_5', E_2517, '#skF_7'), C_2516)=E_2517 | ~v1_funct_1(k1_tmap_1(A_2515, '#skF_3', C_2516, '#skF_5', E_2517, '#skF_7')) | k2_partfun1(C_2516, '#skF_3', E_2517, k9_subset_1(A_2515, C_2516, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2515, C_2516, '#skF_5')) | ~m1_subset_1(E_2517, k1_zfmisc_1(k2_zfmisc_1(C_2516, '#skF_3'))) | ~v1_funct_2(E_2517, C_2516, '#skF_3') | ~v1_funct_1(E_2517) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2515)) | ~m1_subset_1(C_2516, k1_zfmisc_1(A_2515)) | v1_xboole_0(C_2516) | v1_xboole_0(A_2515))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_100319])).
% 30.48/20.21  tff(c_100848, plain, (![A_2515]: (k2_partfun1(k4_subset_1(A_2515, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2515, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2515, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_2515, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2515, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2515)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2515)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2515))), inference(resolution, [status(thm)], [c_76, c_100841])).
% 30.48/20.21  tff(c_100858, plain, (![A_2515]: (k2_partfun1(k4_subset_1(A_2515, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2515, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2515, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2515, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2515, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2515)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2515)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2515))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_46114, c_100848])).
% 30.48/20.21  tff(c_103572, plain, (![A_2551]: (k2_partfun1(k4_subset_1(A_2551, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2551, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2551, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2551, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2551, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2551)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2551)) | v1_xboole_0(A_2551))), inference(negUnitSimplification, [status(thm)], [c_90, c_100858])).
% 30.48/20.21  tff(c_7343, plain, (![B_892, A_893]: (k1_relat_1(B_892)=A_893 | ~v1_partfun1(B_892, A_893) | ~v4_relat_1(B_892, A_893) | ~v1_relat_1(B_892))), inference(cnfTransformation, [status(thm)], [f_134])).
% 30.48/20.21  tff(c_7346, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7162, c_7343])).
% 30.48/20.21  tff(c_7352, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_7346])).
% 30.48/20.21  tff(c_7356, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_7352])).
% 30.48/20.21  tff(c_8180, plain, (![C_951, A_952, B_953]: (v1_partfun1(C_951, A_952) | ~v1_funct_2(C_951, A_952, B_953) | ~v1_funct_1(C_951) | ~m1_subset_1(C_951, k1_zfmisc_1(k2_zfmisc_1(A_952, B_953))) | v1_xboole_0(B_953))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.21  tff(c_8186, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_8180])).
% 30.48/20.21  tff(c_8193, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_8186])).
% 30.48/20.21  tff(c_8195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_7356, c_8193])).
% 30.48/20.21  tff(c_8196, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_7352])).
% 30.48/20.21  tff(c_7192, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7177])).
% 30.48/20.21  tff(c_8198, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8196, c_7192])).
% 30.48/20.21  tff(c_8202, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8196, c_16])).
% 30.48/20.21  tff(c_8765, plain, (![B_988]: (k7_relat_1('#skF_6', B_988)=k1_xboole_0 | ~r1_xboole_0(B_988, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_8202])).
% 30.48/20.21  tff(c_8777, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_8765])).
% 30.48/20.21  tff(c_8784, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_8198, c_8777])).
% 30.48/20.21  tff(c_8791, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8784, c_26])).
% 30.48/20.21  tff(c_8797, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_20, c_8791])).
% 30.48/20.21  tff(c_8799, plain, (![C_989, B_990, A_991]: (k7_relat_1(k7_relat_1(C_989, B_990), A_991)=k7_relat_1(C_989, A_991) | ~r1_tarski(A_991, B_990) | ~v1_relat_1(C_989))), inference(cnfTransformation, [status(thm)], [f_52])).
% 30.48/20.21  tff(c_8824, plain, (![A_991]: (k7_relat_1(k1_xboole_0, A_991)=k7_relat_1('#skF_6', A_991) | ~r1_tarski(A_991, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8784, c_8799])).
% 30.48/20.21  tff(c_9324, plain, (![A_1025]: (k7_relat_1(k1_xboole_0, A_1025)=k7_relat_1('#skF_6', A_1025) | ~r1_tarski(A_1025, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_8824])).
% 30.48/20.21  tff(c_9335, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_8797, c_9324])).
% 30.48/20.21  tff(c_9349, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7048, c_9335])).
% 30.48/20.21  tff(c_7204, plain, (![A_878, B_879]: (r1_xboole_0(A_878, B_879) | ~r1_subset_1(A_878, B_879) | v1_xboole_0(B_879) | v1_xboole_0(A_878))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.48/20.21  tff(c_9615, plain, (![A_1046, B_1047]: (k3_xboole_0(A_1046, B_1047)=k1_xboole_0 | ~r1_subset_1(A_1046, B_1047) | v1_xboole_0(B_1047) | v1_xboole_0(A_1046))), inference(resolution, [status(thm)], [c_7204, c_2])).
% 30.48/20.21  tff(c_9621, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_9615])).
% 30.48/20.21  tff(c_9625, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_9621])).
% 30.48/20.21  tff(c_7349, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7161, c_7343])).
% 30.48/20.21  tff(c_7355, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_7349])).
% 30.48/20.21  tff(c_8228, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_7355])).
% 30.48/20.21  tff(c_8623, plain, (![C_979, A_980, B_981]: (v1_partfun1(C_979, A_980) | ~v1_funct_2(C_979, A_980, B_981) | ~v1_funct_1(C_979) | ~m1_subset_1(C_979, k1_zfmisc_1(k2_zfmisc_1(A_980, B_981))) | v1_xboole_0(B_981))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.21  tff(c_8626, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_8623])).
% 30.48/20.21  tff(c_8632, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_8626])).
% 30.48/20.21  tff(c_8634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_8228, c_8632])).
% 30.48/20.21  tff(c_8635, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_7355])).
% 30.48/20.21  tff(c_8641, plain, (![B_18]: (k7_relat_1('#skF_7', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8635, c_16])).
% 30.48/20.21  tff(c_8731, plain, (![B_987]: (k7_relat_1('#skF_7', B_987)=k1_xboole_0 | ~r1_xboole_0(B_987, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_8641])).
% 30.48/20.21  tff(c_8735, plain, (![A_25]: (k7_relat_1('#skF_7', A_25)=k1_xboole_0 | ~r1_subset_1(A_25, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_34, c_8731])).
% 30.48/20.21  tff(c_9067, plain, (![A_1009]: (k7_relat_1('#skF_7', A_1009)=k1_xboole_0 | ~r1_subset_1(A_1009, '#skF_5') | v1_xboole_0(A_1009))), inference(negUnitSimplification, [status(thm)], [c_86, c_8735])).
% 30.48/20.21  tff(c_9070, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_9067])).
% 30.48/20.21  tff(c_9073, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_9070])).
% 30.48/20.21  tff(c_9086, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_9073, c_26])).
% 30.48/20.21  tff(c_9098, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_20, c_9086])).
% 30.48/20.21  tff(c_14, plain, (![C_15, B_14, A_13]: (k7_relat_1(k7_relat_1(C_15, B_14), A_13)=k7_relat_1(C_15, A_13) | ~r1_tarski(A_13, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 30.48/20.21  tff(c_9080, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k7_relat_1('#skF_7', A_13) | ~r1_tarski(A_13, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_9073, c_14])).
% 30.48/20.21  tff(c_9149, plain, (![A_1019]: (k7_relat_1(k1_xboole_0, A_1019)=k7_relat_1('#skF_7', A_1019) | ~r1_tarski(A_1019, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_9080])).
% 30.48/20.21  tff(c_9152, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_9098, c_9149])).
% 30.48/20.21  tff(c_9173, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7048, c_9152])).
% 30.48/20.21  tff(c_8671, plain, (![A_982, B_983, C_984]: (k9_subset_1(A_982, B_983, C_984)=k3_xboole_0(B_983, C_984) | ~m1_subset_1(C_984, k1_zfmisc_1(A_982)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.48/20.21  tff(c_8682, plain, (![B_983]: (k9_subset_1('#skF_2', B_983, '#skF_5')=k3_xboole_0(B_983, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_8671])).
% 30.48/20.21  tff(c_9136, plain, (![E_1014, C_1018, A_1016, F_1017, D_1015, B_1013]: (v1_funct_1(k1_tmap_1(A_1016, B_1013, C_1018, D_1015, E_1014, F_1017)) | ~m1_subset_1(F_1017, k1_zfmisc_1(k2_zfmisc_1(D_1015, B_1013))) | ~v1_funct_2(F_1017, D_1015, B_1013) | ~v1_funct_1(F_1017) | ~m1_subset_1(E_1014, k1_zfmisc_1(k2_zfmisc_1(C_1018, B_1013))) | ~v1_funct_2(E_1014, C_1018, B_1013) | ~v1_funct_1(E_1014) | ~m1_subset_1(D_1015, k1_zfmisc_1(A_1016)) | v1_xboole_0(D_1015) | ~m1_subset_1(C_1018, k1_zfmisc_1(A_1016)) | v1_xboole_0(C_1018) | v1_xboole_0(B_1013) | v1_xboole_0(A_1016))), inference(cnfTransformation, [status(thm)], [f_222])).
% 30.48/20.21  tff(c_9138, plain, (![A_1016, C_1018, E_1014]: (v1_funct_1(k1_tmap_1(A_1016, '#skF_3', C_1018, '#skF_5', E_1014, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1014, k1_zfmisc_1(k2_zfmisc_1(C_1018, '#skF_3'))) | ~v1_funct_2(E_1014, C_1018, '#skF_3') | ~v1_funct_1(E_1014) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1016)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1018, k1_zfmisc_1(A_1016)) | v1_xboole_0(C_1018) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1016))), inference(resolution, [status(thm)], [c_70, c_9136])).
% 30.48/20.21  tff(c_9143, plain, (![A_1016, C_1018, E_1014]: (v1_funct_1(k1_tmap_1(A_1016, '#skF_3', C_1018, '#skF_5', E_1014, '#skF_7')) | ~m1_subset_1(E_1014, k1_zfmisc_1(k2_zfmisc_1(C_1018, '#skF_3'))) | ~v1_funct_2(E_1014, C_1018, '#skF_3') | ~v1_funct_1(E_1014) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1016)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1018, k1_zfmisc_1(A_1016)) | v1_xboole_0(C_1018) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1016))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_9138])).
% 30.48/20.21  tff(c_10346, plain, (![A_1075, C_1076, E_1077]: (v1_funct_1(k1_tmap_1(A_1075, '#skF_3', C_1076, '#skF_5', E_1077, '#skF_7')) | ~m1_subset_1(E_1077, k1_zfmisc_1(k2_zfmisc_1(C_1076, '#skF_3'))) | ~v1_funct_2(E_1077, C_1076, '#skF_3') | ~v1_funct_1(E_1077) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1075)) | ~m1_subset_1(C_1076, k1_zfmisc_1(A_1075)) | v1_xboole_0(C_1076) | v1_xboole_0(A_1075))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_9143])).
% 30.48/20.21  tff(c_10353, plain, (![A_1075]: (v1_funct_1(k1_tmap_1(A_1075, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1075)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1075)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1075))), inference(resolution, [status(thm)], [c_76, c_10346])).
% 30.48/20.21  tff(c_10363, plain, (![A_1075]: (v1_funct_1(k1_tmap_1(A_1075, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1075)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1075)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1075))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_10353])).
% 30.48/20.21  tff(c_10915, plain, (![A_1096]: (v1_funct_1(k1_tmap_1(A_1096, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1096)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1096)) | v1_xboole_0(A_1096))), inference(negUnitSimplification, [status(thm)], [c_90, c_10363])).
% 30.48/20.21  tff(c_10918, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_10915])).
% 30.48/20.21  tff(c_10921, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10918])).
% 30.48/20.21  tff(c_10922, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_10921])).
% 30.48/20.21  tff(c_8961, plain, (![A_996, B_997, C_998, D_999]: (k2_partfun1(A_996, B_997, C_998, D_999)=k7_relat_1(C_998, D_999) | ~m1_subset_1(C_998, k1_zfmisc_1(k2_zfmisc_1(A_996, B_997))) | ~v1_funct_1(C_998))), inference(cnfTransformation, [status(thm)], [f_140])).
% 30.48/20.21  tff(c_8965, plain, (![D_999]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_999)=k7_relat_1('#skF_6', D_999) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_8961])).
% 30.48/20.21  tff(c_8971, plain, (![D_999]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_999)=k7_relat_1('#skF_6', D_999))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8965])).
% 30.48/20.21  tff(c_8963, plain, (![D_999]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_999)=k7_relat_1('#skF_7', D_999) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_8961])).
% 30.48/20.21  tff(c_8968, plain, (![D_999]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_999)=k7_relat_1('#skF_7', D_999))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_8963])).
% 30.48/20.21  tff(c_9748, plain, (![B_1058, C_1057, E_1056, F_1059, A_1055, D_1054]: (k2_partfun1(k4_subset_1(A_1055, C_1057, D_1054), B_1058, k1_tmap_1(A_1055, B_1058, C_1057, D_1054, E_1056, F_1059), D_1054)=F_1059 | ~m1_subset_1(k1_tmap_1(A_1055, B_1058, C_1057, D_1054, E_1056, F_1059), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1055, C_1057, D_1054), B_1058))) | ~v1_funct_2(k1_tmap_1(A_1055, B_1058, C_1057, D_1054, E_1056, F_1059), k4_subset_1(A_1055, C_1057, D_1054), B_1058) | ~v1_funct_1(k1_tmap_1(A_1055, B_1058, C_1057, D_1054, E_1056, F_1059)) | k2_partfun1(D_1054, B_1058, F_1059, k9_subset_1(A_1055, C_1057, D_1054))!=k2_partfun1(C_1057, B_1058, E_1056, k9_subset_1(A_1055, C_1057, D_1054)) | ~m1_subset_1(F_1059, k1_zfmisc_1(k2_zfmisc_1(D_1054, B_1058))) | ~v1_funct_2(F_1059, D_1054, B_1058) | ~v1_funct_1(F_1059) | ~m1_subset_1(E_1056, k1_zfmisc_1(k2_zfmisc_1(C_1057, B_1058))) | ~v1_funct_2(E_1056, C_1057, B_1058) | ~v1_funct_1(E_1056) | ~m1_subset_1(D_1054, k1_zfmisc_1(A_1055)) | v1_xboole_0(D_1054) | ~m1_subset_1(C_1057, k1_zfmisc_1(A_1055)) | v1_xboole_0(C_1057) | v1_xboole_0(B_1058) | v1_xboole_0(A_1055))), inference(cnfTransformation, [status(thm)], [f_188])).
% 30.48/20.21  tff(c_19969, plain, (![A_1269, D_1268, C_1271, E_1267, B_1266, F_1270]: (k2_partfun1(k4_subset_1(A_1269, C_1271, D_1268), B_1266, k1_tmap_1(A_1269, B_1266, C_1271, D_1268, E_1267, F_1270), D_1268)=F_1270 | ~v1_funct_2(k1_tmap_1(A_1269, B_1266, C_1271, D_1268, E_1267, F_1270), k4_subset_1(A_1269, C_1271, D_1268), B_1266) | ~v1_funct_1(k1_tmap_1(A_1269, B_1266, C_1271, D_1268, E_1267, F_1270)) | k2_partfun1(D_1268, B_1266, F_1270, k9_subset_1(A_1269, C_1271, D_1268))!=k2_partfun1(C_1271, B_1266, E_1267, k9_subset_1(A_1269, C_1271, D_1268)) | ~m1_subset_1(F_1270, k1_zfmisc_1(k2_zfmisc_1(D_1268, B_1266))) | ~v1_funct_2(F_1270, D_1268, B_1266) | ~v1_funct_1(F_1270) | ~m1_subset_1(E_1267, k1_zfmisc_1(k2_zfmisc_1(C_1271, B_1266))) | ~v1_funct_2(E_1267, C_1271, B_1266) | ~v1_funct_1(E_1267) | ~m1_subset_1(D_1268, k1_zfmisc_1(A_1269)) | v1_xboole_0(D_1268) | ~m1_subset_1(C_1271, k1_zfmisc_1(A_1269)) | v1_xboole_0(C_1271) | v1_xboole_0(B_1266) | v1_xboole_0(A_1269))), inference(resolution, [status(thm)], [c_62, c_9748])).
% 30.48/20.21  tff(c_40125, plain, (![F_1489, A_1488, B_1485, E_1486, D_1487, C_1490]: (k2_partfun1(k4_subset_1(A_1488, C_1490, D_1487), B_1485, k1_tmap_1(A_1488, B_1485, C_1490, D_1487, E_1486, F_1489), D_1487)=F_1489 | ~v1_funct_1(k1_tmap_1(A_1488, B_1485, C_1490, D_1487, E_1486, F_1489)) | k2_partfun1(D_1487, B_1485, F_1489, k9_subset_1(A_1488, C_1490, D_1487))!=k2_partfun1(C_1490, B_1485, E_1486, k9_subset_1(A_1488, C_1490, D_1487)) | ~m1_subset_1(F_1489, k1_zfmisc_1(k2_zfmisc_1(D_1487, B_1485))) | ~v1_funct_2(F_1489, D_1487, B_1485) | ~v1_funct_1(F_1489) | ~m1_subset_1(E_1486, k1_zfmisc_1(k2_zfmisc_1(C_1490, B_1485))) | ~v1_funct_2(E_1486, C_1490, B_1485) | ~v1_funct_1(E_1486) | ~m1_subset_1(D_1487, k1_zfmisc_1(A_1488)) | v1_xboole_0(D_1487) | ~m1_subset_1(C_1490, k1_zfmisc_1(A_1488)) | v1_xboole_0(C_1490) | v1_xboole_0(B_1485) | v1_xboole_0(A_1488))), inference(resolution, [status(thm)], [c_64, c_19969])).
% 30.48/20.21  tff(c_40129, plain, (![A_1488, C_1490, E_1486]: (k2_partfun1(k4_subset_1(A_1488, C_1490, '#skF_5'), '#skF_3', k1_tmap_1(A_1488, '#skF_3', C_1490, '#skF_5', E_1486, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1488, '#skF_3', C_1490, '#skF_5', E_1486, '#skF_7')) | k2_partfun1(C_1490, '#skF_3', E_1486, k9_subset_1(A_1488, C_1490, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1488, C_1490, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1486, k1_zfmisc_1(k2_zfmisc_1(C_1490, '#skF_3'))) | ~v1_funct_2(E_1486, C_1490, '#skF_3') | ~v1_funct_1(E_1486) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1488)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1490, k1_zfmisc_1(A_1488)) | v1_xboole_0(C_1490) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1488))), inference(resolution, [status(thm)], [c_70, c_40125])).
% 30.48/20.21  tff(c_40135, plain, (![A_1488, C_1490, E_1486]: (k2_partfun1(k4_subset_1(A_1488, C_1490, '#skF_5'), '#skF_3', k1_tmap_1(A_1488, '#skF_3', C_1490, '#skF_5', E_1486, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1488, '#skF_3', C_1490, '#skF_5', E_1486, '#skF_7')) | k2_partfun1(C_1490, '#skF_3', E_1486, k9_subset_1(A_1488, C_1490, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1488, C_1490, '#skF_5')) | ~m1_subset_1(E_1486, k1_zfmisc_1(k2_zfmisc_1(C_1490, '#skF_3'))) | ~v1_funct_2(E_1486, C_1490, '#skF_3') | ~v1_funct_1(E_1486) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1488)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1490, k1_zfmisc_1(A_1488)) | v1_xboole_0(C_1490) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1488))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_8968, c_40129])).
% 30.48/20.21  tff(c_41118, plain, (![A_1496, C_1497, E_1498]: (k2_partfun1(k4_subset_1(A_1496, C_1497, '#skF_5'), '#skF_3', k1_tmap_1(A_1496, '#skF_3', C_1497, '#skF_5', E_1498, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1496, '#skF_3', C_1497, '#skF_5', E_1498, '#skF_7')) | k2_partfun1(C_1497, '#skF_3', E_1498, k9_subset_1(A_1496, C_1497, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1496, C_1497, '#skF_5')) | ~m1_subset_1(E_1498, k1_zfmisc_1(k2_zfmisc_1(C_1497, '#skF_3'))) | ~v1_funct_2(E_1498, C_1497, '#skF_3') | ~v1_funct_1(E_1498) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1496)) | ~m1_subset_1(C_1497, k1_zfmisc_1(A_1496)) | v1_xboole_0(C_1497) | v1_xboole_0(A_1496))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_40135])).
% 30.48/20.21  tff(c_41125, plain, (![A_1496]: (k2_partfun1(k4_subset_1(A_1496, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1496, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1496, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1496, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1496, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1496)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1496)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1496))), inference(resolution, [status(thm)], [c_76, c_41118])).
% 30.48/20.21  tff(c_41135, plain, (![A_1496]: (k2_partfun1(k4_subset_1(A_1496, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1496, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1496, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1496, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1496, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1496)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1496)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1496))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_8971, c_41125])).
% 30.48/20.21  tff(c_44201, plain, (![A_1525]: (k2_partfun1(k4_subset_1(A_1525, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1525, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1525, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1525, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1525, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1525)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1525)) | v1_xboole_0(A_1525))), inference(negUnitSimplification, [status(thm)], [c_90, c_41135])).
% 30.48/20.21  tff(c_635, plain, (![C_313, A_314, B_315]: (v1_relat_1(C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 30.48/20.21  tff(c_642, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_635])).
% 30.48/20.21  tff(c_661, plain, (![C_316, A_317, B_318]: (v4_relat_1(C_316, A_317) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_317, B_318))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 30.48/20.21  tff(c_668, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_661])).
% 30.48/20.21  tff(c_4357, plain, (![B_608, A_609]: (k1_relat_1(B_608)=A_609 | ~v1_partfun1(B_608, A_609) | ~v4_relat_1(B_608, A_609) | ~v1_relat_1(B_608))), inference(cnfTransformation, [status(thm)], [f_134])).
% 30.48/20.21  tff(c_4366, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_668, c_4357])).
% 30.48/20.21  tff(c_4375, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_4366])).
% 30.48/20.21  tff(c_5442, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_4375])).
% 30.48/20.21  tff(c_5832, plain, (![C_728, A_729, B_730]: (v1_partfun1(C_728, A_729) | ~v1_funct_2(C_728, A_729, B_730) | ~v1_funct_1(C_728) | ~m1_subset_1(C_728, k1_zfmisc_1(k2_zfmisc_1(A_729, B_730))) | v1_xboole_0(B_730))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.21  tff(c_5838, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_5832])).
% 30.48/20.21  tff(c_5845, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5838])).
% 30.48/20.21  tff(c_5847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_5442, c_5845])).
% 30.48/20.21  tff(c_5848, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_4375])).
% 30.48/20.21  tff(c_643, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_635])).
% 30.48/20.21  tff(c_168, plain, (![C_252, A_253, B_254]: (v1_relat_1(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 30.48/20.21  tff(c_176, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_168])).
% 30.48/20.21  tff(c_192, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_176, c_24])).
% 30.48/20.21  tff(c_213, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_192])).
% 30.48/20.21  tff(c_119, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_115])).
% 30.48/20.21  tff(c_255, plain, (![A_267, B_268]: (k7_relat_1(A_267, B_268)=k1_xboole_0 | ~r1_xboole_0(B_268, k1_relat_1(A_267)) | ~v1_relat_1(A_267))), inference(cnfTransformation, [status(thm)], [f_59])).
% 30.48/20.21  tff(c_447, plain, (![A_292]: (k7_relat_1(A_292, '#skF_1'(k1_relat_1(A_292)))=k1_xboole_0 | ~v1_relat_1(A_292) | k1_relat_1(A_292)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_255])).
% 30.48/20.21  tff(c_287, plain, (![B_271, A_272]: (k3_xboole_0(B_271, k2_zfmisc_1(A_272, k2_relat_1(B_271)))=k7_relat_1(B_271, A_272) | ~v1_relat_1(B_271))), inference(cnfTransformation, [status(thm)], [f_78])).
% 30.48/20.21  tff(c_293, plain, (![B_271, A_272]: (v1_relat_1(k7_relat_1(B_271, A_272)) | ~v1_relat_1(B_271) | ~v1_relat_1(B_271))), inference(superposition, [status(thm), theory('equality')], [c_287, c_12])).
% 30.48/20.21  tff(c_460, plain, (![A_292]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_292) | ~v1_relat_1(A_292) | ~v1_relat_1(A_292) | k1_relat_1(A_292)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_447, c_293])).
% 30.48/20.21  tff(c_510, plain, (![A_299]: (~v1_relat_1(A_299) | ~v1_relat_1(A_299) | ~v1_relat_1(A_299) | k1_relat_1(A_299)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_119, c_460])).
% 30.48/20.21  tff(c_514, plain, (~v1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_176, c_510])).
% 30.48/20.21  tff(c_522, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_176, c_514])).
% 30.48/20.21  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_522])).
% 30.48/20.21  tff(c_525, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_192])).
% 30.48/20.21  tff(c_534, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_119])).
% 30.48/20.21  tff(c_541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_534])).
% 30.48/20.21  tff(c_542, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_115])).
% 30.48/20.21  tff(c_669, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_661])).
% 30.48/20.21  tff(c_882, plain, (![B_344, A_345]: (k1_relat_1(B_344)=A_345 | ~v1_partfun1(B_344, A_345) | ~v4_relat_1(B_344, A_345) | ~v1_relat_1(B_344))), inference(cnfTransformation, [status(thm)], [f_134])).
% 30.48/20.21  tff(c_885, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_669, c_882])).
% 30.48/20.21  tff(c_891, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_885])).
% 30.48/20.21  tff(c_895, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_891])).
% 30.48/20.21  tff(c_1483, plain, (![C_389, A_390, B_391]: (v1_partfun1(C_389, A_390) | ~v1_funct_2(C_389, A_390, B_391) | ~v1_funct_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))) | v1_xboole_0(B_391))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.21  tff(c_1489, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1483])).
% 30.48/20.21  tff(c_1496, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1489])).
% 30.48/20.21  tff(c_1498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_895, c_1496])).
% 30.48/20.21  tff(c_1499, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_891])).
% 30.48/20.21  tff(c_658, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_643, c_24])).
% 30.48/20.21  tff(c_672, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_658])).
% 30.48/20.21  tff(c_1501, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1499, c_672])).
% 30.48/20.21  tff(c_1505, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1499, c_16])).
% 30.48/20.21  tff(c_1850, plain, (![B_412]: (k7_relat_1('#skF_6', B_412)=k1_xboole_0 | ~r1_xboole_0(B_412, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_1505])).
% 30.48/20.21  tff(c_1862, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_1850])).
% 30.48/20.21  tff(c_1869, plain, (k7_relat_1('#skF_6', '#skF_1'('#skF_4'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1501, c_1862])).
% 30.48/20.21  tff(c_1876, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1869, c_26])).
% 30.48/20.21  tff(c_1882, plain, (r1_tarski(k1_xboole_0, '#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_20, c_1876])).
% 30.48/20.21  tff(c_1884, plain, (![C_413, B_414, A_415]: (k7_relat_1(k7_relat_1(C_413, B_414), A_415)=k7_relat_1(C_413, A_415) | ~r1_tarski(A_415, B_414) | ~v1_relat_1(C_413))), inference(cnfTransformation, [status(thm)], [f_52])).
% 30.48/20.21  tff(c_1909, plain, (![A_415]: (k7_relat_1(k1_xboole_0, A_415)=k7_relat_1('#skF_6', A_415) | ~r1_tarski(A_415, '#skF_1'('#skF_4')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1869, c_1884])).
% 30.48/20.21  tff(c_2397, plain, (![A_447]: (k7_relat_1(k1_xboole_0, A_447)=k7_relat_1('#skF_6', A_447) | ~r1_tarski(A_447, '#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_1909])).
% 30.48/20.21  tff(c_2408, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_1882, c_2397])).
% 30.48/20.21  tff(c_2422, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_542, c_2408])).
% 30.48/20.21  tff(c_693, plain, (![A_323, B_324]: (r1_xboole_0(A_323, B_324) | ~r1_subset_1(A_323, B_324) | v1_xboole_0(B_324) | v1_xboole_0(A_323))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.48/20.21  tff(c_2522, plain, (![A_457, B_458]: (k3_xboole_0(A_457, B_458)=k1_xboole_0 | ~r1_subset_1(A_457, B_458) | v1_xboole_0(B_458) | v1_xboole_0(A_457))), inference(resolution, [status(thm)], [c_693, c_2])).
% 30.48/20.21  tff(c_2525, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_2522])).
% 30.48/20.21  tff(c_2528, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_2525])).
% 30.48/20.21  tff(c_888, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_668, c_882])).
% 30.48/20.21  tff(c_894, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_888])).
% 30.48/20.21  tff(c_1547, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_894])).
% 30.48/20.21  tff(c_1790, plain, (![C_409, A_410, B_411]: (v1_partfun1(C_409, A_410) | ~v1_funct_2(C_409, A_410, B_411) | ~v1_funct_1(C_409) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))) | v1_xboole_0(B_411))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.21  tff(c_1793, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1790])).
% 30.48/20.21  tff(c_1799, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1793])).
% 30.48/20.21  tff(c_1801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1547, c_1799])).
% 30.48/20.21  tff(c_1802, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_894])).
% 30.48/20.21  tff(c_1808, plain, (![B_18]: (k7_relat_1('#skF_7', B_18)=k1_xboole_0 | ~r1_xboole_0(B_18, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1802, c_16])).
% 30.48/20.21  tff(c_1946, plain, (![B_416]: (k7_relat_1('#skF_7', B_416)=k1_xboole_0 | ~r1_xboole_0(B_416, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_642, c_1808])).
% 30.48/20.21  tff(c_1950, plain, (![A_25]: (k7_relat_1('#skF_7', A_25)=k1_xboole_0 | ~r1_subset_1(A_25, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_34, c_1946])).
% 30.48/20.21  tff(c_2083, plain, (![A_425]: (k7_relat_1('#skF_7', A_425)=k1_xboole_0 | ~r1_subset_1(A_425, '#skF_5') | v1_xboole_0(A_425))), inference(negUnitSimplification, [status(thm)], [c_86, c_1950])).
% 30.48/20.21  tff(c_2086, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_2083])).
% 30.48/20.21  tff(c_2089, plain, (k7_relat_1('#skF_7', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_2086])).
% 30.48/20.21  tff(c_2102, plain, (r1_tarski(k1_relat_1(k1_xboole_0), '#skF_4') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2089, c_26])).
% 30.48/20.21  tff(c_2114, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_20, c_2102])).
% 30.48/20.21  tff(c_2096, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k7_relat_1('#skF_7', A_13) | ~r1_tarski(A_13, '#skF_4') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2089, c_14])).
% 30.48/20.21  tff(c_2203, plain, (![A_433]: (k7_relat_1(k1_xboole_0, A_433)=k7_relat_1('#skF_7', A_433) | ~r1_tarski(A_433, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_642, c_2096])).
% 30.48/20.21  tff(c_2210, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_2114, c_2203])).
% 30.48/20.21  tff(c_2225, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_542, c_2210])).
% 30.48/20.21  tff(c_2072, plain, (![A_421, B_422, C_423, D_424]: (k2_partfun1(A_421, B_422, C_423, D_424)=k7_relat_1(C_423, D_424) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_421, B_422))) | ~v1_funct_1(C_423))), inference(cnfTransformation, [status(thm)], [f_140])).
% 30.48/20.21  tff(c_2076, plain, (![D_424]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_424)=k7_relat_1('#skF_6', D_424) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_2072])).
% 30.48/20.21  tff(c_2082, plain, (![D_424]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_424)=k7_relat_1('#skF_6', D_424))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2076])).
% 30.48/20.21  tff(c_2074, plain, (![D_424]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_424)=k7_relat_1('#skF_7', D_424) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_2072])).
% 30.48/20.21  tff(c_2079, plain, (![D_424]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_424)=k7_relat_1('#skF_7', D_424))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2074])).
% 30.48/20.21  tff(c_739, plain, (![A_330, B_331, C_332]: (k9_subset_1(A_330, B_331, C_332)=k3_xboole_0(B_331, C_332) | ~m1_subset_1(C_332, k1_zfmisc_1(A_330)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.48/20.21  tff(c_750, plain, (![B_331]: (k9_subset_1('#skF_2', B_331, '#skF_5')=k3_xboole_0(B_331, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_739])).
% 30.48/20.21  tff(c_68, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_264])).
% 30.48/20.21  tff(c_118, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 30.48/20.21  tff(c_769, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_750, c_750, c_118])).
% 30.48/20.21  tff(c_2118, plain, (k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2079, c_769])).
% 30.48/20.21  tff(c_2954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2422, c_2528, c_2225, c_2528, c_2082, c_2118])).
% 30.48/20.21  tff(c_2955, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_658])).
% 30.48/20.21  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 30.48/20.21  tff(c_2971, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_2955, c_18])).
% 30.48/20.21  tff(c_22, plain, (![A_19]: (k2_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 30.48/20.21  tff(c_659, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_643, c_22])).
% 30.48/20.21  tff(c_670, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_659])).
% 30.48/20.21  tff(c_2958, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_670])).
% 30.48/20.21  tff(c_3002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2971, c_2958])).
% 30.48/20.21  tff(c_3003, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_659])).
% 30.48/20.21  tff(c_3016, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_3003, c_20])).
% 30.48/20.21  tff(c_4363, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_669, c_4357])).
% 30.48/20.21  tff(c_4372, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_3016, c_4363])).
% 30.48/20.21  tff(c_4376, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_4372])).
% 30.48/20.21  tff(c_5332, plain, (![C_686, A_687, B_688]: (v1_partfun1(C_686, A_687) | ~v1_funct_2(C_686, A_687, B_688) | ~v1_funct_1(C_686) | ~m1_subset_1(C_686, k1_zfmisc_1(k2_zfmisc_1(A_687, B_688))) | v1_xboole_0(B_688))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.21  tff(c_5338, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_5332])).
% 30.48/20.21  tff(c_5345, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_5338])).
% 30.48/20.21  tff(c_5347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_4376, c_5345])).
% 30.48/20.21  tff(c_5348, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_4372])).
% 30.48/20.21  tff(c_4233, plain, (![A_16, B_18]: (k7_relat_1(A_16, B_18)='#skF_6' | ~r1_xboole_0(B_18, k1_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_16])).
% 30.48/20.21  tff(c_6267, plain, (![A_765, B_766]: (k7_relat_1(A_765, B_766)='#skF_4' | ~r1_xboole_0(B_766, k1_relat_1(A_765)) | ~v1_relat_1(A_765))), inference(demodulation, [status(thm), theory('equality')], [c_5348, c_4233])).
% 30.48/20.22  tff(c_6278, plain, (![B_766]: (k7_relat_1('#skF_7', B_766)='#skF_4' | ~r1_xboole_0(B_766, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5848, c_6267])).
% 30.48/20.22  tff(c_6293, plain, (![B_767]: (k7_relat_1('#skF_7', B_767)='#skF_4' | ~r1_xboole_0(B_767, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_642, c_6278])).
% 30.48/20.22  tff(c_6305, plain, (![A_25]: (k7_relat_1('#skF_7', A_25)='#skF_4' | ~r1_subset_1(A_25, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_34, c_6293])).
% 30.48/20.22  tff(c_6401, plain, (![A_772]: (k7_relat_1('#skF_7', A_772)='#skF_4' | ~r1_subset_1(A_772, '#skF_5') | v1_xboole_0(A_772))), inference(negUnitSimplification, [status(thm)], [c_86, c_6305])).
% 30.48/20.22  tff(c_6404, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_6401])).
% 30.48/20.22  tff(c_6407, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_90, c_6404])).
% 30.48/20.22  tff(c_3011, plain, (k7_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_3003, c_3003, c_542])).
% 30.48/20.22  tff(c_5363, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5348, c_5348, c_5348, c_3011])).
% 30.48/20.22  tff(c_4278, plain, (![A_602, B_603]: (r1_xboole_0(A_602, B_603) | ~r1_subset_1(A_602, B_603) | v1_xboole_0(B_603) | v1_xboole_0(A_602))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.48/20.22  tff(c_3013, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_6' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_2])).
% 30.48/20.22  tff(c_4289, plain, (![A_602, B_603]: (k3_xboole_0(A_602, B_603)='#skF_6' | ~r1_subset_1(A_602, B_603) | v1_xboole_0(B_603) | v1_xboole_0(A_602))), inference(resolution, [status(thm)], [c_4278, c_3013])).
% 30.48/20.22  tff(c_6643, plain, (![A_797, B_798]: (k3_xboole_0(A_797, B_798)='#skF_4' | ~r1_subset_1(A_797, B_798) | v1_xboole_0(B_798) | v1_xboole_0(A_797))), inference(demodulation, [status(thm), theory('equality')], [c_5348, c_4289])).
% 30.48/20.22  tff(c_6649, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_6643])).
% 30.48/20.22  tff(c_6653, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_6649])).
% 30.48/20.22  tff(c_5376, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5348, c_80])).
% 30.48/20.22  tff(c_5374, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5348, c_76])).
% 30.48/20.22  tff(c_6194, plain, (![A_756, B_757, C_758, D_759]: (k2_partfun1(A_756, B_757, C_758, D_759)=k7_relat_1(C_758, D_759) | ~m1_subset_1(C_758, k1_zfmisc_1(k2_zfmisc_1(A_756, B_757))) | ~v1_funct_1(C_758))), inference(cnfTransformation, [status(thm)], [f_140])).
% 30.48/20.22  tff(c_6196, plain, (![D_759]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_759)=k7_relat_1('#skF_4', D_759) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5374, c_6194])).
% 30.48/20.22  tff(c_6201, plain, (![D_759]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_759)=k7_relat_1('#skF_4', D_759))), inference(demodulation, [status(thm), theory('equality')], [c_5376, c_6196])).
% 30.48/20.22  tff(c_6198, plain, (![D_759]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_759)=k7_relat_1('#skF_7', D_759) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_6194])).
% 30.48/20.22  tff(c_6204, plain, (![D_759]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_759)=k7_relat_1('#skF_7', D_759))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6198])).
% 30.48/20.22  tff(c_5414, plain, (![A_689, B_690, C_691]: (k9_subset_1(A_689, B_690, C_691)=k3_xboole_0(B_690, C_691) | ~m1_subset_1(C_691, k1_zfmisc_1(A_689)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.48/20.22  tff(c_5422, plain, (![B_690]: (k9_subset_1('#skF_2', B_690, '#skF_5')=k3_xboole_0(B_690, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_5414])).
% 30.48/20.22  tff(c_5373, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_4', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5348, c_118])).
% 30.48/20.22  tff(c_6232, plain, (k7_relat_1('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6201, c_6204, c_5422, c_5422, c_5373])).
% 30.48/20.22  tff(c_6654, plain, (k7_relat_1('#skF_7', '#skF_4')!=k7_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6653, c_6653, c_6232])).
% 30.48/20.22  tff(c_6657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6407, c_5363, c_6654])).
% 30.48/20.22  tff(c_6658, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_68])).
% 30.48/20.22  tff(c_7191, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_6658])).
% 30.48/20.22  tff(c_44212, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44201, c_7191])).
% 30.48/20.22  tff(c_44226, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_9349, c_9625, c_9173, c_9625, c_8682, c_8682, c_10922, c_44212])).
% 30.48/20.22  tff(c_44228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_44226])).
% 30.48/20.22  tff(c_44229, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7177])).
% 30.48/20.22  tff(c_44245, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44229, c_44229, c_18])).
% 30.48/20.22  tff(c_7178, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_7153, c_22])).
% 30.48/20.22  tff(c_7181, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7178])).
% 30.48/20.22  tff(c_44231, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44229, c_7181])).
% 30.48/20.22  tff(c_44268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44245, c_44231])).
% 30.48/20.22  tff(c_44269, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_6658])).
% 30.48/20.22  tff(c_103584, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103572, c_44269])).
% 30.48/20.22  tff(c_103598, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_46462, c_46585, c_44398, c_46157, c_46585, c_44398, c_47695, c_103584])).
% 30.48/20.22  tff(c_103600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_103598])).
% 30.48/20.22  tff(c_103601, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7177])).
% 30.48/20.22  tff(c_103603, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103601, c_7181])).
% 30.48/20.22  tff(c_103617, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103601, c_103601, c_18])).
% 30.48/20.22  tff(c_103634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103603, c_103617])).
% 30.48/20.22  tff(c_103635, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7178])).
% 30.48/20.22  tff(c_103658, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103635, c_103635, c_20])).
% 30.48/20.22  tff(c_137662, plain, (![B_3388, A_3389]: (k1_relat_1(B_3388)=A_3389 | ~v1_partfun1(B_3388, A_3389) | ~v4_relat_1(B_3388, A_3389) | ~v1_relat_1(B_3388))), inference(cnfTransformation, [status(thm)], [f_134])).
% 30.48/20.22  tff(c_137668, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7162, c_137662])).
% 30.48/20.22  tff(c_137677, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_103658, c_137668])).
% 30.48/20.22  tff(c_137681, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_137677])).
% 30.48/20.22  tff(c_138375, plain, (![C_3444, A_3445, B_3446]: (v1_partfun1(C_3444, A_3445) | ~v1_funct_2(C_3444, A_3445, B_3446) | ~v1_funct_1(C_3444) | ~m1_subset_1(C_3444, k1_zfmisc_1(k2_zfmisc_1(A_3445, B_3446))) | v1_xboole_0(B_3446))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.22  tff(c_138381, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_138375])).
% 30.48/20.22  tff(c_138388, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_138381])).
% 30.48/20.22  tff(c_138390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_137681, c_138388])).
% 30.48/20.22  tff(c_138391, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_137677])).
% 30.48/20.22  tff(c_103654, plain, (k7_relat_1('#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103635, c_103635, c_103635, c_7048])).
% 30.48/20.22  tff(c_138411, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138391, c_138391, c_138391, c_103654])).
% 30.48/20.22  tff(c_103653, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)='#skF_6' | ~r1_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_103635, c_2])).
% 30.48/20.22  tff(c_138890, plain, (![A_3486, B_3487]: (k3_xboole_0(A_3486, B_3487)='#skF_4' | ~r1_xboole_0(A_3486, B_3487))), inference(demodulation, [status(thm), theory('equality')], [c_138391, c_103653])).
% 30.48/20.22  tff(c_139586, plain, (![A_3552, B_3553]: (k3_xboole_0(A_3552, B_3553)='#skF_4' | ~r1_subset_1(A_3552, B_3553) | v1_xboole_0(B_3553) | v1_xboole_0(A_3552))), inference(resolution, [status(thm)], [c_34, c_138890])).
% 30.48/20.22  tff(c_139592, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_139586])).
% 30.48/20.22  tff(c_139596, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_139592])).
% 30.48/20.22  tff(c_137671, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7161, c_137662])).
% 30.48/20.22  tff(c_137680, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_137671])).
% 30.48/20.22  tff(c_138584, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_137680])).
% 30.48/20.22  tff(c_138728, plain, (![C_3473, A_3474, B_3475]: (v1_partfun1(C_3473, A_3474) | ~v1_funct_2(C_3473, A_3474, B_3475) | ~v1_funct_1(C_3473) | ~m1_subset_1(C_3473, k1_zfmisc_1(k2_zfmisc_1(A_3474, B_3475))) | v1_xboole_0(B_3475))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.22  tff(c_138734, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_138728])).
% 30.48/20.22  tff(c_138741, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_138734])).
% 30.48/20.22  tff(c_138743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_138584, c_138741])).
% 30.48/20.22  tff(c_138744, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_137680])).
% 30.48/20.22  tff(c_136115, plain, (![A_16, B_18]: (k7_relat_1(A_16, B_18)='#skF_6' | ~r1_xboole_0(B_18, k1_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_103635, c_16])).
% 30.48/20.22  tff(c_139083, plain, (![A_3509, B_3510]: (k7_relat_1(A_3509, B_3510)='#skF_4' | ~r1_xboole_0(B_3510, k1_relat_1(A_3509)) | ~v1_relat_1(A_3509))), inference(demodulation, [status(thm), theory('equality')], [c_138391, c_136115])).
% 30.48/20.22  tff(c_139094, plain, (![B_3510]: (k7_relat_1('#skF_7', B_3510)='#skF_4' | ~r1_xboole_0(B_3510, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_138744, c_139083])).
% 30.48/20.22  tff(c_139122, plain, (![B_3514]: (k7_relat_1('#skF_7', B_3514)='#skF_4' | ~r1_xboole_0(B_3514, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_139094])).
% 30.48/20.22  tff(c_139134, plain, (![A_25]: (k7_relat_1('#skF_7', A_25)='#skF_4' | ~r1_subset_1(A_25, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_34, c_139122])).
% 30.48/20.22  tff(c_139213, plain, (![A_3522]: (k7_relat_1('#skF_7', A_3522)='#skF_4' | ~r1_subset_1(A_3522, '#skF_5') | v1_xboole_0(A_3522))), inference(negUnitSimplification, [status(thm)], [c_86, c_139134])).
% 30.48/20.22  tff(c_139216, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_139213])).
% 30.48/20.22  tff(c_139219, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_90, c_139216])).
% 30.48/20.22  tff(c_138465, plain, (![A_3447, B_3448, C_3449]: (k9_subset_1(A_3447, B_3448, C_3449)=k3_xboole_0(B_3448, C_3449) | ~m1_subset_1(C_3449, k1_zfmisc_1(A_3447)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.48/20.22  tff(c_138473, plain, (![B_3448]: (k9_subset_1('#skF_2', B_3448, '#skF_5')=k3_xboole_0(B_3448, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_138465])).
% 30.48/20.22  tff(c_138425, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138391, c_80])).
% 30.48/20.22  tff(c_138424, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138391, c_78])).
% 30.48/20.22  tff(c_138423, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_138391, c_76])).
% 30.48/20.22  tff(c_139070, plain, (![A_3506, E_3504, C_3508, B_3503, D_3505, F_3507]: (v1_funct_1(k1_tmap_1(A_3506, B_3503, C_3508, D_3505, E_3504, F_3507)) | ~m1_subset_1(F_3507, k1_zfmisc_1(k2_zfmisc_1(D_3505, B_3503))) | ~v1_funct_2(F_3507, D_3505, B_3503) | ~v1_funct_1(F_3507) | ~m1_subset_1(E_3504, k1_zfmisc_1(k2_zfmisc_1(C_3508, B_3503))) | ~v1_funct_2(E_3504, C_3508, B_3503) | ~v1_funct_1(E_3504) | ~m1_subset_1(D_3505, k1_zfmisc_1(A_3506)) | v1_xboole_0(D_3505) | ~m1_subset_1(C_3508, k1_zfmisc_1(A_3506)) | v1_xboole_0(C_3508) | v1_xboole_0(B_3503) | v1_xboole_0(A_3506))), inference(cnfTransformation, [status(thm)], [f_222])).
% 30.48/20.22  tff(c_139074, plain, (![A_3506, C_3508, E_3504]: (v1_funct_1(k1_tmap_1(A_3506, '#skF_3', C_3508, '#skF_5', E_3504, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3504, k1_zfmisc_1(k2_zfmisc_1(C_3508, '#skF_3'))) | ~v1_funct_2(E_3504, C_3508, '#skF_3') | ~v1_funct_1(E_3504) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3506)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3508, k1_zfmisc_1(A_3506)) | v1_xboole_0(C_3508) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3506))), inference(resolution, [status(thm)], [c_70, c_139070])).
% 30.48/20.22  tff(c_139081, plain, (![A_3506, C_3508, E_3504]: (v1_funct_1(k1_tmap_1(A_3506, '#skF_3', C_3508, '#skF_5', E_3504, '#skF_7')) | ~m1_subset_1(E_3504, k1_zfmisc_1(k2_zfmisc_1(C_3508, '#skF_3'))) | ~v1_funct_2(E_3504, C_3508, '#skF_3') | ~v1_funct_1(E_3504) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3506)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3508, k1_zfmisc_1(A_3506)) | v1_xboole_0(C_3508) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3506))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_139074])).
% 30.48/20.22  tff(c_139109, plain, (![A_3511, C_3512, E_3513]: (v1_funct_1(k1_tmap_1(A_3511, '#skF_3', C_3512, '#skF_5', E_3513, '#skF_7')) | ~m1_subset_1(E_3513, k1_zfmisc_1(k2_zfmisc_1(C_3512, '#skF_3'))) | ~v1_funct_2(E_3513, C_3512, '#skF_3') | ~v1_funct_1(E_3513) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3511)) | ~m1_subset_1(C_3512, k1_zfmisc_1(A_3511)) | v1_xboole_0(C_3512) | v1_xboole_0(A_3511))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_139081])).
% 30.48/20.22  tff(c_139111, plain, (![A_3511]: (v1_funct_1(k1_tmap_1(A_3511, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3511)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3511)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3511))), inference(resolution, [status(thm)], [c_138423, c_139109])).
% 30.48/20.22  tff(c_139116, plain, (![A_3511]: (v1_funct_1(k1_tmap_1(A_3511, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3511)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3511)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3511))), inference(demodulation, [status(thm), theory('equality')], [c_138425, c_138424, c_139111])).
% 30.48/20.22  tff(c_139578, plain, (![A_3551]: (v1_funct_1(k1_tmap_1(A_3551, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3551)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3551)) | v1_xboole_0(A_3551))), inference(negUnitSimplification, [status(thm)], [c_90, c_139116])).
% 30.48/20.22  tff(c_139581, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_139578])).
% 30.48/20.22  tff(c_139584, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_139581])).
% 30.48/20.22  tff(c_139585, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_139584])).
% 30.48/20.22  tff(c_138807, plain, (![A_3478, B_3479, C_3480, D_3481]: (k2_partfun1(A_3478, B_3479, C_3480, D_3481)=k7_relat_1(C_3480, D_3481) | ~m1_subset_1(C_3480, k1_zfmisc_1(k2_zfmisc_1(A_3478, B_3479))) | ~v1_funct_1(C_3480))), inference(cnfTransformation, [status(thm)], [f_140])).
% 30.48/20.22  tff(c_138809, plain, (![D_3481]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_3481)=k7_relat_1('#skF_4', D_3481) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_138423, c_138807])).
% 30.48/20.22  tff(c_138814, plain, (![D_3481]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_3481)=k7_relat_1('#skF_4', D_3481))), inference(demodulation, [status(thm), theory('equality')], [c_138425, c_138809])).
% 30.48/20.22  tff(c_138811, plain, (![D_3481]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_3481)=k7_relat_1('#skF_7', D_3481) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_138807])).
% 30.48/20.22  tff(c_138817, plain, (![D_3481]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_3481)=k7_relat_1('#skF_7', D_3481))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_138811])).
% 30.48/20.22  tff(c_139617, plain, (![E_3556, D_3554, F_3559, B_3558, A_3555, C_3557]: (k2_partfun1(k4_subset_1(A_3555, C_3557, D_3554), B_3558, k1_tmap_1(A_3555, B_3558, C_3557, D_3554, E_3556, F_3559), C_3557)=E_3556 | ~m1_subset_1(k1_tmap_1(A_3555, B_3558, C_3557, D_3554, E_3556, F_3559), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3555, C_3557, D_3554), B_3558))) | ~v1_funct_2(k1_tmap_1(A_3555, B_3558, C_3557, D_3554, E_3556, F_3559), k4_subset_1(A_3555, C_3557, D_3554), B_3558) | ~v1_funct_1(k1_tmap_1(A_3555, B_3558, C_3557, D_3554, E_3556, F_3559)) | k2_partfun1(D_3554, B_3558, F_3559, k9_subset_1(A_3555, C_3557, D_3554))!=k2_partfun1(C_3557, B_3558, E_3556, k9_subset_1(A_3555, C_3557, D_3554)) | ~m1_subset_1(F_3559, k1_zfmisc_1(k2_zfmisc_1(D_3554, B_3558))) | ~v1_funct_2(F_3559, D_3554, B_3558) | ~v1_funct_1(F_3559) | ~m1_subset_1(E_3556, k1_zfmisc_1(k2_zfmisc_1(C_3557, B_3558))) | ~v1_funct_2(E_3556, C_3557, B_3558) | ~v1_funct_1(E_3556) | ~m1_subset_1(D_3554, k1_zfmisc_1(A_3555)) | v1_xboole_0(D_3554) | ~m1_subset_1(C_3557, k1_zfmisc_1(A_3555)) | v1_xboole_0(C_3557) | v1_xboole_0(B_3558) | v1_xboole_0(A_3555))), inference(cnfTransformation, [status(thm)], [f_188])).
% 30.48/20.22  tff(c_146287, plain, (![B_3731, A_3734, F_3735, D_3733, C_3736, E_3732]: (k2_partfun1(k4_subset_1(A_3734, C_3736, D_3733), B_3731, k1_tmap_1(A_3734, B_3731, C_3736, D_3733, E_3732, F_3735), C_3736)=E_3732 | ~v1_funct_2(k1_tmap_1(A_3734, B_3731, C_3736, D_3733, E_3732, F_3735), k4_subset_1(A_3734, C_3736, D_3733), B_3731) | ~v1_funct_1(k1_tmap_1(A_3734, B_3731, C_3736, D_3733, E_3732, F_3735)) | k2_partfun1(D_3733, B_3731, F_3735, k9_subset_1(A_3734, C_3736, D_3733))!=k2_partfun1(C_3736, B_3731, E_3732, k9_subset_1(A_3734, C_3736, D_3733)) | ~m1_subset_1(F_3735, k1_zfmisc_1(k2_zfmisc_1(D_3733, B_3731))) | ~v1_funct_2(F_3735, D_3733, B_3731) | ~v1_funct_1(F_3735) | ~m1_subset_1(E_3732, k1_zfmisc_1(k2_zfmisc_1(C_3736, B_3731))) | ~v1_funct_2(E_3732, C_3736, B_3731) | ~v1_funct_1(E_3732) | ~m1_subset_1(D_3733, k1_zfmisc_1(A_3734)) | v1_xboole_0(D_3733) | ~m1_subset_1(C_3736, k1_zfmisc_1(A_3734)) | v1_xboole_0(C_3736) | v1_xboole_0(B_3731) | v1_xboole_0(A_3734))), inference(resolution, [status(thm)], [c_62, c_139617])).
% 30.48/20.22  tff(c_155574, plain, (![B_3880, D_3882, A_3883, E_3881, F_3884, C_3885]: (k2_partfun1(k4_subset_1(A_3883, C_3885, D_3882), B_3880, k1_tmap_1(A_3883, B_3880, C_3885, D_3882, E_3881, F_3884), C_3885)=E_3881 | ~v1_funct_1(k1_tmap_1(A_3883, B_3880, C_3885, D_3882, E_3881, F_3884)) | k2_partfun1(D_3882, B_3880, F_3884, k9_subset_1(A_3883, C_3885, D_3882))!=k2_partfun1(C_3885, B_3880, E_3881, k9_subset_1(A_3883, C_3885, D_3882)) | ~m1_subset_1(F_3884, k1_zfmisc_1(k2_zfmisc_1(D_3882, B_3880))) | ~v1_funct_2(F_3884, D_3882, B_3880) | ~v1_funct_1(F_3884) | ~m1_subset_1(E_3881, k1_zfmisc_1(k2_zfmisc_1(C_3885, B_3880))) | ~v1_funct_2(E_3881, C_3885, B_3880) | ~v1_funct_1(E_3881) | ~m1_subset_1(D_3882, k1_zfmisc_1(A_3883)) | v1_xboole_0(D_3882) | ~m1_subset_1(C_3885, k1_zfmisc_1(A_3883)) | v1_xboole_0(C_3885) | v1_xboole_0(B_3880) | v1_xboole_0(A_3883))), inference(resolution, [status(thm)], [c_64, c_146287])).
% 30.48/20.22  tff(c_155580, plain, (![A_3883, C_3885, E_3881]: (k2_partfun1(k4_subset_1(A_3883, C_3885, '#skF_5'), '#skF_3', k1_tmap_1(A_3883, '#skF_3', C_3885, '#skF_5', E_3881, '#skF_7'), C_3885)=E_3881 | ~v1_funct_1(k1_tmap_1(A_3883, '#skF_3', C_3885, '#skF_5', E_3881, '#skF_7')) | k2_partfun1(C_3885, '#skF_3', E_3881, k9_subset_1(A_3883, C_3885, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_3883, C_3885, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3881, k1_zfmisc_1(k2_zfmisc_1(C_3885, '#skF_3'))) | ~v1_funct_2(E_3881, C_3885, '#skF_3') | ~v1_funct_1(E_3881) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3883)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3885, k1_zfmisc_1(A_3883)) | v1_xboole_0(C_3885) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3883))), inference(resolution, [status(thm)], [c_70, c_155574])).
% 30.48/20.22  tff(c_155588, plain, (![A_3883, C_3885, E_3881]: (k2_partfun1(k4_subset_1(A_3883, C_3885, '#skF_5'), '#skF_3', k1_tmap_1(A_3883, '#skF_3', C_3885, '#skF_5', E_3881, '#skF_7'), C_3885)=E_3881 | ~v1_funct_1(k1_tmap_1(A_3883, '#skF_3', C_3885, '#skF_5', E_3881, '#skF_7')) | k2_partfun1(C_3885, '#skF_3', E_3881, k9_subset_1(A_3883, C_3885, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3883, C_3885, '#skF_5')) | ~m1_subset_1(E_3881, k1_zfmisc_1(k2_zfmisc_1(C_3885, '#skF_3'))) | ~v1_funct_2(E_3881, C_3885, '#skF_3') | ~v1_funct_1(E_3881) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3883)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3885, k1_zfmisc_1(A_3883)) | v1_xboole_0(C_3885) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3883))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_138817, c_155580])).
% 30.48/20.22  tff(c_167544, plain, (![A_3988, C_3989, E_3990]: (k2_partfun1(k4_subset_1(A_3988, C_3989, '#skF_5'), '#skF_3', k1_tmap_1(A_3988, '#skF_3', C_3989, '#skF_5', E_3990, '#skF_7'), C_3989)=E_3990 | ~v1_funct_1(k1_tmap_1(A_3988, '#skF_3', C_3989, '#skF_5', E_3990, '#skF_7')) | k2_partfun1(C_3989, '#skF_3', E_3990, k9_subset_1(A_3988, C_3989, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3988, C_3989, '#skF_5')) | ~m1_subset_1(E_3990, k1_zfmisc_1(k2_zfmisc_1(C_3989, '#skF_3'))) | ~v1_funct_2(E_3990, C_3989, '#skF_3') | ~v1_funct_1(E_3990) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3988)) | ~m1_subset_1(C_3989, k1_zfmisc_1(A_3988)) | v1_xboole_0(C_3989) | v1_xboole_0(A_3988))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_155588])).
% 30.48/20.22  tff(c_167549, plain, (![A_3988]: (k2_partfun1(k4_subset_1(A_3988, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3988, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')='#skF_4' | ~v1_funct_1(k1_tmap_1(A_3988, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_4', k9_subset_1(A_3988, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3988, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3988)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3988)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3988))), inference(resolution, [status(thm)], [c_138423, c_167544])).
% 30.48/20.22  tff(c_167557, plain, (![A_3988]: (k2_partfun1(k4_subset_1(A_3988, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3988, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')='#skF_4' | ~v1_funct_1(k1_tmap_1(A_3988, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_3988, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1(A_3988, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3988)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3988)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3988))), inference(demodulation, [status(thm), theory('equality')], [c_138425, c_138424, c_138814, c_167549])).
% 30.48/20.22  tff(c_168734, plain, (![A_3998]: (k2_partfun1(k4_subset_1(A_3998, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3998, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')='#skF_4' | ~v1_funct_1(k1_tmap_1(A_3998, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_3998, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1(A_3998, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3998)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3998)) | v1_xboole_0(A_3998))), inference(negUnitSimplification, [status(thm)], [c_90, c_167557])).
% 30.48/20.22  tff(c_104772, plain, (![B_2648, A_2649]: (k1_relat_1(B_2648)=A_2649 | ~v1_partfun1(B_2648, A_2649) | ~v4_relat_1(B_2648, A_2649) | ~v1_relat_1(B_2648))), inference(cnfTransformation, [status(thm)], [f_134])).
% 30.48/20.22  tff(c_104778, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7162, c_104772])).
% 30.48/20.22  tff(c_104787, plain, ('#skF_6'='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_103658, c_104778])).
% 30.48/20.22  tff(c_104791, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_104787])).
% 30.48/20.22  tff(c_105714, plain, (![C_2714, A_2715, B_2716]: (v1_partfun1(C_2714, A_2715) | ~v1_funct_2(C_2714, A_2715, B_2716) | ~v1_funct_1(C_2714) | ~m1_subset_1(C_2714, k1_zfmisc_1(k2_zfmisc_1(A_2715, B_2716))) | v1_xboole_0(B_2716))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.22  tff(c_105720, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_105714])).
% 30.48/20.22  tff(c_105727, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_105720])).
% 30.48/20.22  tff(c_105729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_104791, c_105727])).
% 30.48/20.22  tff(c_105730, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_104787])).
% 30.48/20.22  tff(c_105749, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_105730, c_105730, c_105730, c_103654])).
% 30.48/20.22  tff(c_104645, plain, (![A_2638, B_2639]: (r1_xboole_0(A_2638, B_2639) | ~r1_subset_1(A_2638, B_2639) | v1_xboole_0(B_2639) | v1_xboole_0(A_2638))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.48/20.22  tff(c_104662, plain, (![A_2638, B_2639]: (k3_xboole_0(A_2638, B_2639)='#skF_6' | ~r1_subset_1(A_2638, B_2639) | v1_xboole_0(B_2639) | v1_xboole_0(A_2638))), inference(resolution, [status(thm)], [c_104645, c_103653])).
% 30.48/20.22  tff(c_106853, plain, (![A_2823, B_2824]: (k3_xboole_0(A_2823, B_2824)='#skF_4' | ~r1_subset_1(A_2823, B_2824) | v1_xboole_0(B_2824) | v1_xboole_0(A_2823))), inference(demodulation, [status(thm), theory('equality')], [c_105730, c_104662])).
% 30.48/20.22  tff(c_106862, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_106853])).
% 30.48/20.22  tff(c_106867, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_106862])).
% 30.48/20.22  tff(c_104781, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7161, c_104772])).
% 30.48/20.22  tff(c_104790, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_104781])).
% 30.48/20.22  tff(c_105926, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_104790])).
% 30.48/20.22  tff(c_106081, plain, (![C_2744, A_2745, B_2746]: (v1_partfun1(C_2744, A_2745) | ~v1_funct_2(C_2744, A_2745, B_2746) | ~v1_funct_1(C_2744) | ~m1_subset_1(C_2744, k1_zfmisc_1(k2_zfmisc_1(A_2745, B_2746))) | v1_xboole_0(B_2746))), inference(cnfTransformation, [status(thm)], [f_126])).
% 30.48/20.22  tff(c_106087, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_106081])).
% 30.48/20.22  tff(c_106094, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_106087])).
% 30.48/20.22  tff(c_106096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_105926, c_106094])).
% 30.48/20.22  tff(c_106097, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_104790])).
% 30.48/20.22  tff(c_103681, plain, (![A_16, B_18]: (k7_relat_1(A_16, B_18)='#skF_6' | ~r1_xboole_0(B_18, k1_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_103635, c_16])).
% 30.48/20.22  tff(c_106433, plain, (![A_2779, B_2780]: (k7_relat_1(A_2779, B_2780)='#skF_4' | ~r1_xboole_0(B_2780, k1_relat_1(A_2779)) | ~v1_relat_1(A_2779))), inference(demodulation, [status(thm), theory('equality')], [c_105730, c_103681])).
% 30.48/20.22  tff(c_106440, plain, (![B_2780]: (k7_relat_1('#skF_7', B_2780)='#skF_4' | ~r1_xboole_0(B_2780, '#skF_5') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_106097, c_106433])).
% 30.48/20.22  tff(c_106472, plain, (![B_2784]: (k7_relat_1('#skF_7', B_2784)='#skF_4' | ~r1_xboole_0(B_2784, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7152, c_106440])).
% 30.48/20.22  tff(c_106484, plain, (![A_25]: (k7_relat_1('#skF_7', A_25)='#skF_4' | ~r1_subset_1(A_25, '#skF_5') | v1_xboole_0('#skF_5') | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_34, c_106472])).
% 30.48/20.22  tff(c_106563, plain, (![A_2792]: (k7_relat_1('#skF_7', A_2792)='#skF_4' | ~r1_subset_1(A_2792, '#skF_5') | v1_xboole_0(A_2792))), inference(negUnitSimplification, [status(thm)], [c_86, c_106484])).
% 30.48/20.22  tff(c_106566, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_106563])).
% 30.48/20.22  tff(c_106569, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_90, c_106566])).
% 30.48/20.22  tff(c_105788, plain, (![A_2717, B_2718, C_2719]: (k9_subset_1(A_2717, B_2718, C_2719)=k3_xboole_0(B_2718, C_2719) | ~m1_subset_1(C_2719, k1_zfmisc_1(A_2717)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 30.48/20.22  tff(c_105796, plain, (![B_2718]: (k9_subset_1('#skF_2', B_2718, '#skF_5')=k3_xboole_0(B_2718, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_105788])).
% 30.48/20.22  tff(c_105763, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105730, c_80])).
% 30.48/20.22  tff(c_105762, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105730, c_78])).
% 30.48/20.22  tff(c_105761, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_105730, c_76])).
% 30.48/20.22  tff(c_106403, plain, (![C_2777, D_2774, F_2776, A_2775, B_2772, E_2773]: (v1_funct_1(k1_tmap_1(A_2775, B_2772, C_2777, D_2774, E_2773, F_2776)) | ~m1_subset_1(F_2776, k1_zfmisc_1(k2_zfmisc_1(D_2774, B_2772))) | ~v1_funct_2(F_2776, D_2774, B_2772) | ~v1_funct_1(F_2776) | ~m1_subset_1(E_2773, k1_zfmisc_1(k2_zfmisc_1(C_2777, B_2772))) | ~v1_funct_2(E_2773, C_2777, B_2772) | ~v1_funct_1(E_2773) | ~m1_subset_1(D_2774, k1_zfmisc_1(A_2775)) | v1_xboole_0(D_2774) | ~m1_subset_1(C_2777, k1_zfmisc_1(A_2775)) | v1_xboole_0(C_2777) | v1_xboole_0(B_2772) | v1_xboole_0(A_2775))), inference(cnfTransformation, [status(thm)], [f_222])).
% 30.48/20.22  tff(c_106407, plain, (![A_2775, C_2777, E_2773]: (v1_funct_1(k1_tmap_1(A_2775, '#skF_3', C_2777, '#skF_5', E_2773, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2773, k1_zfmisc_1(k2_zfmisc_1(C_2777, '#skF_3'))) | ~v1_funct_2(E_2773, C_2777, '#skF_3') | ~v1_funct_1(E_2773) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2775)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2777, k1_zfmisc_1(A_2775)) | v1_xboole_0(C_2777) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2775))), inference(resolution, [status(thm)], [c_70, c_106403])).
% 30.48/20.22  tff(c_106414, plain, (![A_2775, C_2777, E_2773]: (v1_funct_1(k1_tmap_1(A_2775, '#skF_3', C_2777, '#skF_5', E_2773, '#skF_7')) | ~m1_subset_1(E_2773, k1_zfmisc_1(k2_zfmisc_1(C_2777, '#skF_3'))) | ~v1_funct_2(E_2773, C_2777, '#skF_3') | ~v1_funct_1(E_2773) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2775)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2777, k1_zfmisc_1(A_2775)) | v1_xboole_0(C_2777) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2775))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_106407])).
% 30.48/20.22  tff(c_106459, plain, (![A_2781, C_2782, E_2783]: (v1_funct_1(k1_tmap_1(A_2781, '#skF_3', C_2782, '#skF_5', E_2783, '#skF_7')) | ~m1_subset_1(E_2783, k1_zfmisc_1(k2_zfmisc_1(C_2782, '#skF_3'))) | ~v1_funct_2(E_2783, C_2782, '#skF_3') | ~v1_funct_1(E_2783) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2781)) | ~m1_subset_1(C_2782, k1_zfmisc_1(A_2781)) | v1_xboole_0(C_2782) | v1_xboole_0(A_2781))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_106414])).
% 30.48/20.22  tff(c_106461, plain, (![A_2781]: (v1_funct_1(k1_tmap_1(A_2781, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2781)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2781)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2781))), inference(resolution, [status(thm)], [c_105761, c_106459])).
% 30.48/20.22  tff(c_106466, plain, (![A_2781]: (v1_funct_1(k1_tmap_1(A_2781, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2781)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2781)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2781))), inference(demodulation, [status(thm), theory('equality')], [c_105763, c_105762, c_106461])).
% 30.48/20.22  tff(c_106844, plain, (![A_2822]: (v1_funct_1(k1_tmap_1(A_2822, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2822)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2822)) | v1_xboole_0(A_2822))), inference(negUnitSimplification, [status(thm)], [c_90, c_106466])).
% 30.48/20.22  tff(c_106847, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_106844])).
% 30.48/20.22  tff(c_106850, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_106847])).
% 30.48/20.22  tff(c_106851, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_106850])).
% 30.48/20.22  tff(c_106157, plain, (![A_2748, B_2749, C_2750, D_2751]: (k2_partfun1(A_2748, B_2749, C_2750, D_2751)=k7_relat_1(C_2750, D_2751) | ~m1_subset_1(C_2750, k1_zfmisc_1(k2_zfmisc_1(A_2748, B_2749))) | ~v1_funct_1(C_2750))), inference(cnfTransformation, [status(thm)], [f_140])).
% 30.48/20.22  tff(c_106159, plain, (![D_2751]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_2751)=k7_relat_1('#skF_4', D_2751) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_105761, c_106157])).
% 30.48/20.22  tff(c_106164, plain, (![D_2751]: (k2_partfun1('#skF_4', '#skF_3', '#skF_4', D_2751)=k7_relat_1('#skF_4', D_2751))), inference(demodulation, [status(thm), theory('equality')], [c_105763, c_106159])).
% 30.48/20.22  tff(c_106161, plain, (![D_2751]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2751)=k7_relat_1('#skF_7', D_2751) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_106157])).
% 30.48/20.22  tff(c_106167, plain, (![D_2751]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_2751)=k7_relat_1('#skF_7', D_2751))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_106161])).
% 30.48/20.22  tff(c_106887, plain, (![A_2826, F_2830, D_2825, E_2827, B_2829, C_2828]: (k2_partfun1(k4_subset_1(A_2826, C_2828, D_2825), B_2829, k1_tmap_1(A_2826, B_2829, C_2828, D_2825, E_2827, F_2830), D_2825)=F_2830 | ~m1_subset_1(k1_tmap_1(A_2826, B_2829, C_2828, D_2825, E_2827, F_2830), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2826, C_2828, D_2825), B_2829))) | ~v1_funct_2(k1_tmap_1(A_2826, B_2829, C_2828, D_2825, E_2827, F_2830), k4_subset_1(A_2826, C_2828, D_2825), B_2829) | ~v1_funct_1(k1_tmap_1(A_2826, B_2829, C_2828, D_2825, E_2827, F_2830)) | k2_partfun1(D_2825, B_2829, F_2830, k9_subset_1(A_2826, C_2828, D_2825))!=k2_partfun1(C_2828, B_2829, E_2827, k9_subset_1(A_2826, C_2828, D_2825)) | ~m1_subset_1(F_2830, k1_zfmisc_1(k2_zfmisc_1(D_2825, B_2829))) | ~v1_funct_2(F_2830, D_2825, B_2829) | ~v1_funct_1(F_2830) | ~m1_subset_1(E_2827, k1_zfmisc_1(k2_zfmisc_1(C_2828, B_2829))) | ~v1_funct_2(E_2827, C_2828, B_2829) | ~v1_funct_1(E_2827) | ~m1_subset_1(D_2825, k1_zfmisc_1(A_2826)) | v1_xboole_0(D_2825) | ~m1_subset_1(C_2828, k1_zfmisc_1(A_2826)) | v1_xboole_0(C_2828) | v1_xboole_0(B_2829) | v1_xboole_0(A_2826))), inference(cnfTransformation, [status(thm)], [f_188])).
% 30.48/20.22  tff(c_114699, plain, (![A_3018, E_3016, B_3015, C_3020, F_3019, D_3017]: (k2_partfun1(k4_subset_1(A_3018, C_3020, D_3017), B_3015, k1_tmap_1(A_3018, B_3015, C_3020, D_3017, E_3016, F_3019), D_3017)=F_3019 | ~v1_funct_2(k1_tmap_1(A_3018, B_3015, C_3020, D_3017, E_3016, F_3019), k4_subset_1(A_3018, C_3020, D_3017), B_3015) | ~v1_funct_1(k1_tmap_1(A_3018, B_3015, C_3020, D_3017, E_3016, F_3019)) | k2_partfun1(D_3017, B_3015, F_3019, k9_subset_1(A_3018, C_3020, D_3017))!=k2_partfun1(C_3020, B_3015, E_3016, k9_subset_1(A_3018, C_3020, D_3017)) | ~m1_subset_1(F_3019, k1_zfmisc_1(k2_zfmisc_1(D_3017, B_3015))) | ~v1_funct_2(F_3019, D_3017, B_3015) | ~v1_funct_1(F_3019) | ~m1_subset_1(E_3016, k1_zfmisc_1(k2_zfmisc_1(C_3020, B_3015))) | ~v1_funct_2(E_3016, C_3020, B_3015) | ~v1_funct_1(E_3016) | ~m1_subset_1(D_3017, k1_zfmisc_1(A_3018)) | v1_xboole_0(D_3017) | ~m1_subset_1(C_3020, k1_zfmisc_1(A_3018)) | v1_xboole_0(C_3020) | v1_xboole_0(B_3015) | v1_xboole_0(A_3018))), inference(resolution, [status(thm)], [c_62, c_106887])).
% 30.48/20.22  tff(c_123683, plain, (![A_3168, C_3170, F_3169, D_3167, B_3165, E_3166]: (k2_partfun1(k4_subset_1(A_3168, C_3170, D_3167), B_3165, k1_tmap_1(A_3168, B_3165, C_3170, D_3167, E_3166, F_3169), D_3167)=F_3169 | ~v1_funct_1(k1_tmap_1(A_3168, B_3165, C_3170, D_3167, E_3166, F_3169)) | k2_partfun1(D_3167, B_3165, F_3169, k9_subset_1(A_3168, C_3170, D_3167))!=k2_partfun1(C_3170, B_3165, E_3166, k9_subset_1(A_3168, C_3170, D_3167)) | ~m1_subset_1(F_3169, k1_zfmisc_1(k2_zfmisc_1(D_3167, B_3165))) | ~v1_funct_2(F_3169, D_3167, B_3165) | ~v1_funct_1(F_3169) | ~m1_subset_1(E_3166, k1_zfmisc_1(k2_zfmisc_1(C_3170, B_3165))) | ~v1_funct_2(E_3166, C_3170, B_3165) | ~v1_funct_1(E_3166) | ~m1_subset_1(D_3167, k1_zfmisc_1(A_3168)) | v1_xboole_0(D_3167) | ~m1_subset_1(C_3170, k1_zfmisc_1(A_3168)) | v1_xboole_0(C_3170) | v1_xboole_0(B_3165) | v1_xboole_0(A_3168))), inference(resolution, [status(thm)], [c_64, c_114699])).
% 30.48/20.22  tff(c_123689, plain, (![A_3168, C_3170, E_3166]: (k2_partfun1(k4_subset_1(A_3168, C_3170, '#skF_5'), '#skF_3', k1_tmap_1(A_3168, '#skF_3', C_3170, '#skF_5', E_3166, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3168, '#skF_3', C_3170, '#skF_5', E_3166, '#skF_7')) | k2_partfun1(C_3170, '#skF_3', E_3166, k9_subset_1(A_3168, C_3170, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_3168, C_3170, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_3166, k1_zfmisc_1(k2_zfmisc_1(C_3170, '#skF_3'))) | ~v1_funct_2(E_3166, C_3170, '#skF_3') | ~v1_funct_1(E_3166) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3168)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3170, k1_zfmisc_1(A_3168)) | v1_xboole_0(C_3170) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3168))), inference(resolution, [status(thm)], [c_70, c_123683])).
% 30.48/20.22  tff(c_123697, plain, (![A_3168, C_3170, E_3166]: (k2_partfun1(k4_subset_1(A_3168, C_3170, '#skF_5'), '#skF_3', k1_tmap_1(A_3168, '#skF_3', C_3170, '#skF_5', E_3166, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3168, '#skF_3', C_3170, '#skF_5', E_3166, '#skF_7')) | k2_partfun1(C_3170, '#skF_3', E_3166, k9_subset_1(A_3168, C_3170, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3168, C_3170, '#skF_5')) | ~m1_subset_1(E_3166, k1_zfmisc_1(k2_zfmisc_1(C_3170, '#skF_3'))) | ~v1_funct_2(E_3166, C_3170, '#skF_3') | ~v1_funct_1(E_3166) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3168)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_3170, k1_zfmisc_1(A_3168)) | v1_xboole_0(C_3170) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3168))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_106167, c_123689])).
% 30.48/20.22  tff(c_134880, plain, (![A_3257, C_3258, E_3259]: (k2_partfun1(k4_subset_1(A_3257, C_3258, '#skF_5'), '#skF_3', k1_tmap_1(A_3257, '#skF_3', C_3258, '#skF_5', E_3259, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3257, '#skF_3', C_3258, '#skF_5', E_3259, '#skF_7')) | k2_partfun1(C_3258, '#skF_3', E_3259, k9_subset_1(A_3257, C_3258, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3257, C_3258, '#skF_5')) | ~m1_subset_1(E_3259, k1_zfmisc_1(k2_zfmisc_1(C_3258, '#skF_3'))) | ~v1_funct_2(E_3259, C_3258, '#skF_3') | ~v1_funct_1(E_3259) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3257)) | ~m1_subset_1(C_3258, k1_zfmisc_1(A_3257)) | v1_xboole_0(C_3258) | v1_xboole_0(A_3257))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_123697])).
% 30.48/20.22  tff(c_134885, plain, (![A_3257]: (k2_partfun1(k4_subset_1(A_3257, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3257, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3257, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_4', k9_subset_1(A_3257, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_3257, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3257)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3257)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3257))), inference(resolution, [status(thm)], [c_105761, c_134880])).
% 30.48/20.22  tff(c_134893, plain, (![A_3257]: (k2_partfun1(k4_subset_1(A_3257, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3257, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3257, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_3257, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1(A_3257, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3257)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3257)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_3257))), inference(demodulation, [status(thm), theory('equality')], [c_105763, c_105762, c_106164, c_134885])).
% 30.48/20.22  tff(c_136073, plain, (![A_3267]: (k2_partfun1(k4_subset_1(A_3267, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_3267, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_3267, '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_3267, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1(A_3267, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_3267)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3267)) | v1_xboole_0(A_3267))), inference(negUnitSimplification, [status(thm)], [c_90, c_134893])).
% 30.48/20.22  tff(c_103665, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_6658])).
% 30.48/20.22  tff(c_105740, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_105730, c_103665])).
% 30.48/20.22  tff(c_136082, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_136073, c_105740])).
% 30.48/20.22  tff(c_136095, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_105749, c_106867, c_106569, c_106867, c_105796, c_105796, c_106851, c_136082])).
% 30.48/20.22  tff(c_136097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_136095])).
% 30.48/20.22  tff(c_136098, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_6658])).
% 30.48/20.22  tff(c_138395, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138391, c_138391, c_136098])).
% 30.48/20.22  tff(c_168743, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_4', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_4', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_168734, c_138395])).
% 30.48/20.22  tff(c_168754, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_138411, c_139596, c_139219, c_139596, c_138473, c_138473, c_139585, c_168743])).
% 30.48/20.22  tff(c_168756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_168754])).
% 30.48/20.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.48/20.22  
% 30.48/20.22  Inference rules
% 30.48/20.22  ----------------------
% 30.48/20.22  #Ref     : 0
% 30.48/20.22  #Sup     : 36777
% 30.48/20.22  #Fact    : 0
% 30.48/20.22  #Define  : 0
% 30.48/20.22  #Split   : 130
% 30.48/20.22  #Chain   : 0
% 30.48/20.22  #Close   : 0
% 30.48/20.22  
% 30.48/20.22  Ordering : KBO
% 30.48/20.22  
% 30.48/20.22  Simplification rules
% 30.48/20.22  ----------------------
% 30.48/20.22  #Subsume      : 6864
% 30.48/20.22  #Demod        : 77194
% 30.48/20.22  #Tautology    : 18451
% 30.48/20.22  #SimpNegUnit  : 972
% 30.48/20.22  #BackRed      : 348
% 30.48/20.22  
% 30.48/20.22  #Partial instantiations: 0
% 30.48/20.22  #Strategies tried      : 1
% 30.48/20.22  
% 30.48/20.22  Timing (in seconds)
% 30.48/20.22  ----------------------
% 30.48/20.22  Preprocessing        : 0.44
% 30.48/20.22  Parsing              : 0.20
% 30.48/20.22  CNF conversion       : 0.07
% 30.48/20.22  Main loop            : 18.85
% 30.48/20.22  Inferencing          : 3.79
% 30.48/20.22  Reduction            : 8.04
% 30.48/20.22  Demodulation         : 6.34
% 30.48/20.22  BG Simplification    : 0.43
% 30.48/20.22  Subsumption          : 5.81
% 30.48/20.22  Abstraction          : 0.65
% 30.48/20.22  MUC search           : 0.00
% 30.48/20.22  Cooper               : 0.00
% 30.48/20.22  Total                : 19.45
% 30.48/20.22  Index Insertion      : 0.00
% 30.48/20.22  Index Deletion       : 0.00
% 30.48/20.22  Index Matching       : 0.00
% 30.48/20.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
