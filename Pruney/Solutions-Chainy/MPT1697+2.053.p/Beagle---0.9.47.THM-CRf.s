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

% Result     : Theorem 12.28s
% Output     : CNFRefutation 12.54s
% Verified   : 
% Statistics : Number of formulae       :  285 (1438 expanded)
%              Number of leaves         :   47 ( 508 expanded)
%              Depth                    :   12
%              Number of atoms          :  863 (6175 expanded)
%              Number of equality atoms :  191 (1180 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_235,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_73,axiom,(
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

tff(f_193,axiom,(
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

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_159,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_98,plain,(
    ! [C_230,A_231,B_232] :
      ( v1_relat_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_98])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_2006,plain,(
    ! [C_416,A_417,B_418] :
      ( v4_relat_1(C_416,A_417)
      | ~ m1_subset_1(C_416,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2032,plain,(
    ! [A_419] : v4_relat_1(k1_xboole_0,A_419) ),
    inference(resolution,[status(thm)],[c_8,c_2006])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2035,plain,(
    ! [A_419] :
      ( k7_relat_1(k1_xboole_0,A_419) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2032,c_14])).

tff(c_2038,plain,(
    ! [A_419] : k7_relat_1(k1_xboole_0,A_419) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2035])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7214,plain,(
    ! [B_937,A_938] :
      ( r1_xboole_0(k1_relat_1(B_937),A_938)
      | k7_relat_1(B_937,A_938) != k1_xboole_0
      | ~ v1_relat_1(B_937) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7227,plain,(
    ! [A_938] :
      ( r1_xboole_0(k1_xboole_0,A_938)
      | k7_relat_1(k1_xboole_0,A_938) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_7214])).

tff(c_7233,plain,(
    ! [A_939] : r1_xboole_0(k1_xboole_0,A_939) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2038,c_7227])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( k7_relat_1(A_10,B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,k1_relat_1(A_10))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7250,plain,(
    ! [A_941] :
      ( k7_relat_1(A_941,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_941) ) ),
    inference(resolution,[status(thm)],[c_7233,c_12])).

tff(c_7263,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_7250])).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_2017,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2006])).

tff(c_7353,plain,(
    ! [B_953,A_954] :
      ( k1_relat_1(B_953) = A_954
      | ~ v1_partfun1(B_953,A_954)
      | ~ v4_relat_1(B_953,A_954)
      | ~ v1_relat_1(B_953) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7362,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2017,c_7353])).

tff(c_7371,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_7362])).

tff(c_7869,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7371])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_8106,plain,(
    ! [C_1018,A_1019,B_1020] :
      ( v1_partfun1(C_1018,A_1019)
      | ~ v1_funct_2(C_1018,A_1019,B_1020)
      | ~ v1_funct_1(C_1018)
      | ~ m1_subset_1(C_1018,k1_zfmisc_1(k2_zfmisc_1(A_1019,B_1020)))
      | v1_xboole_0(B_1020) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8109,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_8106])).

tff(c_8119,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8109])).

tff(c_8121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7869,c_8119])).

tff(c_8122,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7371])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_xboole_0(k1_relat_1(B_16),A_15)
      | k7_relat_1(B_16,A_15) != k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8127,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k7_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8122,c_22])).

tff(c_8219,plain,(
    ! [A_1025] :
      ( r1_xboole_0('#skF_4',A_1025)
      | k7_relat_1('#skF_6',A_1025) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_8127])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_110,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_98])).

tff(c_2018,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2006])).

tff(c_7359,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2018,c_7353])).

tff(c_7368,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_7359])).

tff(c_7378,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7368])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_7813,plain,(
    ! [C_998,A_999,B_1000] :
      ( v1_partfun1(C_998,A_999)
      | ~ v1_funct_2(C_998,A_999,B_1000)
      | ~ v1_funct_1(C_998)
      | ~ m1_subset_1(C_998,k1_zfmisc_1(k2_zfmisc_1(A_999,B_1000)))
      | v1_xboole_0(B_1000) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7819,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_7813])).

tff(c_7830,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_7819])).

tff(c_7832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7378,c_7830])).

tff(c_7833,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7368])).

tff(c_7847,plain,(
    ! [B_12] :
      ( k7_relat_1('#skF_5',B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7833,c_12])).

tff(c_7857,plain,(
    ! [B_12] :
      ( k7_relat_1('#skF_5',B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_7847])).

tff(c_8241,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8219,c_7857])).

tff(c_8319,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8241])).

tff(c_70,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | ~ r1_subset_1(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8136,plain,(
    ! [B_12] :
      ( k7_relat_1('#skF_6',B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8122,c_12])).

tff(c_8171,plain,(
    ! [B_1023] :
      ( k7_relat_1('#skF_6',B_1023) = k1_xboole_0
      | ~ r1_xboole_0(B_1023,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_8136])).

tff(c_8175,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_6',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_8171])).

tff(c_8454,plain,(
    ! [A_1042] :
      ( k7_relat_1('#skF_6',A_1042) = k1_xboole_0
      | ~ r1_subset_1(A_1042,'#skF_4')
      | v1_xboole_0(A_1042) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8175])).

tff(c_8461,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_8454])).

tff(c_8468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8319,c_8461])).

tff(c_8469,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8241])).

tff(c_7838,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k7_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7833,c_22])).

tff(c_8263,plain,(
    ! [A_1027] :
      ( r1_xboole_0('#skF_3',A_1027)
      | k7_relat_1('#skF_5',A_1027) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_7838])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8729,plain,(
    ! [A_1058] :
      ( k3_xboole_0('#skF_3',A_1058) = k1_xboole_0
      | k7_relat_1('#skF_5',A_1058) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8263,c_2])).

tff(c_8746,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8469,c_8729])).

tff(c_7260,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_7250])).

tff(c_7309,plain,(
    ! [A_946,B_947,C_948] :
      ( k9_subset_1(A_946,B_947,C_948) = k3_xboole_0(B_947,C_948)
      | ~ m1_subset_1(C_948,k1_zfmisc_1(A_946)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7323,plain,(
    ! [B_947] : k9_subset_1('#skF_1',B_947,'#skF_4') = k3_xboole_0(B_947,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_7309])).

tff(c_8758,plain,(
    ! [C_1064,D_1061,F_1060,E_1063,B_1059,A_1062] :
      ( v1_funct_1(k1_tmap_1(A_1062,B_1059,C_1064,D_1061,E_1063,F_1060))
      | ~ m1_subset_1(F_1060,k1_zfmisc_1(k2_zfmisc_1(D_1061,B_1059)))
      | ~ v1_funct_2(F_1060,D_1061,B_1059)
      | ~ v1_funct_1(F_1060)
      | ~ m1_subset_1(E_1063,k1_zfmisc_1(k2_zfmisc_1(C_1064,B_1059)))
      | ~ v1_funct_2(E_1063,C_1064,B_1059)
      | ~ v1_funct_1(E_1063)
      | ~ m1_subset_1(D_1061,k1_zfmisc_1(A_1062))
      | v1_xboole_0(D_1061)
      | ~ m1_subset_1(C_1064,k1_zfmisc_1(A_1062))
      | v1_xboole_0(C_1064)
      | v1_xboole_0(B_1059)
      | v1_xboole_0(A_1062) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_8760,plain,(
    ! [A_1062,C_1064,E_1063] :
      ( v1_funct_1(k1_tmap_1(A_1062,'#skF_2',C_1064,'#skF_4',E_1063,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1063,k1_zfmisc_1(k2_zfmisc_1(C_1064,'#skF_2')))
      | ~ v1_funct_2(E_1063,C_1064,'#skF_2')
      | ~ v1_funct_1(E_1063)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1062))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1064,k1_zfmisc_1(A_1062))
      | v1_xboole_0(C_1064)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1062) ) ),
    inference(resolution,[status(thm)],[c_58,c_8758])).

tff(c_8768,plain,(
    ! [A_1062,C_1064,E_1063] :
      ( v1_funct_1(k1_tmap_1(A_1062,'#skF_2',C_1064,'#skF_4',E_1063,'#skF_6'))
      | ~ m1_subset_1(E_1063,k1_zfmisc_1(k2_zfmisc_1(C_1064,'#skF_2')))
      | ~ v1_funct_2(E_1063,C_1064,'#skF_2')
      | ~ v1_funct_1(E_1063)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1062))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1064,k1_zfmisc_1(A_1062))
      | v1_xboole_0(C_1064)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1062) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8760])).

tff(c_9384,plain,(
    ! [A_1117,C_1118,E_1119] :
      ( v1_funct_1(k1_tmap_1(A_1117,'#skF_2',C_1118,'#skF_4',E_1119,'#skF_6'))
      | ~ m1_subset_1(E_1119,k1_zfmisc_1(k2_zfmisc_1(C_1118,'#skF_2')))
      | ~ v1_funct_2(E_1119,C_1118,'#skF_2')
      | ~ v1_funct_1(E_1119)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1117))
      | ~ m1_subset_1(C_1118,k1_zfmisc_1(A_1117))
      | v1_xboole_0(C_1118)
      | v1_xboole_0(A_1117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_8768])).

tff(c_9391,plain,(
    ! [A_1117] :
      ( v1_funct_1(k1_tmap_1(A_1117,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1117))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1117))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1117) ) ),
    inference(resolution,[status(thm)],[c_64,c_9384])).

tff(c_9404,plain,(
    ! [A_1117] :
      ( v1_funct_1(k1_tmap_1(A_1117,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1117))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1117))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_9391])).

tff(c_9414,plain,(
    ! [A_1121] :
      ( v1_funct_1(k1_tmap_1(A_1121,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1121))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1121))
      | v1_xboole_0(A_1121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9404])).

tff(c_9417,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_9414])).

tff(c_9420,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9417])).

tff(c_9421,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_9420])).

tff(c_8505,plain,(
    ! [A_1044,B_1045,C_1046,D_1047] :
      ( k2_partfun1(A_1044,B_1045,C_1046,D_1047) = k7_relat_1(C_1046,D_1047)
      | ~ m1_subset_1(C_1046,k1_zfmisc_1(k2_zfmisc_1(A_1044,B_1045)))
      | ~ v1_funct_1(C_1046) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8509,plain,(
    ! [D_1047] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1047) = k7_relat_1('#skF_5',D_1047)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_8505])).

tff(c_8518,plain,(
    ! [D_1047] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1047) = k7_relat_1('#skF_5',D_1047) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8509])).

tff(c_8507,plain,(
    ! [D_1047] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1047) = k7_relat_1('#skF_6',D_1047)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_8505])).

tff(c_8515,plain,(
    ! [D_1047] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1047) = k7_relat_1('#skF_6',D_1047) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8507])).

tff(c_52,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( v1_funct_2(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k4_subset_1(A_162,C_164,D_165),B_163)
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_50,plain,(
    ! [E_166,F_167,B_163,D_165,A_162,C_164] :
      ( m1_subset_1(k1_tmap_1(A_162,B_163,C_164,D_165,E_166,F_167),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162,C_164,D_165),B_163)))
      | ~ m1_subset_1(F_167,k1_zfmisc_1(k2_zfmisc_1(D_165,B_163)))
      | ~ v1_funct_2(F_167,D_165,B_163)
      | ~ v1_funct_1(F_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(C_164,B_163)))
      | ~ v1_funct_2(E_166,C_164,B_163)
      | ~ v1_funct_1(E_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_162))
      | v1_xboole_0(D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(A_162))
      | v1_xboole_0(C_164)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_9465,plain,(
    ! [A_1132,B_1134,C_1136,F_1131,D_1135,E_1133] :
      ( k2_partfun1(k4_subset_1(A_1132,C_1136,D_1135),B_1134,k1_tmap_1(A_1132,B_1134,C_1136,D_1135,E_1133,F_1131),C_1136) = E_1133
      | ~ m1_subset_1(k1_tmap_1(A_1132,B_1134,C_1136,D_1135,E_1133,F_1131),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1132,C_1136,D_1135),B_1134)))
      | ~ v1_funct_2(k1_tmap_1(A_1132,B_1134,C_1136,D_1135,E_1133,F_1131),k4_subset_1(A_1132,C_1136,D_1135),B_1134)
      | ~ v1_funct_1(k1_tmap_1(A_1132,B_1134,C_1136,D_1135,E_1133,F_1131))
      | k2_partfun1(D_1135,B_1134,F_1131,k9_subset_1(A_1132,C_1136,D_1135)) != k2_partfun1(C_1136,B_1134,E_1133,k9_subset_1(A_1132,C_1136,D_1135))
      | ~ m1_subset_1(F_1131,k1_zfmisc_1(k2_zfmisc_1(D_1135,B_1134)))
      | ~ v1_funct_2(F_1131,D_1135,B_1134)
      | ~ v1_funct_1(F_1131)
      | ~ m1_subset_1(E_1133,k1_zfmisc_1(k2_zfmisc_1(C_1136,B_1134)))
      | ~ v1_funct_2(E_1133,C_1136,B_1134)
      | ~ v1_funct_1(E_1133)
      | ~ m1_subset_1(D_1135,k1_zfmisc_1(A_1132))
      | v1_xboole_0(D_1135)
      | ~ m1_subset_1(C_1136,k1_zfmisc_1(A_1132))
      | v1_xboole_0(C_1136)
      | v1_xboole_0(B_1134)
      | v1_xboole_0(A_1132) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_10110,plain,(
    ! [F_1261,A_1263,D_1262,C_1265,B_1260,E_1264] :
      ( k2_partfun1(k4_subset_1(A_1263,C_1265,D_1262),B_1260,k1_tmap_1(A_1263,B_1260,C_1265,D_1262,E_1264,F_1261),C_1265) = E_1264
      | ~ v1_funct_2(k1_tmap_1(A_1263,B_1260,C_1265,D_1262,E_1264,F_1261),k4_subset_1(A_1263,C_1265,D_1262),B_1260)
      | ~ v1_funct_1(k1_tmap_1(A_1263,B_1260,C_1265,D_1262,E_1264,F_1261))
      | k2_partfun1(D_1262,B_1260,F_1261,k9_subset_1(A_1263,C_1265,D_1262)) != k2_partfun1(C_1265,B_1260,E_1264,k9_subset_1(A_1263,C_1265,D_1262))
      | ~ m1_subset_1(F_1261,k1_zfmisc_1(k2_zfmisc_1(D_1262,B_1260)))
      | ~ v1_funct_2(F_1261,D_1262,B_1260)
      | ~ v1_funct_1(F_1261)
      | ~ m1_subset_1(E_1264,k1_zfmisc_1(k2_zfmisc_1(C_1265,B_1260)))
      | ~ v1_funct_2(E_1264,C_1265,B_1260)
      | ~ v1_funct_1(E_1264)
      | ~ m1_subset_1(D_1262,k1_zfmisc_1(A_1263))
      | v1_xboole_0(D_1262)
      | ~ m1_subset_1(C_1265,k1_zfmisc_1(A_1263))
      | v1_xboole_0(C_1265)
      | v1_xboole_0(B_1260)
      | v1_xboole_0(A_1263) ) ),
    inference(resolution,[status(thm)],[c_50,c_9465])).

tff(c_10707,plain,(
    ! [D_1302,A_1303,E_1304,B_1300,F_1301,C_1305] :
      ( k2_partfun1(k4_subset_1(A_1303,C_1305,D_1302),B_1300,k1_tmap_1(A_1303,B_1300,C_1305,D_1302,E_1304,F_1301),C_1305) = E_1304
      | ~ v1_funct_1(k1_tmap_1(A_1303,B_1300,C_1305,D_1302,E_1304,F_1301))
      | k2_partfun1(D_1302,B_1300,F_1301,k9_subset_1(A_1303,C_1305,D_1302)) != k2_partfun1(C_1305,B_1300,E_1304,k9_subset_1(A_1303,C_1305,D_1302))
      | ~ m1_subset_1(F_1301,k1_zfmisc_1(k2_zfmisc_1(D_1302,B_1300)))
      | ~ v1_funct_2(F_1301,D_1302,B_1300)
      | ~ v1_funct_1(F_1301)
      | ~ m1_subset_1(E_1304,k1_zfmisc_1(k2_zfmisc_1(C_1305,B_1300)))
      | ~ v1_funct_2(E_1304,C_1305,B_1300)
      | ~ v1_funct_1(E_1304)
      | ~ m1_subset_1(D_1302,k1_zfmisc_1(A_1303))
      | v1_xboole_0(D_1302)
      | ~ m1_subset_1(C_1305,k1_zfmisc_1(A_1303))
      | v1_xboole_0(C_1305)
      | v1_xboole_0(B_1300)
      | v1_xboole_0(A_1303) ) ),
    inference(resolution,[status(thm)],[c_52,c_10110])).

tff(c_10711,plain,(
    ! [A_1303,C_1305,E_1304] :
      ( k2_partfun1(k4_subset_1(A_1303,C_1305,'#skF_4'),'#skF_2',k1_tmap_1(A_1303,'#skF_2',C_1305,'#skF_4',E_1304,'#skF_6'),C_1305) = E_1304
      | ~ v1_funct_1(k1_tmap_1(A_1303,'#skF_2',C_1305,'#skF_4',E_1304,'#skF_6'))
      | k2_partfun1(C_1305,'#skF_2',E_1304,k9_subset_1(A_1303,C_1305,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1303,C_1305,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1304,k1_zfmisc_1(k2_zfmisc_1(C_1305,'#skF_2')))
      | ~ v1_funct_2(E_1304,C_1305,'#skF_2')
      | ~ v1_funct_1(E_1304)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1303))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1305,k1_zfmisc_1(A_1303))
      | v1_xboole_0(C_1305)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1303) ) ),
    inference(resolution,[status(thm)],[c_58,c_10707])).

tff(c_10720,plain,(
    ! [A_1303,C_1305,E_1304] :
      ( k2_partfun1(k4_subset_1(A_1303,C_1305,'#skF_4'),'#skF_2',k1_tmap_1(A_1303,'#skF_2',C_1305,'#skF_4',E_1304,'#skF_6'),C_1305) = E_1304
      | ~ v1_funct_1(k1_tmap_1(A_1303,'#skF_2',C_1305,'#skF_4',E_1304,'#skF_6'))
      | k2_partfun1(C_1305,'#skF_2',E_1304,k9_subset_1(A_1303,C_1305,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1303,C_1305,'#skF_4'))
      | ~ m1_subset_1(E_1304,k1_zfmisc_1(k2_zfmisc_1(C_1305,'#skF_2')))
      | ~ v1_funct_2(E_1304,C_1305,'#skF_2')
      | ~ v1_funct_1(E_1304)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1303))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1305,k1_zfmisc_1(A_1303))
      | v1_xboole_0(C_1305)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8515,c_10711])).

tff(c_10735,plain,(
    ! [A_1306,C_1307,E_1308] :
      ( k2_partfun1(k4_subset_1(A_1306,C_1307,'#skF_4'),'#skF_2',k1_tmap_1(A_1306,'#skF_2',C_1307,'#skF_4',E_1308,'#skF_6'),C_1307) = E_1308
      | ~ v1_funct_1(k1_tmap_1(A_1306,'#skF_2',C_1307,'#skF_4',E_1308,'#skF_6'))
      | k2_partfun1(C_1307,'#skF_2',E_1308,k9_subset_1(A_1306,C_1307,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1306,C_1307,'#skF_4'))
      | ~ m1_subset_1(E_1308,k1_zfmisc_1(k2_zfmisc_1(C_1307,'#skF_2')))
      | ~ v1_funct_2(E_1308,C_1307,'#skF_2')
      | ~ v1_funct_1(E_1308)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1306))
      | ~ m1_subset_1(C_1307,k1_zfmisc_1(A_1306))
      | v1_xboole_0(C_1307)
      | v1_xboole_0(A_1306) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_10720])).

tff(c_10742,plain,(
    ! [A_1306] :
      ( k2_partfun1(k4_subset_1(A_1306,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1306,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1306,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1306,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1306,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1306))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1306))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1306) ) ),
    inference(resolution,[status(thm)],[c_64,c_10735])).

tff(c_10755,plain,(
    ! [A_1306] :
      ( k2_partfun1(k4_subset_1(A_1306,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1306,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1306,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1306,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1306,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1306))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1306))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_8518,c_10742])).

tff(c_12577,plain,(
    ! [A_1451] :
      ( k2_partfun1(k4_subset_1(A_1451,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1451,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1451,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1451,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1451,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1451))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1451))
      | v1_xboole_0(A_1451) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_10755])).

tff(c_2112,plain,(
    ! [B_435,A_436] :
      ( r1_xboole_0(k1_relat_1(B_435),A_436)
      | k7_relat_1(B_435,A_436) != k1_xboole_0
      | ~ v1_relat_1(B_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2125,plain,(
    ! [A_436] :
      ( r1_xboole_0(k1_xboole_0,A_436)
      | k7_relat_1(k1_xboole_0,A_436) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2112])).

tff(c_2131,plain,(
    ! [A_437] : r1_xboole_0(k1_xboole_0,A_437) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2038,c_2125])).

tff(c_2148,plain,(
    ! [A_439] :
      ( k7_relat_1(A_439,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_439) ) ),
    inference(resolution,[status(thm)],[c_2131,c_12])).

tff(c_2161,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_2148])).

tff(c_2247,plain,(
    ! [B_451,A_452] :
      ( k1_relat_1(B_451) = A_452
      | ~ v1_partfun1(B_451,A_452)
      | ~ v4_relat_1(B_451,A_452)
      | ~ v1_relat_1(B_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2253,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2018,c_2247])).

tff(c_2262,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2253])).

tff(c_2272,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2262])).

tff(c_2587,plain,(
    ! [C_488,A_489,B_490] :
      ( v1_partfun1(C_488,A_489)
      | ~ v1_funct_2(C_488,A_489,B_490)
      | ~ v1_funct_1(C_488)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(A_489,B_490)))
      | v1_xboole_0(B_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2593,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2587])).

tff(c_2604,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2593])).

tff(c_2606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2272,c_2604])).

tff(c_2607,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2262])).

tff(c_2612,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k7_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2607,c_22])).

tff(c_2908,plain,(
    ! [A_511] :
      ( r1_xboole_0('#skF_3',A_511)
      | k7_relat_1('#skF_5',A_511) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2612])).

tff(c_2256,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2017,c_2247])).

tff(c_2265,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2256])).

tff(c_2643,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2265])).

tff(c_2764,plain,(
    ! [C_503,A_504,B_505] :
      ( v1_partfun1(C_503,A_504)
      | ~ v1_funct_2(C_503,A_504,B_505)
      | ~ v1_funct_1(C_503)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_505)))
      | v1_xboole_0(B_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2767,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2764])).

tff(c_2777,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2767])).

tff(c_2779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2643,c_2777])).

tff(c_2780,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2265])).

tff(c_2794,plain,(
    ! [B_12] :
      ( k7_relat_1('#skF_6',B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2780,c_12])).

tff(c_2804,plain,(
    ! [B_12] :
      ( k7_relat_1('#skF_6',B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2794])).

tff(c_2927,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2908,c_2804])).

tff(c_2988,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2927])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2618,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_5',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2607,c_20])).

tff(c_2951,plain,(
    ! [A_516] :
      ( k7_relat_1('#skF_5',A_516) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_516) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2618])).

tff(c_2958,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_2951])).

tff(c_3123,plain,(
    ! [B_533] :
      ( k7_relat_1('#skF_5',B_533) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_533)
      | v1_xboole_0(B_533) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2958])).

tff(c_3126,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3123])).

tff(c_3130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2988,c_3126])).

tff(c_3132,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2927])).

tff(c_3193,plain,(
    ! [A_538] :
      ( k3_xboole_0('#skF_3',A_538) = k1_xboole_0
      | k7_relat_1('#skF_5',A_538) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2908,c_2])).

tff(c_3207,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3132,c_3193])).

tff(c_2158,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_2148])).

tff(c_2203,plain,(
    ! [A_444,B_445,C_446] :
      ( k9_subset_1(A_444,B_445,C_446) = k3_xboole_0(B_445,C_446)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(A_444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2217,plain,(
    ! [B_445] : k9_subset_1('#skF_1',B_445,'#skF_4') = k3_xboole_0(B_445,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2203])).

tff(c_3252,plain,(
    ! [B_541,C_546,D_543,A_544,E_545,F_542] :
      ( v1_funct_1(k1_tmap_1(A_544,B_541,C_546,D_543,E_545,F_542))
      | ~ m1_subset_1(F_542,k1_zfmisc_1(k2_zfmisc_1(D_543,B_541)))
      | ~ v1_funct_2(F_542,D_543,B_541)
      | ~ v1_funct_1(F_542)
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(C_546,B_541)))
      | ~ v1_funct_2(E_545,C_546,B_541)
      | ~ v1_funct_1(E_545)
      | ~ m1_subset_1(D_543,k1_zfmisc_1(A_544))
      | v1_xboole_0(D_543)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(A_544))
      | v1_xboole_0(C_546)
      | v1_xboole_0(B_541)
      | v1_xboole_0(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_3254,plain,(
    ! [A_544,C_546,E_545] :
      ( v1_funct_1(k1_tmap_1(A_544,'#skF_2',C_546,'#skF_4',E_545,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(C_546,'#skF_2')))
      | ~ v1_funct_2(E_545,C_546,'#skF_2')
      | ~ v1_funct_1(E_545)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_544))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_546,k1_zfmisc_1(A_544))
      | v1_xboole_0(C_546)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_544) ) ),
    inference(resolution,[status(thm)],[c_58,c_3252])).

tff(c_3262,plain,(
    ! [A_544,C_546,E_545] :
      ( v1_funct_1(k1_tmap_1(A_544,'#skF_2',C_546,'#skF_4',E_545,'#skF_6'))
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(C_546,'#skF_2')))
      | ~ v1_funct_2(E_545,C_546,'#skF_2')
      | ~ v1_funct_1(E_545)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_544))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_546,k1_zfmisc_1(A_544))
      | v1_xboole_0(C_546)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_544) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3254])).

tff(c_3712,plain,(
    ! [A_580,C_581,E_582] :
      ( v1_funct_1(k1_tmap_1(A_580,'#skF_2',C_581,'#skF_4',E_582,'#skF_6'))
      | ~ m1_subset_1(E_582,k1_zfmisc_1(k2_zfmisc_1(C_581,'#skF_2')))
      | ~ v1_funct_2(E_582,C_581,'#skF_2')
      | ~ v1_funct_1(E_582)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_580))
      | ~ m1_subset_1(C_581,k1_zfmisc_1(A_580))
      | v1_xboole_0(C_581)
      | v1_xboole_0(A_580) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_3262])).

tff(c_3719,plain,(
    ! [A_580] :
      ( v1_funct_1(k1_tmap_1(A_580,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_580))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_580))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_580) ) ),
    inference(resolution,[status(thm)],[c_64,c_3712])).

tff(c_3732,plain,(
    ! [A_580] :
      ( v1_funct_1(k1_tmap_1(A_580,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_580))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_580))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_580) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3719])).

tff(c_4037,plain,(
    ! [A_608] :
      ( v1_funct_1(k1_tmap_1(A_608,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_608))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_608))
      | v1_xboole_0(A_608) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3732])).

tff(c_4040,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_4037])).

tff(c_4043,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4040])).

tff(c_4044,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4043])).

tff(c_2935,plain,(
    ! [A_512,B_513,C_514,D_515] :
      ( k2_partfun1(A_512,B_513,C_514,D_515) = k7_relat_1(C_514,D_515)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_512,B_513)))
      | ~ v1_funct_1(C_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2939,plain,(
    ! [D_515] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_515) = k7_relat_1('#skF_5',D_515)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_2935])).

tff(c_2948,plain,(
    ! [D_515] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_515) = k7_relat_1('#skF_5',D_515) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2939])).

tff(c_2937,plain,(
    ! [D_515] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_515) = k7_relat_1('#skF_6',D_515)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_2935])).

tff(c_2945,plain,(
    ! [D_515] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_515) = k7_relat_1('#skF_6',D_515) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2937])).

tff(c_3867,plain,(
    ! [F_587,A_588,B_590,C_592,E_589,D_591] :
      ( k2_partfun1(k4_subset_1(A_588,C_592,D_591),B_590,k1_tmap_1(A_588,B_590,C_592,D_591,E_589,F_587),D_591) = F_587
      | ~ m1_subset_1(k1_tmap_1(A_588,B_590,C_592,D_591,E_589,F_587),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_588,C_592,D_591),B_590)))
      | ~ v1_funct_2(k1_tmap_1(A_588,B_590,C_592,D_591,E_589,F_587),k4_subset_1(A_588,C_592,D_591),B_590)
      | ~ v1_funct_1(k1_tmap_1(A_588,B_590,C_592,D_591,E_589,F_587))
      | k2_partfun1(D_591,B_590,F_587,k9_subset_1(A_588,C_592,D_591)) != k2_partfun1(C_592,B_590,E_589,k9_subset_1(A_588,C_592,D_591))
      | ~ m1_subset_1(F_587,k1_zfmisc_1(k2_zfmisc_1(D_591,B_590)))
      | ~ v1_funct_2(F_587,D_591,B_590)
      | ~ v1_funct_1(F_587)
      | ~ m1_subset_1(E_589,k1_zfmisc_1(k2_zfmisc_1(C_592,B_590)))
      | ~ v1_funct_2(E_589,C_592,B_590)
      | ~ v1_funct_1(E_589)
      | ~ m1_subset_1(D_591,k1_zfmisc_1(A_588))
      | v1_xboole_0(D_591)
      | ~ m1_subset_1(C_592,k1_zfmisc_1(A_588))
      | v1_xboole_0(C_592)
      | v1_xboole_0(B_590)
      | v1_xboole_0(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4959,plain,(
    ! [A_745,D_744,C_747,F_743,B_742,E_746] :
      ( k2_partfun1(k4_subset_1(A_745,C_747,D_744),B_742,k1_tmap_1(A_745,B_742,C_747,D_744,E_746,F_743),D_744) = F_743
      | ~ v1_funct_2(k1_tmap_1(A_745,B_742,C_747,D_744,E_746,F_743),k4_subset_1(A_745,C_747,D_744),B_742)
      | ~ v1_funct_1(k1_tmap_1(A_745,B_742,C_747,D_744,E_746,F_743))
      | k2_partfun1(D_744,B_742,F_743,k9_subset_1(A_745,C_747,D_744)) != k2_partfun1(C_747,B_742,E_746,k9_subset_1(A_745,C_747,D_744))
      | ~ m1_subset_1(F_743,k1_zfmisc_1(k2_zfmisc_1(D_744,B_742)))
      | ~ v1_funct_2(F_743,D_744,B_742)
      | ~ v1_funct_1(F_743)
      | ~ m1_subset_1(E_746,k1_zfmisc_1(k2_zfmisc_1(C_747,B_742)))
      | ~ v1_funct_2(E_746,C_747,B_742)
      | ~ v1_funct_1(E_746)
      | ~ m1_subset_1(D_744,k1_zfmisc_1(A_745))
      | v1_xboole_0(D_744)
      | ~ m1_subset_1(C_747,k1_zfmisc_1(A_745))
      | v1_xboole_0(C_747)
      | v1_xboole_0(B_742)
      | v1_xboole_0(A_745) ) ),
    inference(resolution,[status(thm)],[c_50,c_3867])).

tff(c_5345,plain,(
    ! [D_794,B_792,E_796,C_797,A_795,F_793] :
      ( k2_partfun1(k4_subset_1(A_795,C_797,D_794),B_792,k1_tmap_1(A_795,B_792,C_797,D_794,E_796,F_793),D_794) = F_793
      | ~ v1_funct_1(k1_tmap_1(A_795,B_792,C_797,D_794,E_796,F_793))
      | k2_partfun1(D_794,B_792,F_793,k9_subset_1(A_795,C_797,D_794)) != k2_partfun1(C_797,B_792,E_796,k9_subset_1(A_795,C_797,D_794))
      | ~ m1_subset_1(F_793,k1_zfmisc_1(k2_zfmisc_1(D_794,B_792)))
      | ~ v1_funct_2(F_793,D_794,B_792)
      | ~ v1_funct_1(F_793)
      | ~ m1_subset_1(E_796,k1_zfmisc_1(k2_zfmisc_1(C_797,B_792)))
      | ~ v1_funct_2(E_796,C_797,B_792)
      | ~ v1_funct_1(E_796)
      | ~ m1_subset_1(D_794,k1_zfmisc_1(A_795))
      | v1_xboole_0(D_794)
      | ~ m1_subset_1(C_797,k1_zfmisc_1(A_795))
      | v1_xboole_0(C_797)
      | v1_xboole_0(B_792)
      | v1_xboole_0(A_795) ) ),
    inference(resolution,[status(thm)],[c_52,c_4959])).

tff(c_5349,plain,(
    ! [A_795,C_797,E_796] :
      ( k2_partfun1(k4_subset_1(A_795,C_797,'#skF_4'),'#skF_2',k1_tmap_1(A_795,'#skF_2',C_797,'#skF_4',E_796,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_795,'#skF_2',C_797,'#skF_4',E_796,'#skF_6'))
      | k2_partfun1(C_797,'#skF_2',E_796,k9_subset_1(A_795,C_797,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_795,C_797,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_796,k1_zfmisc_1(k2_zfmisc_1(C_797,'#skF_2')))
      | ~ v1_funct_2(E_796,C_797,'#skF_2')
      | ~ v1_funct_1(E_796)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_795))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_797,k1_zfmisc_1(A_795))
      | v1_xboole_0(C_797)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_795) ) ),
    inference(resolution,[status(thm)],[c_58,c_5345])).

tff(c_5358,plain,(
    ! [A_795,C_797,E_796] :
      ( k2_partfun1(k4_subset_1(A_795,C_797,'#skF_4'),'#skF_2',k1_tmap_1(A_795,'#skF_2',C_797,'#skF_4',E_796,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_795,'#skF_2',C_797,'#skF_4',E_796,'#skF_6'))
      | k2_partfun1(C_797,'#skF_2',E_796,k9_subset_1(A_795,C_797,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_795,C_797,'#skF_4'))
      | ~ m1_subset_1(E_796,k1_zfmisc_1(k2_zfmisc_1(C_797,'#skF_2')))
      | ~ v1_funct_2(E_796,C_797,'#skF_2')
      | ~ v1_funct_1(E_796)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_795))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_797,k1_zfmisc_1(A_795))
      | v1_xboole_0(C_797)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_795) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2945,c_5349])).

tff(c_5761,plain,(
    ! [A_840,C_841,E_842] :
      ( k2_partfun1(k4_subset_1(A_840,C_841,'#skF_4'),'#skF_2',k1_tmap_1(A_840,'#skF_2',C_841,'#skF_4',E_842,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_840,'#skF_2',C_841,'#skF_4',E_842,'#skF_6'))
      | k2_partfun1(C_841,'#skF_2',E_842,k9_subset_1(A_840,C_841,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_840,C_841,'#skF_4'))
      | ~ m1_subset_1(E_842,k1_zfmisc_1(k2_zfmisc_1(C_841,'#skF_2')))
      | ~ v1_funct_2(E_842,C_841,'#skF_2')
      | ~ v1_funct_1(E_842)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_840))
      | ~ m1_subset_1(C_841,k1_zfmisc_1(A_840))
      | v1_xboole_0(C_841)
      | v1_xboole_0(A_840) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_5358])).

tff(c_5768,plain,(
    ! [A_840] :
      ( k2_partfun1(k4_subset_1(A_840,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_840,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_840,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_840,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_840,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_840))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_840))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_840) ) ),
    inference(resolution,[status(thm)],[c_64,c_5761])).

tff(c_5781,plain,(
    ! [A_840] :
      ( k2_partfun1(k4_subset_1(A_840,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_840,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_840,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_840,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_840,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_840))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_840))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_840) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2948,c_5768])).

tff(c_7184,plain,(
    ! [A_936] :
      ( k2_partfun1(k4_subset_1(A_936,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_936,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_936,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_936,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_936,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_936))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_936))
      | v1_xboole_0(A_936) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5781])).

tff(c_127,plain,(
    ! [C_236,A_237,B_238] :
      ( v4_relat_1(C_236,A_237)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_140,plain,(
    ! [A_237] : v4_relat_1(k1_xboole_0,A_237) ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_143,plain,(
    ! [B_241,A_242] :
      ( k7_relat_1(B_241,A_242) = B_241
      | ~ v4_relat_1(B_241,A_242)
      | ~ v1_relat_1(B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,(
    ! [A_237] :
      ( k7_relat_1(k1_xboole_0,A_237) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_140,c_143])).

tff(c_155,plain,(
    ! [A_237] : k7_relat_1(k1_xboole_0,A_237) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_146])).

tff(c_254,plain,(
    ! [B_257,A_258] :
      ( r1_xboole_0(k1_relat_1(B_257),A_258)
      | k7_relat_1(B_257,A_258) != k1_xboole_0
      | ~ v1_relat_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_270,plain,(
    ! [A_258] :
      ( r1_xboole_0(k1_xboole_0,A_258)
      | k7_relat_1(k1_xboole_0,A_258) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_254])).

tff(c_277,plain,(
    ! [A_259] : r1_xboole_0(k1_xboole_0,A_259) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_155,c_270])).

tff(c_300,plain,(
    ! [A_264] :
      ( k7_relat_1(A_264,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_264) ) ),
    inference(resolution,[status(thm)],[c_277,c_12])).

tff(c_313,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_300])).

tff(c_139,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_127])).

tff(c_387,plain,(
    ! [B_276,A_277] :
      ( k1_relat_1(B_276) = A_277
      | ~ v1_partfun1(B_276,A_277)
      | ~ v4_relat_1(B_276,A_277)
      | ~ v1_relat_1(B_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_393,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_139,c_387])).

tff(c_402,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_393])).

tff(c_428,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_585,plain,(
    ! [C_295,A_296,B_297] :
      ( v1_partfun1(C_295,A_296)
      | ~ v1_funct_2(C_295,A_296,B_297)
      | ~ v1_funct_1(C_295)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297)))
      | v1_xboole_0(B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_591,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_585])).

tff(c_602,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_591])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_428,c_602])).

tff(c_605,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_610,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k7_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_22])).

tff(c_849,plain,(
    ! [A_310] :
      ( r1_xboole_0('#skF_3',A_310)
      | k7_relat_1('#skF_5',A_310) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_610])).

tff(c_138,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_127])).

tff(c_396,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_138,c_387])).

tff(c_405,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_396])).

tff(c_641,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_705,plain,(
    ! [C_302,A_303,B_304] :
      ( v1_partfun1(C_302,A_303)
      | ~ v1_funct_2(C_302,A_303,B_304)
      | ~ v1_funct_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304)))
      | v1_xboole_0(B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_708,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_705])).

tff(c_718,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_708])).

tff(c_720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_641,c_718])).

tff(c_721,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_735,plain,(
    ! [B_12] :
      ( k7_relat_1('#skF_6',B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_12])).

tff(c_745,plain,(
    ! [B_12] :
      ( k7_relat_1('#skF_6',B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_735])).

tff(c_868,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_849,c_745])).

tff(c_915,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_726,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k7_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_22])).

tff(c_794,plain,(
    ! [A_308] :
      ( r1_xboole_0('#skF_4',A_308)
      | k7_relat_1('#skF_6',A_308) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_726])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r1_subset_1(A_17,B_18)
      | ~ r1_xboole_0(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_804,plain,(
    ! [A_308] :
      ( r1_subset_1('#skF_4',A_308)
      | v1_xboole_0(A_308)
      | v1_xboole_0('#skF_4')
      | k7_relat_1('#skF_6',A_308) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_794,c_24])).

tff(c_816,plain,(
    ! [A_308] :
      ( r1_subset_1('#skF_4',A_308)
      | v1_xboole_0(A_308)
      | k7_relat_1('#skF_6',A_308) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_804])).

tff(c_619,plain,(
    ! [B_12] :
      ( k7_relat_1('#skF_5',B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_12])).

tff(c_757,plain,(
    ! [B_306] :
      ( k7_relat_1('#skF_5',B_306) = k1_xboole_0
      | ~ r1_xboole_0(B_306,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_619])).

tff(c_769,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_5',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_757])).

tff(c_1022,plain,(
    ! [A_333] :
      ( k7_relat_1('#skF_5',A_333) = k1_xboole_0
      | ~ r1_subset_1(A_333,'#skF_3')
      | v1_xboole_0(A_333) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_769])).

tff(c_1030,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_816,c_1022])).

tff(c_1036,plain,(
    k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_74,c_915,c_1030])).

tff(c_819,plain,(
    ! [B_309] :
      ( k7_relat_1('#skF_6',B_309) = k1_xboole_0
      | ~ r1_xboole_0(B_309,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_735])).

tff(c_835,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_6',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_819])).

tff(c_1177,plain,(
    ! [A_344] :
      ( k7_relat_1('#skF_6',A_344) = k1_xboole_0
      | ~ r1_subset_1(A_344,'#skF_4')
      | v1_xboole_0(A_344) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_835])).

tff(c_1188,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1177])).

tff(c_1197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1036,c_1188])).

tff(c_1199,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_1325,plain,(
    ! [A_361] :
      ( k3_xboole_0('#skF_3',A_361) = k1_xboole_0
      | k7_relat_1('#skF_5',A_361) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_849,c_2])).

tff(c_1339,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1199,c_1325])).

tff(c_310,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_300])).

tff(c_412,plain,(
    ! [A_279,B_280,C_281,D_282] :
      ( k2_partfun1(A_279,B_280,C_281,D_282) = k7_relat_1(C_281,D_282)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280)))
      | ~ v1_funct_1(C_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_416,plain,(
    ! [D_282] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_282) = k7_relat_1('#skF_5',D_282)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_412])).

tff(c_425,plain,(
    ! [D_282] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_282) = k7_relat_1('#skF_5',D_282) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_416])).

tff(c_414,plain,(
    ! [D_282] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_282) = k7_relat_1('#skF_6',D_282)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_412])).

tff(c_422,plain,(
    ! [D_282] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_282) = k7_relat_1('#skF_6',D_282) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_414])).

tff(c_323,plain,(
    ! [A_265,B_266,C_267] :
      ( k9_subset_1(A_265,B_266,C_267) = k3_xboole_0(B_266,C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(A_265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_337,plain,(
    ! [B_266] : k9_subset_1('#skF_1',B_266,'#skF_4') = k3_xboole_0(B_266,'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_323])).

tff(c_56,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_112,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_348,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_337,c_112])).

tff(c_1983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_1339,c_310,c_1339,c_425,c_422,c_348])).

tff(c_1984,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2111,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1984])).

tff(c_7195,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7184,c_2111])).

tff(c_7209,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_2161,c_3207,c_2158,c_3207,c_2217,c_2217,c_4044,c_7195])).

tff(c_7211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7209])).

tff(c_7212,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1984])).

tff(c_12586,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12577,c_7212])).

tff(c_12597,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_7263,c_8746,c_7260,c_8746,c_7323,c_7323,c_9421,c_12586])).

tff(c_12599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_12597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n021.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 14:52:34 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.28/4.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.28/4.62  
% 12.28/4.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.28/4.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.28/4.62  
% 12.28/4.62  %Foreground sorts:
% 12.28/4.62  
% 12.28/4.62  
% 12.28/4.62  %Background operators:
% 12.28/4.62  
% 12.28/4.62  
% 12.28/4.62  %Foreground operators:
% 12.28/4.62  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 12.28/4.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.28/4.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.28/4.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.28/4.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.28/4.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.28/4.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.28/4.62  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.28/4.62  tff('#skF_5', type, '#skF_5': $i).
% 12.28/4.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.28/4.62  tff('#skF_6', type, '#skF_6': $i).
% 12.28/4.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.28/4.62  tff('#skF_2', type, '#skF_2': $i).
% 12.28/4.62  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.28/4.62  tff('#skF_3', type, '#skF_3': $i).
% 12.28/4.62  tff('#skF_1', type, '#skF_1': $i).
% 12.28/4.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.28/4.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.28/4.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.28/4.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.28/4.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.28/4.62  tff('#skF_4', type, '#skF_4': $i).
% 12.28/4.62  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.28/4.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.28/4.62  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.28/4.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.28/4.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.28/4.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.28/4.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.28/4.62  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 12.28/4.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.28/4.62  
% 12.54/4.66  tff(f_235, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 12.54/4.66  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.54/4.66  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 12.54/4.66  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.54/4.66  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 12.54/4.66  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 12.54/4.66  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 12.54/4.66  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 12.54/4.66  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 12.54/4.66  tff(f_97, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 12.54/4.66  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 12.54/4.66  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.54/4.66  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 12.54/4.66  tff(f_193, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 12.54/4.66  tff(f_111, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 12.54/4.66  tff(f_159, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 12.54/4.66  tff(c_82, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_98, plain, (![C_230, A_231, B_232]: (v1_relat_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.54/4.66  tff(c_109, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_98])).
% 12.54/4.66  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.54/4.66  tff(c_111, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_98])).
% 12.54/4.66  tff(c_2006, plain, (![C_416, A_417, B_418]: (v4_relat_1(C_416, A_417) | ~m1_subset_1(C_416, k1_zfmisc_1(k2_zfmisc_1(A_417, B_418))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.54/4.66  tff(c_2032, plain, (![A_419]: (v4_relat_1(k1_xboole_0, A_419))), inference(resolution, [status(thm)], [c_8, c_2006])).
% 12.54/4.66  tff(c_14, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.54/4.66  tff(c_2035, plain, (![A_419]: (k7_relat_1(k1_xboole_0, A_419)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2032, c_14])).
% 12.54/4.66  tff(c_2038, plain, (![A_419]: (k7_relat_1(k1_xboole_0, A_419)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2035])).
% 12.54/4.66  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.54/4.66  tff(c_7214, plain, (![B_937, A_938]: (r1_xboole_0(k1_relat_1(B_937), A_938) | k7_relat_1(B_937, A_938)!=k1_xboole_0 | ~v1_relat_1(B_937))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.54/4.66  tff(c_7227, plain, (![A_938]: (r1_xboole_0(k1_xboole_0, A_938) | k7_relat_1(k1_xboole_0, A_938)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_7214])).
% 12.54/4.66  tff(c_7233, plain, (![A_939]: (r1_xboole_0(k1_xboole_0, A_939))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2038, c_7227])).
% 12.54/4.66  tff(c_12, plain, (![A_10, B_12]: (k7_relat_1(A_10, B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, k1_relat_1(A_10)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.54/4.66  tff(c_7250, plain, (![A_941]: (k7_relat_1(A_941, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_941))), inference(resolution, [status(thm)], [c_7233, c_12])).
% 12.54/4.66  tff(c_7263, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_7250])).
% 12.54/4.66  tff(c_78, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_80, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_2017, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_2006])).
% 12.54/4.66  tff(c_7353, plain, (![B_953, A_954]: (k1_relat_1(B_953)=A_954 | ~v1_partfun1(B_953, A_954) | ~v4_relat_1(B_953, A_954) | ~v1_relat_1(B_953))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.54/4.66  tff(c_7362, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2017, c_7353])).
% 12.54/4.66  tff(c_7371, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_7362])).
% 12.54/4.66  tff(c_7869, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_7371])).
% 12.54/4.66  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_8106, plain, (![C_1018, A_1019, B_1020]: (v1_partfun1(C_1018, A_1019) | ~v1_funct_2(C_1018, A_1019, B_1020) | ~v1_funct_1(C_1018) | ~m1_subset_1(C_1018, k1_zfmisc_1(k2_zfmisc_1(A_1019, B_1020))) | v1_xboole_0(B_1020))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.54/4.66  tff(c_8109, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_8106])).
% 12.54/4.66  tff(c_8119, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8109])).
% 12.54/4.66  tff(c_8121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_7869, c_8119])).
% 12.54/4.66  tff(c_8122, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_7371])).
% 12.54/4.66  tff(c_22, plain, (![B_16, A_15]: (r1_xboole_0(k1_relat_1(B_16), A_15) | k7_relat_1(B_16, A_15)!=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.54/4.66  tff(c_8127, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k7_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8122, c_22])).
% 12.54/4.66  tff(c_8219, plain, (![A_1025]: (r1_xboole_0('#skF_4', A_1025) | k7_relat_1('#skF_6', A_1025)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_8127])).
% 12.54/4.66  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_110, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_98])).
% 12.54/4.66  tff(c_2018, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_2006])).
% 12.54/4.66  tff(c_7359, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2018, c_7353])).
% 12.54/4.66  tff(c_7368, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_7359])).
% 12.54/4.66  tff(c_7378, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_7368])).
% 12.54/4.66  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_7813, plain, (![C_998, A_999, B_1000]: (v1_partfun1(C_998, A_999) | ~v1_funct_2(C_998, A_999, B_1000) | ~v1_funct_1(C_998) | ~m1_subset_1(C_998, k1_zfmisc_1(k2_zfmisc_1(A_999, B_1000))) | v1_xboole_0(B_1000))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.54/4.66  tff(c_7819, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_7813])).
% 12.54/4.66  tff(c_7830, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_7819])).
% 12.54/4.66  tff(c_7832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_7378, c_7830])).
% 12.54/4.66  tff(c_7833, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_7368])).
% 12.54/4.66  tff(c_7847, plain, (![B_12]: (k7_relat_1('#skF_5', B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7833, c_12])).
% 12.54/4.66  tff(c_7857, plain, (![B_12]: (k7_relat_1('#skF_5', B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_7847])).
% 12.54/4.66  tff(c_8241, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8219, c_7857])).
% 12.54/4.66  tff(c_8319, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8241])).
% 12.54/4.66  tff(c_70, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_26, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | ~r1_subset_1(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.54/4.66  tff(c_8136, plain, (![B_12]: (k7_relat_1('#skF_6', B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8122, c_12])).
% 12.54/4.66  tff(c_8171, plain, (![B_1023]: (k7_relat_1('#skF_6', B_1023)=k1_xboole_0 | ~r1_xboole_0(B_1023, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_8136])).
% 12.54/4.66  tff(c_8175, plain, (![A_17]: (k7_relat_1('#skF_6', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_26, c_8171])).
% 12.54/4.66  tff(c_8454, plain, (![A_1042]: (k7_relat_1('#skF_6', A_1042)=k1_xboole_0 | ~r1_subset_1(A_1042, '#skF_4') | v1_xboole_0(A_1042))), inference(negUnitSimplification, [status(thm)], [c_74, c_8175])).
% 12.54/4.66  tff(c_8461, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_8454])).
% 12.54/4.66  tff(c_8468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_8319, c_8461])).
% 12.54/4.66  tff(c_8469, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8241])).
% 12.54/4.66  tff(c_7838, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k7_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7833, c_22])).
% 12.54/4.66  tff(c_8263, plain, (![A_1027]: (r1_xboole_0('#skF_3', A_1027) | k7_relat_1('#skF_5', A_1027)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_7838])).
% 12.54/4.66  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.54/4.66  tff(c_8729, plain, (![A_1058]: (k3_xboole_0('#skF_3', A_1058)=k1_xboole_0 | k7_relat_1('#skF_5', A_1058)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8263, c_2])).
% 12.54/4.66  tff(c_8746, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8469, c_8729])).
% 12.54/4.66  tff(c_7260, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_7250])).
% 12.54/4.66  tff(c_7309, plain, (![A_946, B_947, C_948]: (k9_subset_1(A_946, B_947, C_948)=k3_xboole_0(B_947, C_948) | ~m1_subset_1(C_948, k1_zfmisc_1(A_946)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.54/4.66  tff(c_7323, plain, (![B_947]: (k9_subset_1('#skF_1', B_947, '#skF_4')=k3_xboole_0(B_947, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_7309])).
% 12.54/4.66  tff(c_8758, plain, (![C_1064, D_1061, F_1060, E_1063, B_1059, A_1062]: (v1_funct_1(k1_tmap_1(A_1062, B_1059, C_1064, D_1061, E_1063, F_1060)) | ~m1_subset_1(F_1060, k1_zfmisc_1(k2_zfmisc_1(D_1061, B_1059))) | ~v1_funct_2(F_1060, D_1061, B_1059) | ~v1_funct_1(F_1060) | ~m1_subset_1(E_1063, k1_zfmisc_1(k2_zfmisc_1(C_1064, B_1059))) | ~v1_funct_2(E_1063, C_1064, B_1059) | ~v1_funct_1(E_1063) | ~m1_subset_1(D_1061, k1_zfmisc_1(A_1062)) | v1_xboole_0(D_1061) | ~m1_subset_1(C_1064, k1_zfmisc_1(A_1062)) | v1_xboole_0(C_1064) | v1_xboole_0(B_1059) | v1_xboole_0(A_1062))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.54/4.66  tff(c_8760, plain, (![A_1062, C_1064, E_1063]: (v1_funct_1(k1_tmap_1(A_1062, '#skF_2', C_1064, '#skF_4', E_1063, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1063, k1_zfmisc_1(k2_zfmisc_1(C_1064, '#skF_2'))) | ~v1_funct_2(E_1063, C_1064, '#skF_2') | ~v1_funct_1(E_1063) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1062)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1064, k1_zfmisc_1(A_1062)) | v1_xboole_0(C_1064) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1062))), inference(resolution, [status(thm)], [c_58, c_8758])).
% 12.54/4.66  tff(c_8768, plain, (![A_1062, C_1064, E_1063]: (v1_funct_1(k1_tmap_1(A_1062, '#skF_2', C_1064, '#skF_4', E_1063, '#skF_6')) | ~m1_subset_1(E_1063, k1_zfmisc_1(k2_zfmisc_1(C_1064, '#skF_2'))) | ~v1_funct_2(E_1063, C_1064, '#skF_2') | ~v1_funct_1(E_1063) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1062)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1064, k1_zfmisc_1(A_1062)) | v1_xboole_0(C_1064) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1062))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8760])).
% 12.54/4.66  tff(c_9384, plain, (![A_1117, C_1118, E_1119]: (v1_funct_1(k1_tmap_1(A_1117, '#skF_2', C_1118, '#skF_4', E_1119, '#skF_6')) | ~m1_subset_1(E_1119, k1_zfmisc_1(k2_zfmisc_1(C_1118, '#skF_2'))) | ~v1_funct_2(E_1119, C_1118, '#skF_2') | ~v1_funct_1(E_1119) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1117)) | ~m1_subset_1(C_1118, k1_zfmisc_1(A_1117)) | v1_xboole_0(C_1118) | v1_xboole_0(A_1117))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_8768])).
% 12.54/4.66  tff(c_9391, plain, (![A_1117]: (v1_funct_1(k1_tmap_1(A_1117, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1117)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1117)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1117))), inference(resolution, [status(thm)], [c_64, c_9384])).
% 12.54/4.66  tff(c_9404, plain, (![A_1117]: (v1_funct_1(k1_tmap_1(A_1117, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1117)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1117)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1117))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_9391])).
% 12.54/4.66  tff(c_9414, plain, (![A_1121]: (v1_funct_1(k1_tmap_1(A_1121, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1121)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1121)) | v1_xboole_0(A_1121))), inference(negUnitSimplification, [status(thm)], [c_78, c_9404])).
% 12.54/4.66  tff(c_9417, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_9414])).
% 12.54/4.66  tff(c_9420, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9417])).
% 12.54/4.66  tff(c_9421, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_9420])).
% 12.54/4.66  tff(c_8505, plain, (![A_1044, B_1045, C_1046, D_1047]: (k2_partfun1(A_1044, B_1045, C_1046, D_1047)=k7_relat_1(C_1046, D_1047) | ~m1_subset_1(C_1046, k1_zfmisc_1(k2_zfmisc_1(A_1044, B_1045))) | ~v1_funct_1(C_1046))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.54/4.66  tff(c_8509, plain, (![D_1047]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1047)=k7_relat_1('#skF_5', D_1047) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_8505])).
% 12.54/4.66  tff(c_8518, plain, (![D_1047]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1047)=k7_relat_1('#skF_5', D_1047))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8509])).
% 12.54/4.66  tff(c_8507, plain, (![D_1047]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1047)=k7_relat_1('#skF_6', D_1047) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_8505])).
% 12.54/4.66  tff(c_8515, plain, (![D_1047]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1047)=k7_relat_1('#skF_6', D_1047))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_8507])).
% 12.54/4.66  tff(c_52, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (v1_funct_2(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k4_subset_1(A_162, C_164, D_165), B_163) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.54/4.66  tff(c_50, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (m1_subset_1(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162, C_164, D_165), B_163))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.54/4.66  tff(c_9465, plain, (![A_1132, B_1134, C_1136, F_1131, D_1135, E_1133]: (k2_partfun1(k4_subset_1(A_1132, C_1136, D_1135), B_1134, k1_tmap_1(A_1132, B_1134, C_1136, D_1135, E_1133, F_1131), C_1136)=E_1133 | ~m1_subset_1(k1_tmap_1(A_1132, B_1134, C_1136, D_1135, E_1133, F_1131), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1132, C_1136, D_1135), B_1134))) | ~v1_funct_2(k1_tmap_1(A_1132, B_1134, C_1136, D_1135, E_1133, F_1131), k4_subset_1(A_1132, C_1136, D_1135), B_1134) | ~v1_funct_1(k1_tmap_1(A_1132, B_1134, C_1136, D_1135, E_1133, F_1131)) | k2_partfun1(D_1135, B_1134, F_1131, k9_subset_1(A_1132, C_1136, D_1135))!=k2_partfun1(C_1136, B_1134, E_1133, k9_subset_1(A_1132, C_1136, D_1135)) | ~m1_subset_1(F_1131, k1_zfmisc_1(k2_zfmisc_1(D_1135, B_1134))) | ~v1_funct_2(F_1131, D_1135, B_1134) | ~v1_funct_1(F_1131) | ~m1_subset_1(E_1133, k1_zfmisc_1(k2_zfmisc_1(C_1136, B_1134))) | ~v1_funct_2(E_1133, C_1136, B_1134) | ~v1_funct_1(E_1133) | ~m1_subset_1(D_1135, k1_zfmisc_1(A_1132)) | v1_xboole_0(D_1135) | ~m1_subset_1(C_1136, k1_zfmisc_1(A_1132)) | v1_xboole_0(C_1136) | v1_xboole_0(B_1134) | v1_xboole_0(A_1132))), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.54/4.66  tff(c_10110, plain, (![F_1261, A_1263, D_1262, C_1265, B_1260, E_1264]: (k2_partfun1(k4_subset_1(A_1263, C_1265, D_1262), B_1260, k1_tmap_1(A_1263, B_1260, C_1265, D_1262, E_1264, F_1261), C_1265)=E_1264 | ~v1_funct_2(k1_tmap_1(A_1263, B_1260, C_1265, D_1262, E_1264, F_1261), k4_subset_1(A_1263, C_1265, D_1262), B_1260) | ~v1_funct_1(k1_tmap_1(A_1263, B_1260, C_1265, D_1262, E_1264, F_1261)) | k2_partfun1(D_1262, B_1260, F_1261, k9_subset_1(A_1263, C_1265, D_1262))!=k2_partfun1(C_1265, B_1260, E_1264, k9_subset_1(A_1263, C_1265, D_1262)) | ~m1_subset_1(F_1261, k1_zfmisc_1(k2_zfmisc_1(D_1262, B_1260))) | ~v1_funct_2(F_1261, D_1262, B_1260) | ~v1_funct_1(F_1261) | ~m1_subset_1(E_1264, k1_zfmisc_1(k2_zfmisc_1(C_1265, B_1260))) | ~v1_funct_2(E_1264, C_1265, B_1260) | ~v1_funct_1(E_1264) | ~m1_subset_1(D_1262, k1_zfmisc_1(A_1263)) | v1_xboole_0(D_1262) | ~m1_subset_1(C_1265, k1_zfmisc_1(A_1263)) | v1_xboole_0(C_1265) | v1_xboole_0(B_1260) | v1_xboole_0(A_1263))), inference(resolution, [status(thm)], [c_50, c_9465])).
% 12.54/4.66  tff(c_10707, plain, (![D_1302, A_1303, E_1304, B_1300, F_1301, C_1305]: (k2_partfun1(k4_subset_1(A_1303, C_1305, D_1302), B_1300, k1_tmap_1(A_1303, B_1300, C_1305, D_1302, E_1304, F_1301), C_1305)=E_1304 | ~v1_funct_1(k1_tmap_1(A_1303, B_1300, C_1305, D_1302, E_1304, F_1301)) | k2_partfun1(D_1302, B_1300, F_1301, k9_subset_1(A_1303, C_1305, D_1302))!=k2_partfun1(C_1305, B_1300, E_1304, k9_subset_1(A_1303, C_1305, D_1302)) | ~m1_subset_1(F_1301, k1_zfmisc_1(k2_zfmisc_1(D_1302, B_1300))) | ~v1_funct_2(F_1301, D_1302, B_1300) | ~v1_funct_1(F_1301) | ~m1_subset_1(E_1304, k1_zfmisc_1(k2_zfmisc_1(C_1305, B_1300))) | ~v1_funct_2(E_1304, C_1305, B_1300) | ~v1_funct_1(E_1304) | ~m1_subset_1(D_1302, k1_zfmisc_1(A_1303)) | v1_xboole_0(D_1302) | ~m1_subset_1(C_1305, k1_zfmisc_1(A_1303)) | v1_xboole_0(C_1305) | v1_xboole_0(B_1300) | v1_xboole_0(A_1303))), inference(resolution, [status(thm)], [c_52, c_10110])).
% 12.54/4.66  tff(c_10711, plain, (![A_1303, C_1305, E_1304]: (k2_partfun1(k4_subset_1(A_1303, C_1305, '#skF_4'), '#skF_2', k1_tmap_1(A_1303, '#skF_2', C_1305, '#skF_4', E_1304, '#skF_6'), C_1305)=E_1304 | ~v1_funct_1(k1_tmap_1(A_1303, '#skF_2', C_1305, '#skF_4', E_1304, '#skF_6')) | k2_partfun1(C_1305, '#skF_2', E_1304, k9_subset_1(A_1303, C_1305, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1303, C_1305, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1304, k1_zfmisc_1(k2_zfmisc_1(C_1305, '#skF_2'))) | ~v1_funct_2(E_1304, C_1305, '#skF_2') | ~v1_funct_1(E_1304) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1303)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1305, k1_zfmisc_1(A_1303)) | v1_xboole_0(C_1305) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1303))), inference(resolution, [status(thm)], [c_58, c_10707])).
% 12.54/4.66  tff(c_10720, plain, (![A_1303, C_1305, E_1304]: (k2_partfun1(k4_subset_1(A_1303, C_1305, '#skF_4'), '#skF_2', k1_tmap_1(A_1303, '#skF_2', C_1305, '#skF_4', E_1304, '#skF_6'), C_1305)=E_1304 | ~v1_funct_1(k1_tmap_1(A_1303, '#skF_2', C_1305, '#skF_4', E_1304, '#skF_6')) | k2_partfun1(C_1305, '#skF_2', E_1304, k9_subset_1(A_1303, C_1305, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1303, C_1305, '#skF_4')) | ~m1_subset_1(E_1304, k1_zfmisc_1(k2_zfmisc_1(C_1305, '#skF_2'))) | ~v1_funct_2(E_1304, C_1305, '#skF_2') | ~v1_funct_1(E_1304) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1303)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1305, k1_zfmisc_1(A_1303)) | v1_xboole_0(C_1305) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1303))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_8515, c_10711])).
% 12.54/4.66  tff(c_10735, plain, (![A_1306, C_1307, E_1308]: (k2_partfun1(k4_subset_1(A_1306, C_1307, '#skF_4'), '#skF_2', k1_tmap_1(A_1306, '#skF_2', C_1307, '#skF_4', E_1308, '#skF_6'), C_1307)=E_1308 | ~v1_funct_1(k1_tmap_1(A_1306, '#skF_2', C_1307, '#skF_4', E_1308, '#skF_6')) | k2_partfun1(C_1307, '#skF_2', E_1308, k9_subset_1(A_1306, C_1307, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1306, C_1307, '#skF_4')) | ~m1_subset_1(E_1308, k1_zfmisc_1(k2_zfmisc_1(C_1307, '#skF_2'))) | ~v1_funct_2(E_1308, C_1307, '#skF_2') | ~v1_funct_1(E_1308) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1306)) | ~m1_subset_1(C_1307, k1_zfmisc_1(A_1306)) | v1_xboole_0(C_1307) | v1_xboole_0(A_1306))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_10720])).
% 12.54/4.66  tff(c_10742, plain, (![A_1306]: (k2_partfun1(k4_subset_1(A_1306, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1306, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1306, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1306, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1306, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1306)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1306)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1306))), inference(resolution, [status(thm)], [c_64, c_10735])).
% 12.54/4.66  tff(c_10755, plain, (![A_1306]: (k2_partfun1(k4_subset_1(A_1306, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1306, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1306, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1306, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1306, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1306)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1306)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1306))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_8518, c_10742])).
% 12.54/4.66  tff(c_12577, plain, (![A_1451]: (k2_partfun1(k4_subset_1(A_1451, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1451, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1451, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1451, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1451, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1451)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1451)) | v1_xboole_0(A_1451))), inference(negUnitSimplification, [status(thm)], [c_78, c_10755])).
% 12.54/4.66  tff(c_2112, plain, (![B_435, A_436]: (r1_xboole_0(k1_relat_1(B_435), A_436) | k7_relat_1(B_435, A_436)!=k1_xboole_0 | ~v1_relat_1(B_435))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.54/4.66  tff(c_2125, plain, (![A_436]: (r1_xboole_0(k1_xboole_0, A_436) | k7_relat_1(k1_xboole_0, A_436)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2112])).
% 12.54/4.66  tff(c_2131, plain, (![A_437]: (r1_xboole_0(k1_xboole_0, A_437))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2038, c_2125])).
% 12.54/4.66  tff(c_2148, plain, (![A_439]: (k7_relat_1(A_439, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_439))), inference(resolution, [status(thm)], [c_2131, c_12])).
% 12.54/4.66  tff(c_2161, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_2148])).
% 12.54/4.66  tff(c_2247, plain, (![B_451, A_452]: (k1_relat_1(B_451)=A_452 | ~v1_partfun1(B_451, A_452) | ~v4_relat_1(B_451, A_452) | ~v1_relat_1(B_451))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.54/4.66  tff(c_2253, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2018, c_2247])).
% 12.54/4.66  tff(c_2262, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2253])).
% 12.54/4.66  tff(c_2272, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_2262])).
% 12.54/4.66  tff(c_2587, plain, (![C_488, A_489, B_490]: (v1_partfun1(C_488, A_489) | ~v1_funct_2(C_488, A_489, B_490) | ~v1_funct_1(C_488) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(A_489, B_490))) | v1_xboole_0(B_490))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.54/4.66  tff(c_2593, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2587])).
% 12.54/4.66  tff(c_2604, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2593])).
% 12.54/4.66  tff(c_2606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2272, c_2604])).
% 12.54/4.66  tff(c_2607, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_2262])).
% 12.54/4.66  tff(c_2612, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k7_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2607, c_22])).
% 12.54/4.66  tff(c_2908, plain, (![A_511]: (r1_xboole_0('#skF_3', A_511) | k7_relat_1('#skF_5', A_511)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2612])).
% 12.54/4.66  tff(c_2256, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2017, c_2247])).
% 12.54/4.66  tff(c_2265, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2256])).
% 12.54/4.66  tff(c_2643, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2265])).
% 12.54/4.66  tff(c_2764, plain, (![C_503, A_504, B_505]: (v1_partfun1(C_503, A_504) | ~v1_funct_2(C_503, A_504, B_505) | ~v1_funct_1(C_503) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_505))) | v1_xboole_0(B_505))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.54/4.66  tff(c_2767, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_2764])).
% 12.54/4.66  tff(c_2777, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2767])).
% 12.54/4.66  tff(c_2779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2643, c_2777])).
% 12.54/4.66  tff(c_2780, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_2265])).
% 12.54/4.66  tff(c_2794, plain, (![B_12]: (k7_relat_1('#skF_6', B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2780, c_12])).
% 12.54/4.66  tff(c_2804, plain, (![B_12]: (k7_relat_1('#skF_6', B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2794])).
% 12.54/4.66  tff(c_2927, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2908, c_2804])).
% 12.54/4.66  tff(c_2988, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2927])).
% 12.54/4.66  tff(c_20, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.54/4.66  tff(c_2618, plain, (![A_15]: (k7_relat_1('#skF_5', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2607, c_20])).
% 12.54/4.66  tff(c_2951, plain, (![A_516]: (k7_relat_1('#skF_5', A_516)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_516))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2618])).
% 12.54/4.66  tff(c_2958, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_2951])).
% 12.54/4.66  tff(c_3123, plain, (![B_533]: (k7_relat_1('#skF_5', B_533)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_533) | v1_xboole_0(B_533))), inference(negUnitSimplification, [status(thm)], [c_78, c_2958])).
% 12.54/4.66  tff(c_3126, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3123])).
% 12.54/4.66  tff(c_3130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2988, c_3126])).
% 12.54/4.66  tff(c_3132, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2927])).
% 12.54/4.66  tff(c_3193, plain, (![A_538]: (k3_xboole_0('#skF_3', A_538)=k1_xboole_0 | k7_relat_1('#skF_5', A_538)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2908, c_2])).
% 12.54/4.66  tff(c_3207, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3132, c_3193])).
% 12.54/4.66  tff(c_2158, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_2148])).
% 12.54/4.66  tff(c_2203, plain, (![A_444, B_445, C_446]: (k9_subset_1(A_444, B_445, C_446)=k3_xboole_0(B_445, C_446) | ~m1_subset_1(C_446, k1_zfmisc_1(A_444)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.54/4.66  tff(c_2217, plain, (![B_445]: (k9_subset_1('#skF_1', B_445, '#skF_4')=k3_xboole_0(B_445, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_2203])).
% 12.54/4.66  tff(c_3252, plain, (![B_541, C_546, D_543, A_544, E_545, F_542]: (v1_funct_1(k1_tmap_1(A_544, B_541, C_546, D_543, E_545, F_542)) | ~m1_subset_1(F_542, k1_zfmisc_1(k2_zfmisc_1(D_543, B_541))) | ~v1_funct_2(F_542, D_543, B_541) | ~v1_funct_1(F_542) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(C_546, B_541))) | ~v1_funct_2(E_545, C_546, B_541) | ~v1_funct_1(E_545) | ~m1_subset_1(D_543, k1_zfmisc_1(A_544)) | v1_xboole_0(D_543) | ~m1_subset_1(C_546, k1_zfmisc_1(A_544)) | v1_xboole_0(C_546) | v1_xboole_0(B_541) | v1_xboole_0(A_544))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.54/4.66  tff(c_3254, plain, (![A_544, C_546, E_545]: (v1_funct_1(k1_tmap_1(A_544, '#skF_2', C_546, '#skF_4', E_545, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(C_546, '#skF_2'))) | ~v1_funct_2(E_545, C_546, '#skF_2') | ~v1_funct_1(E_545) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_544)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_546, k1_zfmisc_1(A_544)) | v1_xboole_0(C_546) | v1_xboole_0('#skF_2') | v1_xboole_0(A_544))), inference(resolution, [status(thm)], [c_58, c_3252])).
% 12.54/4.66  tff(c_3262, plain, (![A_544, C_546, E_545]: (v1_funct_1(k1_tmap_1(A_544, '#skF_2', C_546, '#skF_4', E_545, '#skF_6')) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(C_546, '#skF_2'))) | ~v1_funct_2(E_545, C_546, '#skF_2') | ~v1_funct_1(E_545) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_544)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_546, k1_zfmisc_1(A_544)) | v1_xboole_0(C_546) | v1_xboole_0('#skF_2') | v1_xboole_0(A_544))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3254])).
% 12.54/4.66  tff(c_3712, plain, (![A_580, C_581, E_582]: (v1_funct_1(k1_tmap_1(A_580, '#skF_2', C_581, '#skF_4', E_582, '#skF_6')) | ~m1_subset_1(E_582, k1_zfmisc_1(k2_zfmisc_1(C_581, '#skF_2'))) | ~v1_funct_2(E_582, C_581, '#skF_2') | ~v1_funct_1(E_582) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_580)) | ~m1_subset_1(C_581, k1_zfmisc_1(A_580)) | v1_xboole_0(C_581) | v1_xboole_0(A_580))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_3262])).
% 12.54/4.66  tff(c_3719, plain, (![A_580]: (v1_funct_1(k1_tmap_1(A_580, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_580)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_580)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_580))), inference(resolution, [status(thm)], [c_64, c_3712])).
% 12.54/4.66  tff(c_3732, plain, (![A_580]: (v1_funct_1(k1_tmap_1(A_580, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_580)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_580)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_580))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3719])).
% 12.54/4.66  tff(c_4037, plain, (![A_608]: (v1_funct_1(k1_tmap_1(A_608, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_608)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_608)) | v1_xboole_0(A_608))), inference(negUnitSimplification, [status(thm)], [c_78, c_3732])).
% 12.54/4.66  tff(c_4040, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_4037])).
% 12.54/4.66  tff(c_4043, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4040])).
% 12.54/4.66  tff(c_4044, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_4043])).
% 12.54/4.66  tff(c_2935, plain, (![A_512, B_513, C_514, D_515]: (k2_partfun1(A_512, B_513, C_514, D_515)=k7_relat_1(C_514, D_515) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_512, B_513))) | ~v1_funct_1(C_514))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.54/4.66  tff(c_2939, plain, (![D_515]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_515)=k7_relat_1('#skF_5', D_515) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_2935])).
% 12.54/4.66  tff(c_2948, plain, (![D_515]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_515)=k7_relat_1('#skF_5', D_515))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2939])).
% 12.54/4.66  tff(c_2937, plain, (![D_515]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_515)=k7_relat_1('#skF_6', D_515) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_2935])).
% 12.54/4.66  tff(c_2945, plain, (![D_515]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_515)=k7_relat_1('#skF_6', D_515))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2937])).
% 12.54/4.66  tff(c_3867, plain, (![F_587, A_588, B_590, C_592, E_589, D_591]: (k2_partfun1(k4_subset_1(A_588, C_592, D_591), B_590, k1_tmap_1(A_588, B_590, C_592, D_591, E_589, F_587), D_591)=F_587 | ~m1_subset_1(k1_tmap_1(A_588, B_590, C_592, D_591, E_589, F_587), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_588, C_592, D_591), B_590))) | ~v1_funct_2(k1_tmap_1(A_588, B_590, C_592, D_591, E_589, F_587), k4_subset_1(A_588, C_592, D_591), B_590) | ~v1_funct_1(k1_tmap_1(A_588, B_590, C_592, D_591, E_589, F_587)) | k2_partfun1(D_591, B_590, F_587, k9_subset_1(A_588, C_592, D_591))!=k2_partfun1(C_592, B_590, E_589, k9_subset_1(A_588, C_592, D_591)) | ~m1_subset_1(F_587, k1_zfmisc_1(k2_zfmisc_1(D_591, B_590))) | ~v1_funct_2(F_587, D_591, B_590) | ~v1_funct_1(F_587) | ~m1_subset_1(E_589, k1_zfmisc_1(k2_zfmisc_1(C_592, B_590))) | ~v1_funct_2(E_589, C_592, B_590) | ~v1_funct_1(E_589) | ~m1_subset_1(D_591, k1_zfmisc_1(A_588)) | v1_xboole_0(D_591) | ~m1_subset_1(C_592, k1_zfmisc_1(A_588)) | v1_xboole_0(C_592) | v1_xboole_0(B_590) | v1_xboole_0(A_588))), inference(cnfTransformation, [status(thm)], [f_159])).
% 12.54/4.66  tff(c_4959, plain, (![A_745, D_744, C_747, F_743, B_742, E_746]: (k2_partfun1(k4_subset_1(A_745, C_747, D_744), B_742, k1_tmap_1(A_745, B_742, C_747, D_744, E_746, F_743), D_744)=F_743 | ~v1_funct_2(k1_tmap_1(A_745, B_742, C_747, D_744, E_746, F_743), k4_subset_1(A_745, C_747, D_744), B_742) | ~v1_funct_1(k1_tmap_1(A_745, B_742, C_747, D_744, E_746, F_743)) | k2_partfun1(D_744, B_742, F_743, k9_subset_1(A_745, C_747, D_744))!=k2_partfun1(C_747, B_742, E_746, k9_subset_1(A_745, C_747, D_744)) | ~m1_subset_1(F_743, k1_zfmisc_1(k2_zfmisc_1(D_744, B_742))) | ~v1_funct_2(F_743, D_744, B_742) | ~v1_funct_1(F_743) | ~m1_subset_1(E_746, k1_zfmisc_1(k2_zfmisc_1(C_747, B_742))) | ~v1_funct_2(E_746, C_747, B_742) | ~v1_funct_1(E_746) | ~m1_subset_1(D_744, k1_zfmisc_1(A_745)) | v1_xboole_0(D_744) | ~m1_subset_1(C_747, k1_zfmisc_1(A_745)) | v1_xboole_0(C_747) | v1_xboole_0(B_742) | v1_xboole_0(A_745))), inference(resolution, [status(thm)], [c_50, c_3867])).
% 12.54/4.66  tff(c_5345, plain, (![D_794, B_792, E_796, C_797, A_795, F_793]: (k2_partfun1(k4_subset_1(A_795, C_797, D_794), B_792, k1_tmap_1(A_795, B_792, C_797, D_794, E_796, F_793), D_794)=F_793 | ~v1_funct_1(k1_tmap_1(A_795, B_792, C_797, D_794, E_796, F_793)) | k2_partfun1(D_794, B_792, F_793, k9_subset_1(A_795, C_797, D_794))!=k2_partfun1(C_797, B_792, E_796, k9_subset_1(A_795, C_797, D_794)) | ~m1_subset_1(F_793, k1_zfmisc_1(k2_zfmisc_1(D_794, B_792))) | ~v1_funct_2(F_793, D_794, B_792) | ~v1_funct_1(F_793) | ~m1_subset_1(E_796, k1_zfmisc_1(k2_zfmisc_1(C_797, B_792))) | ~v1_funct_2(E_796, C_797, B_792) | ~v1_funct_1(E_796) | ~m1_subset_1(D_794, k1_zfmisc_1(A_795)) | v1_xboole_0(D_794) | ~m1_subset_1(C_797, k1_zfmisc_1(A_795)) | v1_xboole_0(C_797) | v1_xboole_0(B_792) | v1_xboole_0(A_795))), inference(resolution, [status(thm)], [c_52, c_4959])).
% 12.54/4.66  tff(c_5349, plain, (![A_795, C_797, E_796]: (k2_partfun1(k4_subset_1(A_795, C_797, '#skF_4'), '#skF_2', k1_tmap_1(A_795, '#skF_2', C_797, '#skF_4', E_796, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_795, '#skF_2', C_797, '#skF_4', E_796, '#skF_6')) | k2_partfun1(C_797, '#skF_2', E_796, k9_subset_1(A_795, C_797, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_795, C_797, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_796, k1_zfmisc_1(k2_zfmisc_1(C_797, '#skF_2'))) | ~v1_funct_2(E_796, C_797, '#skF_2') | ~v1_funct_1(E_796) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_795)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_797, k1_zfmisc_1(A_795)) | v1_xboole_0(C_797) | v1_xboole_0('#skF_2') | v1_xboole_0(A_795))), inference(resolution, [status(thm)], [c_58, c_5345])).
% 12.54/4.66  tff(c_5358, plain, (![A_795, C_797, E_796]: (k2_partfun1(k4_subset_1(A_795, C_797, '#skF_4'), '#skF_2', k1_tmap_1(A_795, '#skF_2', C_797, '#skF_4', E_796, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_795, '#skF_2', C_797, '#skF_4', E_796, '#skF_6')) | k2_partfun1(C_797, '#skF_2', E_796, k9_subset_1(A_795, C_797, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_795, C_797, '#skF_4')) | ~m1_subset_1(E_796, k1_zfmisc_1(k2_zfmisc_1(C_797, '#skF_2'))) | ~v1_funct_2(E_796, C_797, '#skF_2') | ~v1_funct_1(E_796) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_795)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_797, k1_zfmisc_1(A_795)) | v1_xboole_0(C_797) | v1_xboole_0('#skF_2') | v1_xboole_0(A_795))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2945, c_5349])).
% 12.54/4.66  tff(c_5761, plain, (![A_840, C_841, E_842]: (k2_partfun1(k4_subset_1(A_840, C_841, '#skF_4'), '#skF_2', k1_tmap_1(A_840, '#skF_2', C_841, '#skF_4', E_842, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_840, '#skF_2', C_841, '#skF_4', E_842, '#skF_6')) | k2_partfun1(C_841, '#skF_2', E_842, k9_subset_1(A_840, C_841, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_840, C_841, '#skF_4')) | ~m1_subset_1(E_842, k1_zfmisc_1(k2_zfmisc_1(C_841, '#skF_2'))) | ~v1_funct_2(E_842, C_841, '#skF_2') | ~v1_funct_1(E_842) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_840)) | ~m1_subset_1(C_841, k1_zfmisc_1(A_840)) | v1_xboole_0(C_841) | v1_xboole_0(A_840))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_5358])).
% 12.54/4.66  tff(c_5768, plain, (![A_840]: (k2_partfun1(k4_subset_1(A_840, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_840, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_840, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_840, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_840, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_840)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_840)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_840))), inference(resolution, [status(thm)], [c_64, c_5761])).
% 12.54/4.66  tff(c_5781, plain, (![A_840]: (k2_partfun1(k4_subset_1(A_840, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_840, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_840, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_840, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_840, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_840)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_840)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_840))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2948, c_5768])).
% 12.54/4.66  tff(c_7184, plain, (![A_936]: (k2_partfun1(k4_subset_1(A_936, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_936, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_936, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_936, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_936, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_936)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_936)) | v1_xboole_0(A_936))), inference(negUnitSimplification, [status(thm)], [c_78, c_5781])).
% 12.54/4.66  tff(c_127, plain, (![C_236, A_237, B_238]: (v4_relat_1(C_236, A_237) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.54/4.66  tff(c_140, plain, (![A_237]: (v4_relat_1(k1_xboole_0, A_237))), inference(resolution, [status(thm)], [c_8, c_127])).
% 12.54/4.66  tff(c_143, plain, (![B_241, A_242]: (k7_relat_1(B_241, A_242)=B_241 | ~v4_relat_1(B_241, A_242) | ~v1_relat_1(B_241))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.54/4.66  tff(c_146, plain, (![A_237]: (k7_relat_1(k1_xboole_0, A_237)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_140, c_143])).
% 12.54/4.66  tff(c_155, plain, (![A_237]: (k7_relat_1(k1_xboole_0, A_237)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_146])).
% 12.54/4.66  tff(c_254, plain, (![B_257, A_258]: (r1_xboole_0(k1_relat_1(B_257), A_258) | k7_relat_1(B_257, A_258)!=k1_xboole_0 | ~v1_relat_1(B_257))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.54/4.66  tff(c_270, plain, (![A_258]: (r1_xboole_0(k1_xboole_0, A_258) | k7_relat_1(k1_xboole_0, A_258)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_254])).
% 12.54/4.66  tff(c_277, plain, (![A_259]: (r1_xboole_0(k1_xboole_0, A_259))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_155, c_270])).
% 12.54/4.66  tff(c_300, plain, (![A_264]: (k7_relat_1(A_264, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_264))), inference(resolution, [status(thm)], [c_277, c_12])).
% 12.54/4.66  tff(c_313, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_300])).
% 12.54/4.66  tff(c_139, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_127])).
% 12.54/4.66  tff(c_387, plain, (![B_276, A_277]: (k1_relat_1(B_276)=A_277 | ~v1_partfun1(B_276, A_277) | ~v4_relat_1(B_276, A_277) | ~v1_relat_1(B_276))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.54/4.66  tff(c_393, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_139, c_387])).
% 12.54/4.66  tff(c_402, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_393])).
% 12.54/4.66  tff(c_428, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_402])).
% 12.54/4.66  tff(c_585, plain, (![C_295, A_296, B_297]: (v1_partfun1(C_295, A_296) | ~v1_funct_2(C_295, A_296, B_297) | ~v1_funct_1(C_295) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))) | v1_xboole_0(B_297))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.54/4.66  tff(c_591, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_585])).
% 12.54/4.66  tff(c_602, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_591])).
% 12.54/4.66  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_428, c_602])).
% 12.54/4.66  tff(c_605, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_402])).
% 12.54/4.66  tff(c_610, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k7_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_605, c_22])).
% 12.54/4.66  tff(c_849, plain, (![A_310]: (r1_xboole_0('#skF_3', A_310) | k7_relat_1('#skF_5', A_310)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_610])).
% 12.54/4.66  tff(c_138, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_127])).
% 12.54/4.66  tff(c_396, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_138, c_387])).
% 12.54/4.66  tff(c_405, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_396])).
% 12.54/4.66  tff(c_641, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_405])).
% 12.54/4.66  tff(c_705, plain, (![C_302, A_303, B_304]: (v1_partfun1(C_302, A_303) | ~v1_funct_2(C_302, A_303, B_304) | ~v1_funct_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))) | v1_xboole_0(B_304))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.54/4.66  tff(c_708, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_705])).
% 12.54/4.66  tff(c_718, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_708])).
% 12.54/4.66  tff(c_720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_641, c_718])).
% 12.54/4.66  tff(c_721, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_405])).
% 12.54/4.66  tff(c_735, plain, (![B_12]: (k7_relat_1('#skF_6', B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_721, c_12])).
% 12.54/4.66  tff(c_745, plain, (![B_12]: (k7_relat_1('#skF_6', B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_735])).
% 12.54/4.66  tff(c_868, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_849, c_745])).
% 12.54/4.66  tff(c_915, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_868])).
% 12.54/4.66  tff(c_726, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k7_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_721, c_22])).
% 12.54/4.66  tff(c_794, plain, (![A_308]: (r1_xboole_0('#skF_4', A_308) | k7_relat_1('#skF_6', A_308)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_726])).
% 12.54/4.66  tff(c_24, plain, (![A_17, B_18]: (r1_subset_1(A_17, B_18) | ~r1_xboole_0(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.54/4.66  tff(c_804, plain, (![A_308]: (r1_subset_1('#skF_4', A_308) | v1_xboole_0(A_308) | v1_xboole_0('#skF_4') | k7_relat_1('#skF_6', A_308)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_794, c_24])).
% 12.54/4.66  tff(c_816, plain, (![A_308]: (r1_subset_1('#skF_4', A_308) | v1_xboole_0(A_308) | k7_relat_1('#skF_6', A_308)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_74, c_804])).
% 12.54/4.66  tff(c_619, plain, (![B_12]: (k7_relat_1('#skF_5', B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_605, c_12])).
% 12.54/4.66  tff(c_757, plain, (![B_306]: (k7_relat_1('#skF_5', B_306)=k1_xboole_0 | ~r1_xboole_0(B_306, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_619])).
% 12.54/4.66  tff(c_769, plain, (![A_17]: (k7_relat_1('#skF_5', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_26, c_757])).
% 12.54/4.66  tff(c_1022, plain, (![A_333]: (k7_relat_1('#skF_5', A_333)=k1_xboole_0 | ~r1_subset_1(A_333, '#skF_3') | v1_xboole_0(A_333))), inference(negUnitSimplification, [status(thm)], [c_78, c_769])).
% 12.54/4.66  tff(c_1030, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_816, c_1022])).
% 12.54/4.66  tff(c_1036, plain, (k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_78, c_74, c_915, c_1030])).
% 12.54/4.66  tff(c_819, plain, (![B_309]: (k7_relat_1('#skF_6', B_309)=k1_xboole_0 | ~r1_xboole_0(B_309, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_735])).
% 12.54/4.66  tff(c_835, plain, (![A_17]: (k7_relat_1('#skF_6', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_26, c_819])).
% 12.54/4.66  tff(c_1177, plain, (![A_344]: (k7_relat_1('#skF_6', A_344)=k1_xboole_0 | ~r1_subset_1(A_344, '#skF_4') | v1_xboole_0(A_344))), inference(negUnitSimplification, [status(thm)], [c_74, c_835])).
% 12.54/4.66  tff(c_1188, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1177])).
% 12.54/4.66  tff(c_1197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1036, c_1188])).
% 12.54/4.66  tff(c_1199, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_868])).
% 12.54/4.66  tff(c_1325, plain, (![A_361]: (k3_xboole_0('#skF_3', A_361)=k1_xboole_0 | k7_relat_1('#skF_5', A_361)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_849, c_2])).
% 12.54/4.66  tff(c_1339, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1199, c_1325])).
% 12.54/4.66  tff(c_310, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_300])).
% 12.54/4.66  tff(c_412, plain, (![A_279, B_280, C_281, D_282]: (k2_partfun1(A_279, B_280, C_281, D_282)=k7_relat_1(C_281, D_282) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))) | ~v1_funct_1(C_281))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.54/4.66  tff(c_416, plain, (![D_282]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_282)=k7_relat_1('#skF_5', D_282) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_412])).
% 12.54/4.66  tff(c_425, plain, (![D_282]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_282)=k7_relat_1('#skF_5', D_282))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_416])).
% 12.54/4.66  tff(c_414, plain, (![D_282]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_282)=k7_relat_1('#skF_6', D_282) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_58, c_412])).
% 12.54/4.66  tff(c_422, plain, (![D_282]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_282)=k7_relat_1('#skF_6', D_282))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_414])).
% 12.54/4.66  tff(c_323, plain, (![A_265, B_266, C_267]: (k9_subset_1(A_265, B_266, C_267)=k3_xboole_0(B_266, C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(A_265)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.54/4.66  tff(c_337, plain, (![B_266]: (k9_subset_1('#skF_1', B_266, '#skF_4')=k3_xboole_0(B_266, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_323])).
% 12.54/4.66  tff(c_56, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 12.54/4.66  tff(c_112, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_56])).
% 12.54/4.66  tff(c_348, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_337, c_112])).
% 12.54/4.66  tff(c_1983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_1339, c_310, c_1339, c_425, c_422, c_348])).
% 12.54/4.66  tff(c_1984, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_56])).
% 12.54/4.66  tff(c_2111, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1984])).
% 12.54/4.66  tff(c_7195, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7184, c_2111])).
% 12.54/4.66  tff(c_7209, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_2161, c_3207, c_2158, c_3207, c_2217, c_2217, c_4044, c_7195])).
% 12.54/4.66  tff(c_7211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_7209])).
% 12.54/4.66  tff(c_7212, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1984])).
% 12.54/4.66  tff(c_12586, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12577, c_7212])).
% 12.54/4.66  tff(c_12597, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_7263, c_8746, c_7260, c_8746, c_7323, c_7323, c_9421, c_12586])).
% 12.54/4.66  tff(c_12599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_12597])).
% 12.54/4.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.54/4.66  
% 12.54/4.66  Inference rules
% 12.54/4.66  ----------------------
% 12.54/4.66  #Ref     : 0
% 12.54/4.66  #Sup     : 2572
% 12.54/4.66  #Fact    : 0
% 12.54/4.66  #Define  : 0
% 12.54/4.66  #Split   : 74
% 12.54/4.66  #Chain   : 0
% 12.54/4.66  #Close   : 0
% 12.54/4.66  
% 12.54/4.66  Ordering : KBO
% 12.54/4.66  
% 12.54/4.66  Simplification rules
% 12.54/4.66  ----------------------
% 12.54/4.66  #Subsume      : 543
% 12.54/4.66  #Demod        : 1682
% 12.54/4.66  #Tautology    : 1061
% 12.54/4.66  #SimpNegUnit  : 572
% 12.54/4.66  #BackRed      : 5
% 12.54/4.66  
% 12.54/4.66  #Partial instantiations: 0
% 12.54/4.66  #Strategies tried      : 1
% 12.54/4.66  
% 12.54/4.66  Timing (in seconds)
% 12.54/4.66  ----------------------
% 12.54/4.67  Preprocessing        : 0.47
% 12.54/4.67  Parsing              : 0.22
% 12.54/4.67  CNF conversion       : 0.06
% 12.54/4.67  Main loop            : 3.38
% 12.54/4.67  Inferencing          : 1.14
% 12.54/4.67  Reduction            : 1.18
% 12.54/4.67  Demodulation         : 0.88
% 12.54/4.67  BG Simplification    : 0.13
% 12.54/4.67  Subsumption          : 0.72
% 12.54/4.67  Abstraction          : 0.16
% 12.54/4.67  MUC search           : 0.00
% 12.54/4.67  Cooper               : 0.00
% 12.54/4.67  Total                : 3.95
% 12.54/4.67  Index Insertion      : 0.00
% 12.54/4.67  Index Deletion       : 0.00
% 12.54/4.67  Index Matching       : 0.00
% 12.54/4.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
