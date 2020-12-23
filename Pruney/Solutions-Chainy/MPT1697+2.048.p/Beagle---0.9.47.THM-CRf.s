%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:16 EST 2020

% Result     : Theorem 8.91s
% Output     : CNFRefutation 9.32s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 682 expanded)
%              Number of leaves         :   47 ( 261 expanded)
%              Depth                    :   14
%              Number of atoms          :  674 (3479 expanded)
%              Number of equality atoms :  129 ( 643 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_239,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_197,axiom,(
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

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_163,axiom,(
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

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_516,plain,(
    ! [C_313,A_314,B_315] :
      ( v1_relat_1(C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_523,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_516])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6073,plain,(
    ! [B_889,A_890] :
      ( k7_relat_1(B_889,A_890) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_889),A_890)
      | ~ v1_relat_1(B_889) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6098,plain,(
    ! [B_891] :
      ( k7_relat_1(B_891,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_891) ) ),
    inference(resolution,[status(thm)],[c_16,c_6073])).

tff(c_6106,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_523,c_6098])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_72,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | ~ r1_subset_1(A_20,B_21)
      | v1_xboole_0(B_21)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_524,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_516])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_5985,plain,(
    ! [C_875,A_876,B_877] :
      ( v4_relat_1(C_875,A_876)
      | ~ m1_subset_1(C_875,k1_zfmisc_1(k2_zfmisc_1(A_876,B_877))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5993,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_5985])).

tff(c_6217,plain,(
    ! [B_910,A_911] :
      ( k1_relat_1(B_910) = A_911
      | ~ v1_partfun1(B_910,A_911)
      | ~ v4_relat_1(B_910,A_911)
      | ~ v1_relat_1(B_910) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6220,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5993,c_6217])).

tff(c_6226,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_6220])).

tff(c_6230,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6226])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_6596,plain,(
    ! [C_961,A_962,B_963] :
      ( v1_partfun1(C_961,A_962)
      | ~ v1_funct_2(C_961,A_962,B_963)
      | ~ v1_funct_1(C_961)
      | ~ m1_subset_1(C_961,k1_zfmisc_1(k2_zfmisc_1(A_962,B_963)))
      | v1_xboole_0(B_963) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6602,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_6596])).

tff(c_6609,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_6602])).

tff(c_6611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6230,c_6609])).

tff(c_6612,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6226])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6622,plain,(
    ! [A_18] :
      ( k7_relat_1('#skF_7',A_18) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_18)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6612,c_22])).

tff(c_6951,plain,(
    ! [A_996] :
      ( k7_relat_1('#skF_7',A_996) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_996) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_6622])).

tff(c_6955,plain,(
    ! [B_21] :
      ( k7_relat_1('#skF_7',B_21) = k1_xboole_0
      | ~ r1_subset_1('#skF_5',B_21)
      | v1_xboole_0(B_21)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_6951])).

tff(c_7159,plain,(
    ! [B_1013] :
      ( k7_relat_1('#skF_7',B_1013) = k1_xboole_0
      | ~ r1_subset_1('#skF_5',B_1013)
      | v1_xboole_0(B_1013) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6955])).

tff(c_7165,plain,
    ( k7_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_7159])).

tff(c_7169,plain,(
    k7_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7165])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_xboole_0(k1_relat_1(B_19),A_18)
      | k7_relat_1(B_19,A_18) != k1_xboole_0
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6619,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_5',A_18)
      | k7_relat_1('#skF_7',A_18) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6612,c_24])).

tff(c_7027,plain,(
    ! [A_999] :
      ( r1_xboole_0('#skF_5',A_999)
      | k7_relat_1('#skF_7',A_999) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_6619])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7044,plain,(
    ! [A_999] :
      ( k3_xboole_0('#skF_5',A_999) = k1_xboole_0
      | k7_relat_1('#skF_7',A_999) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7027,c_6])).

tff(c_7193,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7169,c_7044])).

tff(c_6105,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_524,c_6098])).

tff(c_7087,plain,(
    ! [A_1002,B_1003,C_1004] :
      ( k9_subset_1(A_1002,B_1003,C_1004) = k3_xboole_0(B_1003,C_1004)
      | ~ m1_subset_1(C_1004,k1_zfmisc_1(A_1002)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7099,plain,(
    ! [B_1003] : k9_subset_1('#skF_3',B_1003,'#skF_6') = k3_xboole_0(B_1003,'#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_7087])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_7395,plain,(
    ! [B_1041,F_1040,E_1042,C_1039,A_1043,D_1044] :
      ( v1_funct_1(k1_tmap_1(A_1043,B_1041,C_1039,D_1044,E_1042,F_1040))
      | ~ m1_subset_1(F_1040,k1_zfmisc_1(k2_zfmisc_1(D_1044,B_1041)))
      | ~ v1_funct_2(F_1040,D_1044,B_1041)
      | ~ v1_funct_1(F_1040)
      | ~ m1_subset_1(E_1042,k1_zfmisc_1(k2_zfmisc_1(C_1039,B_1041)))
      | ~ v1_funct_2(E_1042,C_1039,B_1041)
      | ~ v1_funct_1(E_1042)
      | ~ m1_subset_1(D_1044,k1_zfmisc_1(A_1043))
      | v1_xboole_0(D_1044)
      | ~ m1_subset_1(C_1039,k1_zfmisc_1(A_1043))
      | v1_xboole_0(C_1039)
      | v1_xboole_0(B_1041)
      | v1_xboole_0(A_1043) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_7397,plain,(
    ! [A_1043,C_1039,E_1042] :
      ( v1_funct_1(k1_tmap_1(A_1043,'#skF_4',C_1039,'#skF_6',E_1042,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1042,k1_zfmisc_1(k2_zfmisc_1(C_1039,'#skF_4')))
      | ~ v1_funct_2(E_1042,C_1039,'#skF_4')
      | ~ v1_funct_1(E_1042)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1043))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1039,k1_zfmisc_1(A_1043))
      | v1_xboole_0(C_1039)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1043) ) ),
    inference(resolution,[status(thm)],[c_60,c_7395])).

tff(c_7402,plain,(
    ! [A_1043,C_1039,E_1042] :
      ( v1_funct_1(k1_tmap_1(A_1043,'#skF_4',C_1039,'#skF_6',E_1042,'#skF_8'))
      | ~ m1_subset_1(E_1042,k1_zfmisc_1(k2_zfmisc_1(C_1039,'#skF_4')))
      | ~ v1_funct_2(E_1042,C_1039,'#skF_4')
      | ~ v1_funct_1(E_1042)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1043))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1039,k1_zfmisc_1(A_1043))
      | v1_xboole_0(C_1039)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_7397])).

tff(c_7459,plain,(
    ! [A_1052,C_1053,E_1054] :
      ( v1_funct_1(k1_tmap_1(A_1052,'#skF_4',C_1053,'#skF_6',E_1054,'#skF_8'))
      | ~ m1_subset_1(E_1054,k1_zfmisc_1(k2_zfmisc_1(C_1053,'#skF_4')))
      | ~ v1_funct_2(E_1054,C_1053,'#skF_4')
      | ~ v1_funct_1(E_1054)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1052))
      | ~ m1_subset_1(C_1053,k1_zfmisc_1(A_1052))
      | v1_xboole_0(C_1053)
      | v1_xboole_0(A_1052) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_7402])).

tff(c_7463,plain,(
    ! [A_1052] :
      ( v1_funct_1(k1_tmap_1(A_1052,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1052))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1052))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1052) ) ),
    inference(resolution,[status(thm)],[c_66,c_7459])).

tff(c_7470,plain,(
    ! [A_1052] :
      ( v1_funct_1(k1_tmap_1(A_1052,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1052))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1052))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1052) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_7463])).

tff(c_7841,plain,(
    ! [A_1092] :
      ( v1_funct_1(k1_tmap_1(A_1092,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1092))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1092))
      | v1_xboole_0(A_1092) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7470])).

tff(c_7844,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_7841])).

tff(c_7847,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7844])).

tff(c_7848,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_7847])).

tff(c_7170,plain,(
    ! [A_1014,B_1015,C_1016,D_1017] :
      ( k2_partfun1(A_1014,B_1015,C_1016,D_1017) = k7_relat_1(C_1016,D_1017)
      | ~ m1_subset_1(C_1016,k1_zfmisc_1(k2_zfmisc_1(A_1014,B_1015)))
      | ~ v1_funct_1(C_1016) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7174,plain,(
    ! [D_1017] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_1017) = k7_relat_1('#skF_7',D_1017)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_7170])).

tff(c_7180,plain,(
    ! [D_1017] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_1017) = k7_relat_1('#skF_7',D_1017) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7174])).

tff(c_7172,plain,(
    ! [D_1017] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_1017) = k7_relat_1('#skF_8',D_1017)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_60,c_7170])).

tff(c_7177,plain,(
    ! [D_1017] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_1017) = k7_relat_1('#skF_8',D_1017) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_7172])).

tff(c_54,plain,(
    ! [B_166,F_170,D_168,A_165,E_169,C_167] :
      ( v1_funct_2(k1_tmap_1(A_165,B_166,C_167,D_168,E_169,F_170),k4_subset_1(A_165,C_167,D_168),B_166)
      | ~ m1_subset_1(F_170,k1_zfmisc_1(k2_zfmisc_1(D_168,B_166)))
      | ~ v1_funct_2(F_170,D_168,B_166)
      | ~ v1_funct_1(F_170)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(C_167,B_166)))
      | ~ v1_funct_2(E_169,C_167,B_166)
      | ~ v1_funct_1(E_169)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(A_165))
      | v1_xboole_0(D_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(A_165))
      | v1_xboole_0(C_167)
      | v1_xboole_0(B_166)
      | v1_xboole_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_52,plain,(
    ! [B_166,F_170,D_168,A_165,E_169,C_167] :
      ( m1_subset_1(k1_tmap_1(A_165,B_166,C_167,D_168,E_169,F_170),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_165,C_167,D_168),B_166)))
      | ~ m1_subset_1(F_170,k1_zfmisc_1(k2_zfmisc_1(D_168,B_166)))
      | ~ v1_funct_2(F_170,D_168,B_166)
      | ~ v1_funct_1(F_170)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(C_167,B_166)))
      | ~ v1_funct_2(E_169,C_167,B_166)
      | ~ v1_funct_1(E_169)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(A_165))
      | v1_xboole_0(D_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(A_165))
      | v1_xboole_0(C_167)
      | v1_xboole_0(B_166)
      | v1_xboole_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_7925,plain,(
    ! [E_1101,C_1099,A_1098,F_1102,B_1100,D_1103] :
      ( k2_partfun1(k4_subset_1(A_1098,C_1099,D_1103),B_1100,k1_tmap_1(A_1098,B_1100,C_1099,D_1103,E_1101,F_1102),C_1099) = E_1101
      | ~ m1_subset_1(k1_tmap_1(A_1098,B_1100,C_1099,D_1103,E_1101,F_1102),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1098,C_1099,D_1103),B_1100)))
      | ~ v1_funct_2(k1_tmap_1(A_1098,B_1100,C_1099,D_1103,E_1101,F_1102),k4_subset_1(A_1098,C_1099,D_1103),B_1100)
      | ~ v1_funct_1(k1_tmap_1(A_1098,B_1100,C_1099,D_1103,E_1101,F_1102))
      | k2_partfun1(D_1103,B_1100,F_1102,k9_subset_1(A_1098,C_1099,D_1103)) != k2_partfun1(C_1099,B_1100,E_1101,k9_subset_1(A_1098,C_1099,D_1103))
      | ~ m1_subset_1(F_1102,k1_zfmisc_1(k2_zfmisc_1(D_1103,B_1100)))
      | ~ v1_funct_2(F_1102,D_1103,B_1100)
      | ~ v1_funct_1(F_1102)
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(C_1099,B_1100)))
      | ~ v1_funct_2(E_1101,C_1099,B_1100)
      | ~ v1_funct_1(E_1101)
      | ~ m1_subset_1(D_1103,k1_zfmisc_1(A_1098))
      | v1_xboole_0(D_1103)
      | ~ m1_subset_1(C_1099,k1_zfmisc_1(A_1098))
      | v1_xboole_0(C_1099)
      | v1_xboole_0(B_1100)
      | v1_xboole_0(A_1098) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_9615,plain,(
    ! [F_1297,E_1299,C_1296,B_1298,A_1300,D_1301] :
      ( k2_partfun1(k4_subset_1(A_1300,C_1296,D_1301),B_1298,k1_tmap_1(A_1300,B_1298,C_1296,D_1301,E_1299,F_1297),C_1296) = E_1299
      | ~ v1_funct_2(k1_tmap_1(A_1300,B_1298,C_1296,D_1301,E_1299,F_1297),k4_subset_1(A_1300,C_1296,D_1301),B_1298)
      | ~ v1_funct_1(k1_tmap_1(A_1300,B_1298,C_1296,D_1301,E_1299,F_1297))
      | k2_partfun1(D_1301,B_1298,F_1297,k9_subset_1(A_1300,C_1296,D_1301)) != k2_partfun1(C_1296,B_1298,E_1299,k9_subset_1(A_1300,C_1296,D_1301))
      | ~ m1_subset_1(F_1297,k1_zfmisc_1(k2_zfmisc_1(D_1301,B_1298)))
      | ~ v1_funct_2(F_1297,D_1301,B_1298)
      | ~ v1_funct_1(F_1297)
      | ~ m1_subset_1(E_1299,k1_zfmisc_1(k2_zfmisc_1(C_1296,B_1298)))
      | ~ v1_funct_2(E_1299,C_1296,B_1298)
      | ~ v1_funct_1(E_1299)
      | ~ m1_subset_1(D_1301,k1_zfmisc_1(A_1300))
      | v1_xboole_0(D_1301)
      | ~ m1_subset_1(C_1296,k1_zfmisc_1(A_1300))
      | v1_xboole_0(C_1296)
      | v1_xboole_0(B_1298)
      | v1_xboole_0(A_1300) ) ),
    inference(resolution,[status(thm)],[c_52,c_7925])).

tff(c_10379,plain,(
    ! [B_1354,C_1352,E_1355,F_1353,A_1356,D_1357] :
      ( k2_partfun1(k4_subset_1(A_1356,C_1352,D_1357),B_1354,k1_tmap_1(A_1356,B_1354,C_1352,D_1357,E_1355,F_1353),C_1352) = E_1355
      | ~ v1_funct_1(k1_tmap_1(A_1356,B_1354,C_1352,D_1357,E_1355,F_1353))
      | k2_partfun1(D_1357,B_1354,F_1353,k9_subset_1(A_1356,C_1352,D_1357)) != k2_partfun1(C_1352,B_1354,E_1355,k9_subset_1(A_1356,C_1352,D_1357))
      | ~ m1_subset_1(F_1353,k1_zfmisc_1(k2_zfmisc_1(D_1357,B_1354)))
      | ~ v1_funct_2(F_1353,D_1357,B_1354)
      | ~ v1_funct_1(F_1353)
      | ~ m1_subset_1(E_1355,k1_zfmisc_1(k2_zfmisc_1(C_1352,B_1354)))
      | ~ v1_funct_2(E_1355,C_1352,B_1354)
      | ~ v1_funct_1(E_1355)
      | ~ m1_subset_1(D_1357,k1_zfmisc_1(A_1356))
      | v1_xboole_0(D_1357)
      | ~ m1_subset_1(C_1352,k1_zfmisc_1(A_1356))
      | v1_xboole_0(C_1352)
      | v1_xboole_0(B_1354)
      | v1_xboole_0(A_1356) ) ),
    inference(resolution,[status(thm)],[c_54,c_9615])).

tff(c_10383,plain,(
    ! [A_1356,C_1352,E_1355] :
      ( k2_partfun1(k4_subset_1(A_1356,C_1352,'#skF_6'),'#skF_4',k1_tmap_1(A_1356,'#skF_4',C_1352,'#skF_6',E_1355,'#skF_8'),C_1352) = E_1355
      | ~ v1_funct_1(k1_tmap_1(A_1356,'#skF_4',C_1352,'#skF_6',E_1355,'#skF_8'))
      | k2_partfun1(C_1352,'#skF_4',E_1355,k9_subset_1(A_1356,C_1352,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_1356,C_1352,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1355,k1_zfmisc_1(k2_zfmisc_1(C_1352,'#skF_4')))
      | ~ v1_funct_2(E_1355,C_1352,'#skF_4')
      | ~ v1_funct_1(E_1355)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1356))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1352,k1_zfmisc_1(A_1356))
      | v1_xboole_0(C_1352)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1356) ) ),
    inference(resolution,[status(thm)],[c_60,c_10379])).

tff(c_10389,plain,(
    ! [A_1356,C_1352,E_1355] :
      ( k2_partfun1(k4_subset_1(A_1356,C_1352,'#skF_6'),'#skF_4',k1_tmap_1(A_1356,'#skF_4',C_1352,'#skF_6',E_1355,'#skF_8'),C_1352) = E_1355
      | ~ v1_funct_1(k1_tmap_1(A_1356,'#skF_4',C_1352,'#skF_6',E_1355,'#skF_8'))
      | k2_partfun1(C_1352,'#skF_4',E_1355,k9_subset_1(A_1356,C_1352,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1356,C_1352,'#skF_6'))
      | ~ m1_subset_1(E_1355,k1_zfmisc_1(k2_zfmisc_1(C_1352,'#skF_4')))
      | ~ v1_funct_2(E_1355,C_1352,'#skF_4')
      | ~ v1_funct_1(E_1355)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1356))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1352,k1_zfmisc_1(A_1356))
      | v1_xboole_0(C_1352)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_7177,c_10383])).

tff(c_10457,plain,(
    ! [A_1361,C_1362,E_1363] :
      ( k2_partfun1(k4_subset_1(A_1361,C_1362,'#skF_6'),'#skF_4',k1_tmap_1(A_1361,'#skF_4',C_1362,'#skF_6',E_1363,'#skF_8'),C_1362) = E_1363
      | ~ v1_funct_1(k1_tmap_1(A_1361,'#skF_4',C_1362,'#skF_6',E_1363,'#skF_8'))
      | k2_partfun1(C_1362,'#skF_4',E_1363,k9_subset_1(A_1361,C_1362,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1361,C_1362,'#skF_6'))
      | ~ m1_subset_1(E_1363,k1_zfmisc_1(k2_zfmisc_1(C_1362,'#skF_4')))
      | ~ v1_funct_2(E_1363,C_1362,'#skF_4')
      | ~ v1_funct_1(E_1363)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1361))
      | ~ m1_subset_1(C_1362,k1_zfmisc_1(A_1361))
      | v1_xboole_0(C_1362)
      | v1_xboole_0(A_1361) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_10389])).

tff(c_10464,plain,(
    ! [A_1361] :
      ( k2_partfun1(k4_subset_1(A_1361,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1361,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1361,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_1361,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1361,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1361))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1361))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1361) ) ),
    inference(resolution,[status(thm)],[c_66,c_10457])).

tff(c_10474,plain,(
    ! [A_1361] :
      ( k2_partfun1(k4_subset_1(A_1361,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1361,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1361,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1361,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1361,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1361))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1361))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_7180,c_10464])).

tff(c_11089,plain,(
    ! [A_1391] :
      ( k2_partfun1(k4_subset_1(A_1391,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1391,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1391,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1391,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1391,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1391))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1391))
      | v1_xboole_0(A_1391) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10474])).

tff(c_652,plain,(
    ! [B_346,A_347] :
      ( k7_relat_1(B_346,A_347) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_346),A_347)
      | ~ v1_relat_1(B_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_705,plain,(
    ! [B_350] :
      ( k7_relat_1(B_350,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_350) ) ),
    inference(resolution,[status(thm)],[c_16,c_652])).

tff(c_713,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_523,c_705])).

tff(c_570,plain,(
    ! [C_334,A_335,B_336] :
      ( v4_relat_1(C_334,A_335)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_335,B_336))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_578,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_570])).

tff(c_819,plain,(
    ! [B_370,A_371] :
      ( k1_relat_1(B_370) = A_371
      | ~ v1_partfun1(B_370,A_371)
      | ~ v4_relat_1(B_370,A_371)
      | ~ v1_relat_1(B_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_822,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_578,c_819])).

tff(c_828,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_822])).

tff(c_832,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_828])).

tff(c_1156,plain,(
    ! [C_415,A_416,B_417] :
      ( v1_partfun1(C_415,A_416)
      | ~ v1_funct_2(C_415,A_416,B_417)
      | ~ v1_funct_1(C_415)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_416,B_417)))
      | v1_xboole_0(B_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1162,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1156])).

tff(c_1169,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1162])).

tff(c_1171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_832,c_1169])).

tff(c_1172,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_828])).

tff(c_1185,plain,(
    ! [A_18] :
      ( k7_relat_1('#skF_7',A_18) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_18)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1172,c_22])).

tff(c_1397,plain,(
    ! [A_436] :
      ( k7_relat_1('#skF_7',A_436) = k1_xboole_0
      | ~ r1_xboole_0('#skF_5',A_436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_1185])).

tff(c_1401,plain,(
    ! [B_21] :
      ( k7_relat_1('#skF_7',B_21) = k1_xboole_0
      | ~ r1_subset_1('#skF_5',B_21)
      | v1_xboole_0(B_21)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_1397])).

tff(c_1585,plain,(
    ! [B_452] :
      ( k7_relat_1('#skF_7',B_452) = k1_xboole_0
      | ~ r1_subset_1('#skF_5',B_452)
      | v1_xboole_0(B_452) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1401])).

tff(c_1591,plain,
    ( k7_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_1585])).

tff(c_1595,plain,(
    k7_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1591])).

tff(c_1177,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_5',A_18)
      | k7_relat_1('#skF_7',A_18) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1172,c_24])).

tff(c_1473,plain,(
    ! [A_439] :
      ( r1_xboole_0('#skF_5',A_439)
      | k7_relat_1('#skF_7',A_439) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_1177])).

tff(c_1490,plain,(
    ! [A_439] :
      ( k3_xboole_0('#skF_5',A_439) = k1_xboole_0
      | k7_relat_1('#skF_7',A_439) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1473,c_6])).

tff(c_1608,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_1490])).

tff(c_712,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_524,c_705])).

tff(c_759,plain,(
    ! [A_360,B_361,C_362] :
      ( k9_subset_1(A_360,B_361,C_362) = k3_xboole_0(B_361,C_362)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(A_360)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_771,plain,(
    ! [B_361] : k9_subset_1('#skF_3',B_361,'#skF_6') = k3_xboole_0(B_361,'#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_759])).

tff(c_1685,plain,(
    ! [C_465,E_468,B_467,D_470,F_466,A_469] :
      ( v1_funct_1(k1_tmap_1(A_469,B_467,C_465,D_470,E_468,F_466))
      | ~ m1_subset_1(F_466,k1_zfmisc_1(k2_zfmisc_1(D_470,B_467)))
      | ~ v1_funct_2(F_466,D_470,B_467)
      | ~ v1_funct_1(F_466)
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(C_465,B_467)))
      | ~ v1_funct_2(E_468,C_465,B_467)
      | ~ v1_funct_1(E_468)
      | ~ m1_subset_1(D_470,k1_zfmisc_1(A_469))
      | v1_xboole_0(D_470)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(A_469))
      | v1_xboole_0(C_465)
      | v1_xboole_0(B_467)
      | v1_xboole_0(A_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1687,plain,(
    ! [A_469,C_465,E_468] :
      ( v1_funct_1(k1_tmap_1(A_469,'#skF_4',C_465,'#skF_6',E_468,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(C_465,'#skF_4')))
      | ~ v1_funct_2(E_468,C_465,'#skF_4')
      | ~ v1_funct_1(E_468)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_469))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_465,k1_zfmisc_1(A_469))
      | v1_xboole_0(C_465)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_469) ) ),
    inference(resolution,[status(thm)],[c_60,c_1685])).

tff(c_1692,plain,(
    ! [A_469,C_465,E_468] :
      ( v1_funct_1(k1_tmap_1(A_469,'#skF_4',C_465,'#skF_6',E_468,'#skF_8'))
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(C_465,'#skF_4')))
      | ~ v1_funct_2(E_468,C_465,'#skF_4')
      | ~ v1_funct_1(E_468)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_469))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_465,k1_zfmisc_1(A_469))
      | v1_xboole_0(C_465)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1687])).

tff(c_1710,plain,(
    ! [A_472,C_473,E_474] :
      ( v1_funct_1(k1_tmap_1(A_472,'#skF_4',C_473,'#skF_6',E_474,'#skF_8'))
      | ~ m1_subset_1(E_474,k1_zfmisc_1(k2_zfmisc_1(C_473,'#skF_4')))
      | ~ v1_funct_2(E_474,C_473,'#skF_4')
      | ~ v1_funct_1(E_474)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_472))
      | ~ m1_subset_1(C_473,k1_zfmisc_1(A_472))
      | v1_xboole_0(C_473)
      | v1_xboole_0(A_472) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1692])).

tff(c_1714,plain,(
    ! [A_472] :
      ( v1_funct_1(k1_tmap_1(A_472,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_472))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_472))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_472) ) ),
    inference(resolution,[status(thm)],[c_66,c_1710])).

tff(c_1721,plain,(
    ! [A_472] :
      ( v1_funct_1(k1_tmap_1(A_472,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_472))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_472))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1714])).

tff(c_2102,plain,(
    ! [A_515] :
      ( v1_funct_1(k1_tmap_1(A_515,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_515))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_515))
      | v1_xboole_0(A_515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1721])).

tff(c_2105,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2102])).

tff(c_2108,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2105])).

tff(c_2109,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2108])).

tff(c_1533,plain,(
    ! [A_442,B_443,C_444,D_445] :
      ( k2_partfun1(A_442,B_443,C_444,D_445) = k7_relat_1(C_444,D_445)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443)))
      | ~ v1_funct_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1537,plain,(
    ! [D_445] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_445) = k7_relat_1('#skF_7',D_445)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1533])).

tff(c_1543,plain,(
    ! [D_445] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_445) = k7_relat_1('#skF_7',D_445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1537])).

tff(c_1535,plain,(
    ! [D_445] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_445) = k7_relat_1('#skF_8',D_445)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_60,c_1533])).

tff(c_1540,plain,(
    ! [D_445] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_445) = k7_relat_1('#skF_8',D_445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1535])).

tff(c_2125,plain,(
    ! [A_521,C_522,F_525,D_526,E_524,B_523] :
      ( k2_partfun1(k4_subset_1(A_521,C_522,D_526),B_523,k1_tmap_1(A_521,B_523,C_522,D_526,E_524,F_525),D_526) = F_525
      | ~ m1_subset_1(k1_tmap_1(A_521,B_523,C_522,D_526,E_524,F_525),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_521,C_522,D_526),B_523)))
      | ~ v1_funct_2(k1_tmap_1(A_521,B_523,C_522,D_526,E_524,F_525),k4_subset_1(A_521,C_522,D_526),B_523)
      | ~ v1_funct_1(k1_tmap_1(A_521,B_523,C_522,D_526,E_524,F_525))
      | k2_partfun1(D_526,B_523,F_525,k9_subset_1(A_521,C_522,D_526)) != k2_partfun1(C_522,B_523,E_524,k9_subset_1(A_521,C_522,D_526))
      | ~ m1_subset_1(F_525,k1_zfmisc_1(k2_zfmisc_1(D_526,B_523)))
      | ~ v1_funct_2(F_525,D_526,B_523)
      | ~ v1_funct_1(F_525)
      | ~ m1_subset_1(E_524,k1_zfmisc_1(k2_zfmisc_1(C_522,B_523)))
      | ~ v1_funct_2(E_524,C_522,B_523)
      | ~ v1_funct_1(E_524)
      | ~ m1_subset_1(D_526,k1_zfmisc_1(A_521))
      | v1_xboole_0(D_526)
      | ~ m1_subset_1(C_522,k1_zfmisc_1(A_521))
      | v1_xboole_0(C_522)
      | v1_xboole_0(B_523)
      | v1_xboole_0(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4586,plain,(
    ! [F_763,D_767,C_762,A_766,E_765,B_764] :
      ( k2_partfun1(k4_subset_1(A_766,C_762,D_767),B_764,k1_tmap_1(A_766,B_764,C_762,D_767,E_765,F_763),D_767) = F_763
      | ~ v1_funct_2(k1_tmap_1(A_766,B_764,C_762,D_767,E_765,F_763),k4_subset_1(A_766,C_762,D_767),B_764)
      | ~ v1_funct_1(k1_tmap_1(A_766,B_764,C_762,D_767,E_765,F_763))
      | k2_partfun1(D_767,B_764,F_763,k9_subset_1(A_766,C_762,D_767)) != k2_partfun1(C_762,B_764,E_765,k9_subset_1(A_766,C_762,D_767))
      | ~ m1_subset_1(F_763,k1_zfmisc_1(k2_zfmisc_1(D_767,B_764)))
      | ~ v1_funct_2(F_763,D_767,B_764)
      | ~ v1_funct_1(F_763)
      | ~ m1_subset_1(E_765,k1_zfmisc_1(k2_zfmisc_1(C_762,B_764)))
      | ~ v1_funct_2(E_765,C_762,B_764)
      | ~ v1_funct_1(E_765)
      | ~ m1_subset_1(D_767,k1_zfmisc_1(A_766))
      | v1_xboole_0(D_767)
      | ~ m1_subset_1(C_762,k1_zfmisc_1(A_766))
      | v1_xboole_0(C_762)
      | v1_xboole_0(B_764)
      | v1_xboole_0(A_766) ) ),
    inference(resolution,[status(thm)],[c_52,c_2125])).

tff(c_5284,plain,(
    ! [E_818,A_819,B_817,D_820,C_815,F_816] :
      ( k2_partfun1(k4_subset_1(A_819,C_815,D_820),B_817,k1_tmap_1(A_819,B_817,C_815,D_820,E_818,F_816),D_820) = F_816
      | ~ v1_funct_1(k1_tmap_1(A_819,B_817,C_815,D_820,E_818,F_816))
      | k2_partfun1(D_820,B_817,F_816,k9_subset_1(A_819,C_815,D_820)) != k2_partfun1(C_815,B_817,E_818,k9_subset_1(A_819,C_815,D_820))
      | ~ m1_subset_1(F_816,k1_zfmisc_1(k2_zfmisc_1(D_820,B_817)))
      | ~ v1_funct_2(F_816,D_820,B_817)
      | ~ v1_funct_1(F_816)
      | ~ m1_subset_1(E_818,k1_zfmisc_1(k2_zfmisc_1(C_815,B_817)))
      | ~ v1_funct_2(E_818,C_815,B_817)
      | ~ v1_funct_1(E_818)
      | ~ m1_subset_1(D_820,k1_zfmisc_1(A_819))
      | v1_xboole_0(D_820)
      | ~ m1_subset_1(C_815,k1_zfmisc_1(A_819))
      | v1_xboole_0(C_815)
      | v1_xboole_0(B_817)
      | v1_xboole_0(A_819) ) ),
    inference(resolution,[status(thm)],[c_54,c_4586])).

tff(c_5288,plain,(
    ! [A_819,C_815,E_818] :
      ( k2_partfun1(k4_subset_1(A_819,C_815,'#skF_6'),'#skF_4',k1_tmap_1(A_819,'#skF_4',C_815,'#skF_6',E_818,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_819,'#skF_4',C_815,'#skF_6',E_818,'#skF_8'))
      | k2_partfun1(C_815,'#skF_4',E_818,k9_subset_1(A_819,C_815,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_819,C_815,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_818,k1_zfmisc_1(k2_zfmisc_1(C_815,'#skF_4')))
      | ~ v1_funct_2(E_818,C_815,'#skF_4')
      | ~ v1_funct_1(E_818)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_819))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_815,k1_zfmisc_1(A_819))
      | v1_xboole_0(C_815)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_819) ) ),
    inference(resolution,[status(thm)],[c_60,c_5284])).

tff(c_5294,plain,(
    ! [A_819,C_815,E_818] :
      ( k2_partfun1(k4_subset_1(A_819,C_815,'#skF_6'),'#skF_4',k1_tmap_1(A_819,'#skF_4',C_815,'#skF_6',E_818,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_819,'#skF_4',C_815,'#skF_6',E_818,'#skF_8'))
      | k2_partfun1(C_815,'#skF_4',E_818,k9_subset_1(A_819,C_815,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_819,C_815,'#skF_6'))
      | ~ m1_subset_1(E_818,k1_zfmisc_1(k2_zfmisc_1(C_815,'#skF_4')))
      | ~ v1_funct_2(E_818,C_815,'#skF_4')
      | ~ v1_funct_1(E_818)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_819))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_815,k1_zfmisc_1(A_819))
      | v1_xboole_0(C_815)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_819) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1540,c_5288])).

tff(c_5918,plain,(
    ! [A_866,C_867,E_868] :
      ( k2_partfun1(k4_subset_1(A_866,C_867,'#skF_6'),'#skF_4',k1_tmap_1(A_866,'#skF_4',C_867,'#skF_6',E_868,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_866,'#skF_4',C_867,'#skF_6',E_868,'#skF_8'))
      | k2_partfun1(C_867,'#skF_4',E_868,k9_subset_1(A_866,C_867,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_866,C_867,'#skF_6'))
      | ~ m1_subset_1(E_868,k1_zfmisc_1(k2_zfmisc_1(C_867,'#skF_4')))
      | ~ v1_funct_2(E_868,C_867,'#skF_4')
      | ~ v1_funct_1(E_868)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_866))
      | ~ m1_subset_1(C_867,k1_zfmisc_1(A_866))
      | v1_xboole_0(C_867)
      | v1_xboole_0(A_866) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_5294])).

tff(c_5925,plain,(
    ! [A_866] :
      ( k2_partfun1(k4_subset_1(A_866,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_866,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_866,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_866,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_866,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_866))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_866))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_866) ) ),
    inference(resolution,[status(thm)],[c_66,c_5918])).

tff(c_5935,plain,(
    ! [A_866] :
      ( k2_partfun1(k4_subset_1(A_866,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_866,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_866,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_866,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_866,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_866))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_866))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1543,c_5925])).

tff(c_5945,plain,(
    ! [A_869] :
      ( k2_partfun1(k4_subset_1(A_869,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_869,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_869,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_869,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_869,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_869))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_869))
      | v1_xboole_0(A_869) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_5935])).

tff(c_135,plain,(
    ! [C_247,A_248,B_249] :
      ( v1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_143,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_135])).

tff(c_243,plain,(
    ! [B_271,A_272] :
      ( k7_relat_1(B_271,A_272) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_271),A_272)
      | ~ v1_relat_1(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_279,plain,(
    ! [B_274] :
      ( k7_relat_1(B_274,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_274) ) ),
    inference(resolution,[status(thm)],[c_16,c_243])).

tff(c_286,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_143,c_279])).

tff(c_470,plain,(
    ! [A_305,B_306,C_307,D_308] :
      ( k2_partfun1(A_305,B_306,C_307,D_308) = k7_relat_1(C_307,D_308)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | ~ v1_funct_1(C_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_474,plain,(
    ! [D_308] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_308) = k7_relat_1('#skF_7',D_308)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_470])).

tff(c_480,plain,(
    ! [D_308] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_308) = k7_relat_1('#skF_7',D_308) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_474])).

tff(c_142,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_135])).

tff(c_287,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_279])).

tff(c_472,plain,(
    ! [D_308] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_308) = k7_relat_1('#skF_8',D_308)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_60,c_470])).

tff(c_477,plain,(
    ! [D_308] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_308) = k7_relat_1('#skF_8',D_308) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_472])).

tff(c_316,plain,(
    ! [A_281,B_282] :
      ( r1_xboole_0(A_281,B_282)
      | ~ r1_subset_1(A_281,B_282)
      | v1_xboole_0(B_282)
      | v1_xboole_0(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_458,plain,(
    ! [A_303,B_304] :
      ( k3_xboole_0(A_303,B_304) = k1_xboole_0
      | ~ r1_subset_1(A_303,B_304)
      | v1_xboole_0(B_304)
      | v1_xboole_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_316,c_6])).

tff(c_461,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_458])).

tff(c_464,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_76,c_461])).

tff(c_371,plain,(
    ! [A_289,B_290,C_291] :
      ( k9_subset_1(A_289,B_290,C_291) = k3_xboole_0(B_290,C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(A_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_383,plain,(
    ! [B_290] : k9_subset_1('#skF_3',B_290,'#skF_6') = k3_xboole_0(B_290,'#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_371])).

tff(c_58,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_109,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_393,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_383,c_109])).

tff(c_465,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k1_xboole_0) != k2_partfun1('#skF_6','#skF_4','#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_464,c_393])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_480,c_287,c_477,c_465])).

tff(c_501,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_546,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_5956,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5945,c_546])).

tff(c_5970,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_713,c_1608,c_712,c_1608,c_771,c_771,c_2109,c_5956])).

tff(c_5972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5970])).

tff(c_5973,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_11098,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11089,c_5973])).

tff(c_11109,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_6106,c_7193,c_6105,c_7193,c_7099,c_7099,c_7848,c_11098])).

tff(c_11111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_11109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:39:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.91/3.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/3.27  
% 8.91/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/3.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 8.91/3.28  
% 8.91/3.28  %Foreground sorts:
% 8.91/3.28  
% 8.91/3.28  
% 8.91/3.28  %Background operators:
% 8.91/3.28  
% 8.91/3.28  
% 8.91/3.28  %Foreground operators:
% 8.91/3.28  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.91/3.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.91/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.91/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.91/3.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.91/3.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.91/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.91/3.28  tff('#skF_7', type, '#skF_7': $i).
% 8.91/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.91/3.28  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.91/3.28  tff('#skF_5', type, '#skF_5': $i).
% 8.91/3.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.91/3.28  tff('#skF_6', type, '#skF_6': $i).
% 8.91/3.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.91/3.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.91/3.28  tff('#skF_3', type, '#skF_3': $i).
% 8.91/3.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.91/3.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.91/3.28  tff('#skF_8', type, '#skF_8': $i).
% 8.91/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.91/3.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.91/3.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.91/3.28  tff('#skF_4', type, '#skF_4': $i).
% 8.91/3.28  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.91/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.91/3.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.91/3.28  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.91/3.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.91/3.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.91/3.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.91/3.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.91/3.28  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.91/3.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.91/3.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.91/3.28  
% 9.32/3.31  tff(f_239, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 9.32/3.31  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.32/3.31  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.32/3.31  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 9.32/3.31  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 9.32/3.31  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.32/3.31  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 9.32/3.31  tff(f_101, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 9.32/3.31  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.32/3.31  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.32/3.31  tff(f_197, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 9.32/3.31  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.32/3.31  tff(f_163, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 9.32/3.31  tff(c_84, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_516, plain, (![C_313, A_314, B_315]: (v1_relat_1(C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.31  tff(c_523, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_516])).
% 9.32/3.31  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.32/3.31  tff(c_6073, plain, (![B_889, A_890]: (k7_relat_1(B_889, A_890)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_889), A_890) | ~v1_relat_1(B_889))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.31  tff(c_6098, plain, (![B_891]: (k7_relat_1(B_891, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_891))), inference(resolution, [status(thm)], [c_16, c_6073])).
% 9.32/3.31  tff(c_6106, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_523, c_6098])).
% 9.32/3.31  tff(c_76, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_72, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_80, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_28, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | ~r1_subset_1(A_20, B_21) | v1_xboole_0(B_21) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.32/3.31  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_524, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_516])).
% 9.32/3.31  tff(c_82, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_5985, plain, (![C_875, A_876, B_877]: (v4_relat_1(C_875, A_876) | ~m1_subset_1(C_875, k1_zfmisc_1(k2_zfmisc_1(A_876, B_877))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.32/3.31  tff(c_5993, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_5985])).
% 9.32/3.31  tff(c_6217, plain, (![B_910, A_911]: (k1_relat_1(B_910)=A_911 | ~v1_partfun1(B_910, A_911) | ~v4_relat_1(B_910, A_911) | ~v1_relat_1(B_910))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.32/3.31  tff(c_6220, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5993, c_6217])).
% 9.32/3.31  tff(c_6226, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_6220])).
% 9.32/3.31  tff(c_6230, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_6226])).
% 9.32/3.31  tff(c_70, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_68, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_6596, plain, (![C_961, A_962, B_963]: (v1_partfun1(C_961, A_962) | ~v1_funct_2(C_961, A_962, B_963) | ~v1_funct_1(C_961) | ~m1_subset_1(C_961, k1_zfmisc_1(k2_zfmisc_1(A_962, B_963))) | v1_xboole_0(B_963))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.32/3.31  tff(c_6602, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_6596])).
% 9.32/3.31  tff(c_6609, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_6602])).
% 9.32/3.31  tff(c_6611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_6230, c_6609])).
% 9.32/3.31  tff(c_6612, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_6226])).
% 9.32/3.31  tff(c_22, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.31  tff(c_6622, plain, (![A_18]: (k7_relat_1('#skF_7', A_18)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_18) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6612, c_22])).
% 9.32/3.31  tff(c_6951, plain, (![A_996]: (k7_relat_1('#skF_7', A_996)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_996))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_6622])).
% 9.32/3.31  tff(c_6955, plain, (![B_21]: (k7_relat_1('#skF_7', B_21)=k1_xboole_0 | ~r1_subset_1('#skF_5', B_21) | v1_xboole_0(B_21) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_6951])).
% 9.32/3.31  tff(c_7159, plain, (![B_1013]: (k7_relat_1('#skF_7', B_1013)=k1_xboole_0 | ~r1_subset_1('#skF_5', B_1013) | v1_xboole_0(B_1013))), inference(negUnitSimplification, [status(thm)], [c_80, c_6955])).
% 9.32/3.31  tff(c_7165, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_72, c_7159])).
% 9.32/3.31  tff(c_7169, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_7165])).
% 9.32/3.31  tff(c_24, plain, (![B_19, A_18]: (r1_xboole_0(k1_relat_1(B_19), A_18) | k7_relat_1(B_19, A_18)!=k1_xboole_0 | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.31  tff(c_6619, plain, (![A_18]: (r1_xboole_0('#skF_5', A_18) | k7_relat_1('#skF_7', A_18)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6612, c_24])).
% 9.32/3.31  tff(c_7027, plain, (![A_999]: (r1_xboole_0('#skF_5', A_999) | k7_relat_1('#skF_7', A_999)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_524, c_6619])).
% 9.32/3.31  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.32/3.31  tff(c_7044, plain, (![A_999]: (k3_xboole_0('#skF_5', A_999)=k1_xboole_0 | k7_relat_1('#skF_7', A_999)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7027, c_6])).
% 9.32/3.31  tff(c_7193, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7169, c_7044])).
% 9.32/3.31  tff(c_6105, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_524, c_6098])).
% 9.32/3.31  tff(c_7087, plain, (![A_1002, B_1003, C_1004]: (k9_subset_1(A_1002, B_1003, C_1004)=k3_xboole_0(B_1003, C_1004) | ~m1_subset_1(C_1004, k1_zfmisc_1(A_1002)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.32/3.31  tff(c_7099, plain, (![B_1003]: (k9_subset_1('#skF_3', B_1003, '#skF_6')=k3_xboole_0(B_1003, '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_7087])).
% 9.32/3.31  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_7395, plain, (![B_1041, F_1040, E_1042, C_1039, A_1043, D_1044]: (v1_funct_1(k1_tmap_1(A_1043, B_1041, C_1039, D_1044, E_1042, F_1040)) | ~m1_subset_1(F_1040, k1_zfmisc_1(k2_zfmisc_1(D_1044, B_1041))) | ~v1_funct_2(F_1040, D_1044, B_1041) | ~v1_funct_1(F_1040) | ~m1_subset_1(E_1042, k1_zfmisc_1(k2_zfmisc_1(C_1039, B_1041))) | ~v1_funct_2(E_1042, C_1039, B_1041) | ~v1_funct_1(E_1042) | ~m1_subset_1(D_1044, k1_zfmisc_1(A_1043)) | v1_xboole_0(D_1044) | ~m1_subset_1(C_1039, k1_zfmisc_1(A_1043)) | v1_xboole_0(C_1039) | v1_xboole_0(B_1041) | v1_xboole_0(A_1043))), inference(cnfTransformation, [status(thm)], [f_197])).
% 9.32/3.31  tff(c_7397, plain, (![A_1043, C_1039, E_1042]: (v1_funct_1(k1_tmap_1(A_1043, '#skF_4', C_1039, '#skF_6', E_1042, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1042, k1_zfmisc_1(k2_zfmisc_1(C_1039, '#skF_4'))) | ~v1_funct_2(E_1042, C_1039, '#skF_4') | ~v1_funct_1(E_1042) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1043)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1039, k1_zfmisc_1(A_1043)) | v1_xboole_0(C_1039) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1043))), inference(resolution, [status(thm)], [c_60, c_7395])).
% 9.32/3.31  tff(c_7402, plain, (![A_1043, C_1039, E_1042]: (v1_funct_1(k1_tmap_1(A_1043, '#skF_4', C_1039, '#skF_6', E_1042, '#skF_8')) | ~m1_subset_1(E_1042, k1_zfmisc_1(k2_zfmisc_1(C_1039, '#skF_4'))) | ~v1_funct_2(E_1042, C_1039, '#skF_4') | ~v1_funct_1(E_1042) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1043)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1039, k1_zfmisc_1(A_1043)) | v1_xboole_0(C_1039) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1043))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_7397])).
% 9.32/3.31  tff(c_7459, plain, (![A_1052, C_1053, E_1054]: (v1_funct_1(k1_tmap_1(A_1052, '#skF_4', C_1053, '#skF_6', E_1054, '#skF_8')) | ~m1_subset_1(E_1054, k1_zfmisc_1(k2_zfmisc_1(C_1053, '#skF_4'))) | ~v1_funct_2(E_1054, C_1053, '#skF_4') | ~v1_funct_1(E_1054) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1052)) | ~m1_subset_1(C_1053, k1_zfmisc_1(A_1052)) | v1_xboole_0(C_1053) | v1_xboole_0(A_1052))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_7402])).
% 9.32/3.31  tff(c_7463, plain, (![A_1052]: (v1_funct_1(k1_tmap_1(A_1052, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1052)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1052)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1052))), inference(resolution, [status(thm)], [c_66, c_7459])).
% 9.32/3.31  tff(c_7470, plain, (![A_1052]: (v1_funct_1(k1_tmap_1(A_1052, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1052)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1052)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1052))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_7463])).
% 9.32/3.31  tff(c_7841, plain, (![A_1092]: (v1_funct_1(k1_tmap_1(A_1092, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1092)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1092)) | v1_xboole_0(A_1092))), inference(negUnitSimplification, [status(thm)], [c_80, c_7470])).
% 9.32/3.31  tff(c_7844, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_7841])).
% 9.32/3.31  tff(c_7847, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7844])).
% 9.32/3.31  tff(c_7848, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_7847])).
% 9.32/3.31  tff(c_7170, plain, (![A_1014, B_1015, C_1016, D_1017]: (k2_partfun1(A_1014, B_1015, C_1016, D_1017)=k7_relat_1(C_1016, D_1017) | ~m1_subset_1(C_1016, k1_zfmisc_1(k2_zfmisc_1(A_1014, B_1015))) | ~v1_funct_1(C_1016))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.32/3.31  tff(c_7174, plain, (![D_1017]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1017)=k7_relat_1('#skF_7', D_1017) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_7170])).
% 9.32/3.31  tff(c_7180, plain, (![D_1017]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1017)=k7_relat_1('#skF_7', D_1017))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_7174])).
% 9.32/3.31  tff(c_7172, plain, (![D_1017]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1017)=k7_relat_1('#skF_8', D_1017) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_7170])).
% 9.32/3.31  tff(c_7177, plain, (![D_1017]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1017)=k7_relat_1('#skF_8', D_1017))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_7172])).
% 9.32/3.31  tff(c_54, plain, (![B_166, F_170, D_168, A_165, E_169, C_167]: (v1_funct_2(k1_tmap_1(A_165, B_166, C_167, D_168, E_169, F_170), k4_subset_1(A_165, C_167, D_168), B_166) | ~m1_subset_1(F_170, k1_zfmisc_1(k2_zfmisc_1(D_168, B_166))) | ~v1_funct_2(F_170, D_168, B_166) | ~v1_funct_1(F_170) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(C_167, B_166))) | ~v1_funct_2(E_169, C_167, B_166) | ~v1_funct_1(E_169) | ~m1_subset_1(D_168, k1_zfmisc_1(A_165)) | v1_xboole_0(D_168) | ~m1_subset_1(C_167, k1_zfmisc_1(A_165)) | v1_xboole_0(C_167) | v1_xboole_0(B_166) | v1_xboole_0(A_165))), inference(cnfTransformation, [status(thm)], [f_197])).
% 9.32/3.31  tff(c_52, plain, (![B_166, F_170, D_168, A_165, E_169, C_167]: (m1_subset_1(k1_tmap_1(A_165, B_166, C_167, D_168, E_169, F_170), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_165, C_167, D_168), B_166))) | ~m1_subset_1(F_170, k1_zfmisc_1(k2_zfmisc_1(D_168, B_166))) | ~v1_funct_2(F_170, D_168, B_166) | ~v1_funct_1(F_170) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(C_167, B_166))) | ~v1_funct_2(E_169, C_167, B_166) | ~v1_funct_1(E_169) | ~m1_subset_1(D_168, k1_zfmisc_1(A_165)) | v1_xboole_0(D_168) | ~m1_subset_1(C_167, k1_zfmisc_1(A_165)) | v1_xboole_0(C_167) | v1_xboole_0(B_166) | v1_xboole_0(A_165))), inference(cnfTransformation, [status(thm)], [f_197])).
% 9.32/3.31  tff(c_7925, plain, (![E_1101, C_1099, A_1098, F_1102, B_1100, D_1103]: (k2_partfun1(k4_subset_1(A_1098, C_1099, D_1103), B_1100, k1_tmap_1(A_1098, B_1100, C_1099, D_1103, E_1101, F_1102), C_1099)=E_1101 | ~m1_subset_1(k1_tmap_1(A_1098, B_1100, C_1099, D_1103, E_1101, F_1102), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1098, C_1099, D_1103), B_1100))) | ~v1_funct_2(k1_tmap_1(A_1098, B_1100, C_1099, D_1103, E_1101, F_1102), k4_subset_1(A_1098, C_1099, D_1103), B_1100) | ~v1_funct_1(k1_tmap_1(A_1098, B_1100, C_1099, D_1103, E_1101, F_1102)) | k2_partfun1(D_1103, B_1100, F_1102, k9_subset_1(A_1098, C_1099, D_1103))!=k2_partfun1(C_1099, B_1100, E_1101, k9_subset_1(A_1098, C_1099, D_1103)) | ~m1_subset_1(F_1102, k1_zfmisc_1(k2_zfmisc_1(D_1103, B_1100))) | ~v1_funct_2(F_1102, D_1103, B_1100) | ~v1_funct_1(F_1102) | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(C_1099, B_1100))) | ~v1_funct_2(E_1101, C_1099, B_1100) | ~v1_funct_1(E_1101) | ~m1_subset_1(D_1103, k1_zfmisc_1(A_1098)) | v1_xboole_0(D_1103) | ~m1_subset_1(C_1099, k1_zfmisc_1(A_1098)) | v1_xboole_0(C_1099) | v1_xboole_0(B_1100) | v1_xboole_0(A_1098))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.32/3.31  tff(c_9615, plain, (![F_1297, E_1299, C_1296, B_1298, A_1300, D_1301]: (k2_partfun1(k4_subset_1(A_1300, C_1296, D_1301), B_1298, k1_tmap_1(A_1300, B_1298, C_1296, D_1301, E_1299, F_1297), C_1296)=E_1299 | ~v1_funct_2(k1_tmap_1(A_1300, B_1298, C_1296, D_1301, E_1299, F_1297), k4_subset_1(A_1300, C_1296, D_1301), B_1298) | ~v1_funct_1(k1_tmap_1(A_1300, B_1298, C_1296, D_1301, E_1299, F_1297)) | k2_partfun1(D_1301, B_1298, F_1297, k9_subset_1(A_1300, C_1296, D_1301))!=k2_partfun1(C_1296, B_1298, E_1299, k9_subset_1(A_1300, C_1296, D_1301)) | ~m1_subset_1(F_1297, k1_zfmisc_1(k2_zfmisc_1(D_1301, B_1298))) | ~v1_funct_2(F_1297, D_1301, B_1298) | ~v1_funct_1(F_1297) | ~m1_subset_1(E_1299, k1_zfmisc_1(k2_zfmisc_1(C_1296, B_1298))) | ~v1_funct_2(E_1299, C_1296, B_1298) | ~v1_funct_1(E_1299) | ~m1_subset_1(D_1301, k1_zfmisc_1(A_1300)) | v1_xboole_0(D_1301) | ~m1_subset_1(C_1296, k1_zfmisc_1(A_1300)) | v1_xboole_0(C_1296) | v1_xboole_0(B_1298) | v1_xboole_0(A_1300))), inference(resolution, [status(thm)], [c_52, c_7925])).
% 9.32/3.31  tff(c_10379, plain, (![B_1354, C_1352, E_1355, F_1353, A_1356, D_1357]: (k2_partfun1(k4_subset_1(A_1356, C_1352, D_1357), B_1354, k1_tmap_1(A_1356, B_1354, C_1352, D_1357, E_1355, F_1353), C_1352)=E_1355 | ~v1_funct_1(k1_tmap_1(A_1356, B_1354, C_1352, D_1357, E_1355, F_1353)) | k2_partfun1(D_1357, B_1354, F_1353, k9_subset_1(A_1356, C_1352, D_1357))!=k2_partfun1(C_1352, B_1354, E_1355, k9_subset_1(A_1356, C_1352, D_1357)) | ~m1_subset_1(F_1353, k1_zfmisc_1(k2_zfmisc_1(D_1357, B_1354))) | ~v1_funct_2(F_1353, D_1357, B_1354) | ~v1_funct_1(F_1353) | ~m1_subset_1(E_1355, k1_zfmisc_1(k2_zfmisc_1(C_1352, B_1354))) | ~v1_funct_2(E_1355, C_1352, B_1354) | ~v1_funct_1(E_1355) | ~m1_subset_1(D_1357, k1_zfmisc_1(A_1356)) | v1_xboole_0(D_1357) | ~m1_subset_1(C_1352, k1_zfmisc_1(A_1356)) | v1_xboole_0(C_1352) | v1_xboole_0(B_1354) | v1_xboole_0(A_1356))), inference(resolution, [status(thm)], [c_54, c_9615])).
% 9.32/3.31  tff(c_10383, plain, (![A_1356, C_1352, E_1355]: (k2_partfun1(k4_subset_1(A_1356, C_1352, '#skF_6'), '#skF_4', k1_tmap_1(A_1356, '#skF_4', C_1352, '#skF_6', E_1355, '#skF_8'), C_1352)=E_1355 | ~v1_funct_1(k1_tmap_1(A_1356, '#skF_4', C_1352, '#skF_6', E_1355, '#skF_8')) | k2_partfun1(C_1352, '#skF_4', E_1355, k9_subset_1(A_1356, C_1352, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_1356, C_1352, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1355, k1_zfmisc_1(k2_zfmisc_1(C_1352, '#skF_4'))) | ~v1_funct_2(E_1355, C_1352, '#skF_4') | ~v1_funct_1(E_1355) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1356)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1352, k1_zfmisc_1(A_1356)) | v1_xboole_0(C_1352) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1356))), inference(resolution, [status(thm)], [c_60, c_10379])).
% 9.32/3.31  tff(c_10389, plain, (![A_1356, C_1352, E_1355]: (k2_partfun1(k4_subset_1(A_1356, C_1352, '#skF_6'), '#skF_4', k1_tmap_1(A_1356, '#skF_4', C_1352, '#skF_6', E_1355, '#skF_8'), C_1352)=E_1355 | ~v1_funct_1(k1_tmap_1(A_1356, '#skF_4', C_1352, '#skF_6', E_1355, '#skF_8')) | k2_partfun1(C_1352, '#skF_4', E_1355, k9_subset_1(A_1356, C_1352, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1356, C_1352, '#skF_6')) | ~m1_subset_1(E_1355, k1_zfmisc_1(k2_zfmisc_1(C_1352, '#skF_4'))) | ~v1_funct_2(E_1355, C_1352, '#skF_4') | ~v1_funct_1(E_1355) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1356)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1352, k1_zfmisc_1(A_1356)) | v1_xboole_0(C_1352) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1356))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_7177, c_10383])).
% 9.32/3.31  tff(c_10457, plain, (![A_1361, C_1362, E_1363]: (k2_partfun1(k4_subset_1(A_1361, C_1362, '#skF_6'), '#skF_4', k1_tmap_1(A_1361, '#skF_4', C_1362, '#skF_6', E_1363, '#skF_8'), C_1362)=E_1363 | ~v1_funct_1(k1_tmap_1(A_1361, '#skF_4', C_1362, '#skF_6', E_1363, '#skF_8')) | k2_partfun1(C_1362, '#skF_4', E_1363, k9_subset_1(A_1361, C_1362, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1361, C_1362, '#skF_6')) | ~m1_subset_1(E_1363, k1_zfmisc_1(k2_zfmisc_1(C_1362, '#skF_4'))) | ~v1_funct_2(E_1363, C_1362, '#skF_4') | ~v1_funct_1(E_1363) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1361)) | ~m1_subset_1(C_1362, k1_zfmisc_1(A_1361)) | v1_xboole_0(C_1362) | v1_xboole_0(A_1361))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_10389])).
% 9.32/3.31  tff(c_10464, plain, (![A_1361]: (k2_partfun1(k4_subset_1(A_1361, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1361, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1361, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_1361, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1361, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1361)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1361)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1361))), inference(resolution, [status(thm)], [c_66, c_10457])).
% 9.32/3.31  tff(c_10474, plain, (![A_1361]: (k2_partfun1(k4_subset_1(A_1361, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1361, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1361, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1361, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1361, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1361)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1361)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1361))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_7180, c_10464])).
% 9.32/3.31  tff(c_11089, plain, (![A_1391]: (k2_partfun1(k4_subset_1(A_1391, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1391, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1391, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1391, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1391, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1391)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1391)) | v1_xboole_0(A_1391))), inference(negUnitSimplification, [status(thm)], [c_80, c_10474])).
% 9.32/3.31  tff(c_652, plain, (![B_346, A_347]: (k7_relat_1(B_346, A_347)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_346), A_347) | ~v1_relat_1(B_346))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.31  tff(c_705, plain, (![B_350]: (k7_relat_1(B_350, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_350))), inference(resolution, [status(thm)], [c_16, c_652])).
% 9.32/3.31  tff(c_713, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_523, c_705])).
% 9.32/3.31  tff(c_570, plain, (![C_334, A_335, B_336]: (v4_relat_1(C_334, A_335) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(A_335, B_336))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.32/3.31  tff(c_578, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_570])).
% 9.32/3.31  tff(c_819, plain, (![B_370, A_371]: (k1_relat_1(B_370)=A_371 | ~v1_partfun1(B_370, A_371) | ~v4_relat_1(B_370, A_371) | ~v1_relat_1(B_370))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.32/3.31  tff(c_822, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_578, c_819])).
% 9.32/3.31  tff(c_828, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_822])).
% 9.32/3.31  tff(c_832, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_828])).
% 9.32/3.31  tff(c_1156, plain, (![C_415, A_416, B_417]: (v1_partfun1(C_415, A_416) | ~v1_funct_2(C_415, A_416, B_417) | ~v1_funct_1(C_415) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_416, B_417))) | v1_xboole_0(B_417))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.32/3.31  tff(c_1162, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1156])).
% 9.32/3.31  tff(c_1169, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1162])).
% 9.32/3.31  tff(c_1171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_832, c_1169])).
% 9.32/3.31  tff(c_1172, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_828])).
% 9.32/3.31  tff(c_1185, plain, (![A_18]: (k7_relat_1('#skF_7', A_18)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_18) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1172, c_22])).
% 9.32/3.31  tff(c_1397, plain, (![A_436]: (k7_relat_1('#skF_7', A_436)=k1_xboole_0 | ~r1_xboole_0('#skF_5', A_436))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_1185])).
% 9.32/3.31  tff(c_1401, plain, (![B_21]: (k7_relat_1('#skF_7', B_21)=k1_xboole_0 | ~r1_subset_1('#skF_5', B_21) | v1_xboole_0(B_21) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_1397])).
% 9.32/3.31  tff(c_1585, plain, (![B_452]: (k7_relat_1('#skF_7', B_452)=k1_xboole_0 | ~r1_subset_1('#skF_5', B_452) | v1_xboole_0(B_452))), inference(negUnitSimplification, [status(thm)], [c_80, c_1401])).
% 9.32/3.31  tff(c_1591, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_72, c_1585])).
% 9.32/3.31  tff(c_1595, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_76, c_1591])).
% 9.32/3.31  tff(c_1177, plain, (![A_18]: (r1_xboole_0('#skF_5', A_18) | k7_relat_1('#skF_7', A_18)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1172, c_24])).
% 9.32/3.31  tff(c_1473, plain, (![A_439]: (r1_xboole_0('#skF_5', A_439) | k7_relat_1('#skF_7', A_439)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_524, c_1177])).
% 9.32/3.31  tff(c_1490, plain, (![A_439]: (k3_xboole_0('#skF_5', A_439)=k1_xboole_0 | k7_relat_1('#skF_7', A_439)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1473, c_6])).
% 9.32/3.31  tff(c_1608, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1595, c_1490])).
% 9.32/3.31  tff(c_712, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_524, c_705])).
% 9.32/3.31  tff(c_759, plain, (![A_360, B_361, C_362]: (k9_subset_1(A_360, B_361, C_362)=k3_xboole_0(B_361, C_362) | ~m1_subset_1(C_362, k1_zfmisc_1(A_360)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.32/3.31  tff(c_771, plain, (![B_361]: (k9_subset_1('#skF_3', B_361, '#skF_6')=k3_xboole_0(B_361, '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_759])).
% 9.32/3.31  tff(c_1685, plain, (![C_465, E_468, B_467, D_470, F_466, A_469]: (v1_funct_1(k1_tmap_1(A_469, B_467, C_465, D_470, E_468, F_466)) | ~m1_subset_1(F_466, k1_zfmisc_1(k2_zfmisc_1(D_470, B_467))) | ~v1_funct_2(F_466, D_470, B_467) | ~v1_funct_1(F_466) | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(C_465, B_467))) | ~v1_funct_2(E_468, C_465, B_467) | ~v1_funct_1(E_468) | ~m1_subset_1(D_470, k1_zfmisc_1(A_469)) | v1_xboole_0(D_470) | ~m1_subset_1(C_465, k1_zfmisc_1(A_469)) | v1_xboole_0(C_465) | v1_xboole_0(B_467) | v1_xboole_0(A_469))), inference(cnfTransformation, [status(thm)], [f_197])).
% 9.32/3.31  tff(c_1687, plain, (![A_469, C_465, E_468]: (v1_funct_1(k1_tmap_1(A_469, '#skF_4', C_465, '#skF_6', E_468, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(C_465, '#skF_4'))) | ~v1_funct_2(E_468, C_465, '#skF_4') | ~v1_funct_1(E_468) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_469)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_465, k1_zfmisc_1(A_469)) | v1_xboole_0(C_465) | v1_xboole_0('#skF_4') | v1_xboole_0(A_469))), inference(resolution, [status(thm)], [c_60, c_1685])).
% 9.32/3.31  tff(c_1692, plain, (![A_469, C_465, E_468]: (v1_funct_1(k1_tmap_1(A_469, '#skF_4', C_465, '#skF_6', E_468, '#skF_8')) | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(C_465, '#skF_4'))) | ~v1_funct_2(E_468, C_465, '#skF_4') | ~v1_funct_1(E_468) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_469)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_465, k1_zfmisc_1(A_469)) | v1_xboole_0(C_465) | v1_xboole_0('#skF_4') | v1_xboole_0(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1687])).
% 9.32/3.31  tff(c_1710, plain, (![A_472, C_473, E_474]: (v1_funct_1(k1_tmap_1(A_472, '#skF_4', C_473, '#skF_6', E_474, '#skF_8')) | ~m1_subset_1(E_474, k1_zfmisc_1(k2_zfmisc_1(C_473, '#skF_4'))) | ~v1_funct_2(E_474, C_473, '#skF_4') | ~v1_funct_1(E_474) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_472)) | ~m1_subset_1(C_473, k1_zfmisc_1(A_472)) | v1_xboole_0(C_473) | v1_xboole_0(A_472))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1692])).
% 9.32/3.31  tff(c_1714, plain, (![A_472]: (v1_funct_1(k1_tmap_1(A_472, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_472)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_472)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_472))), inference(resolution, [status(thm)], [c_66, c_1710])).
% 9.32/3.31  tff(c_1721, plain, (![A_472]: (v1_funct_1(k1_tmap_1(A_472, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_472)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_472)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_472))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1714])).
% 9.32/3.31  tff(c_2102, plain, (![A_515]: (v1_funct_1(k1_tmap_1(A_515, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_515)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_515)) | v1_xboole_0(A_515))), inference(negUnitSimplification, [status(thm)], [c_80, c_1721])).
% 9.32/3.31  tff(c_2105, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2102])).
% 9.32/3.31  tff(c_2108, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2105])).
% 9.32/3.31  tff(c_2109, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_2108])).
% 9.32/3.31  tff(c_1533, plain, (![A_442, B_443, C_444, D_445]: (k2_partfun1(A_442, B_443, C_444, D_445)=k7_relat_1(C_444, D_445) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))) | ~v1_funct_1(C_444))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.32/3.31  tff(c_1537, plain, (![D_445]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_445)=k7_relat_1('#skF_7', D_445) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1533])).
% 9.32/3.31  tff(c_1543, plain, (![D_445]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_445)=k7_relat_1('#skF_7', D_445))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1537])).
% 9.32/3.31  tff(c_1535, plain, (![D_445]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_445)=k7_relat_1('#skF_8', D_445) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_1533])).
% 9.32/3.31  tff(c_1540, plain, (![D_445]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_445)=k7_relat_1('#skF_8', D_445))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1535])).
% 9.32/3.31  tff(c_2125, plain, (![A_521, C_522, F_525, D_526, E_524, B_523]: (k2_partfun1(k4_subset_1(A_521, C_522, D_526), B_523, k1_tmap_1(A_521, B_523, C_522, D_526, E_524, F_525), D_526)=F_525 | ~m1_subset_1(k1_tmap_1(A_521, B_523, C_522, D_526, E_524, F_525), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_521, C_522, D_526), B_523))) | ~v1_funct_2(k1_tmap_1(A_521, B_523, C_522, D_526, E_524, F_525), k4_subset_1(A_521, C_522, D_526), B_523) | ~v1_funct_1(k1_tmap_1(A_521, B_523, C_522, D_526, E_524, F_525)) | k2_partfun1(D_526, B_523, F_525, k9_subset_1(A_521, C_522, D_526))!=k2_partfun1(C_522, B_523, E_524, k9_subset_1(A_521, C_522, D_526)) | ~m1_subset_1(F_525, k1_zfmisc_1(k2_zfmisc_1(D_526, B_523))) | ~v1_funct_2(F_525, D_526, B_523) | ~v1_funct_1(F_525) | ~m1_subset_1(E_524, k1_zfmisc_1(k2_zfmisc_1(C_522, B_523))) | ~v1_funct_2(E_524, C_522, B_523) | ~v1_funct_1(E_524) | ~m1_subset_1(D_526, k1_zfmisc_1(A_521)) | v1_xboole_0(D_526) | ~m1_subset_1(C_522, k1_zfmisc_1(A_521)) | v1_xboole_0(C_522) | v1_xboole_0(B_523) | v1_xboole_0(A_521))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.32/3.31  tff(c_4586, plain, (![F_763, D_767, C_762, A_766, E_765, B_764]: (k2_partfun1(k4_subset_1(A_766, C_762, D_767), B_764, k1_tmap_1(A_766, B_764, C_762, D_767, E_765, F_763), D_767)=F_763 | ~v1_funct_2(k1_tmap_1(A_766, B_764, C_762, D_767, E_765, F_763), k4_subset_1(A_766, C_762, D_767), B_764) | ~v1_funct_1(k1_tmap_1(A_766, B_764, C_762, D_767, E_765, F_763)) | k2_partfun1(D_767, B_764, F_763, k9_subset_1(A_766, C_762, D_767))!=k2_partfun1(C_762, B_764, E_765, k9_subset_1(A_766, C_762, D_767)) | ~m1_subset_1(F_763, k1_zfmisc_1(k2_zfmisc_1(D_767, B_764))) | ~v1_funct_2(F_763, D_767, B_764) | ~v1_funct_1(F_763) | ~m1_subset_1(E_765, k1_zfmisc_1(k2_zfmisc_1(C_762, B_764))) | ~v1_funct_2(E_765, C_762, B_764) | ~v1_funct_1(E_765) | ~m1_subset_1(D_767, k1_zfmisc_1(A_766)) | v1_xboole_0(D_767) | ~m1_subset_1(C_762, k1_zfmisc_1(A_766)) | v1_xboole_0(C_762) | v1_xboole_0(B_764) | v1_xboole_0(A_766))), inference(resolution, [status(thm)], [c_52, c_2125])).
% 9.32/3.31  tff(c_5284, plain, (![E_818, A_819, B_817, D_820, C_815, F_816]: (k2_partfun1(k4_subset_1(A_819, C_815, D_820), B_817, k1_tmap_1(A_819, B_817, C_815, D_820, E_818, F_816), D_820)=F_816 | ~v1_funct_1(k1_tmap_1(A_819, B_817, C_815, D_820, E_818, F_816)) | k2_partfun1(D_820, B_817, F_816, k9_subset_1(A_819, C_815, D_820))!=k2_partfun1(C_815, B_817, E_818, k9_subset_1(A_819, C_815, D_820)) | ~m1_subset_1(F_816, k1_zfmisc_1(k2_zfmisc_1(D_820, B_817))) | ~v1_funct_2(F_816, D_820, B_817) | ~v1_funct_1(F_816) | ~m1_subset_1(E_818, k1_zfmisc_1(k2_zfmisc_1(C_815, B_817))) | ~v1_funct_2(E_818, C_815, B_817) | ~v1_funct_1(E_818) | ~m1_subset_1(D_820, k1_zfmisc_1(A_819)) | v1_xboole_0(D_820) | ~m1_subset_1(C_815, k1_zfmisc_1(A_819)) | v1_xboole_0(C_815) | v1_xboole_0(B_817) | v1_xboole_0(A_819))), inference(resolution, [status(thm)], [c_54, c_4586])).
% 9.32/3.31  tff(c_5288, plain, (![A_819, C_815, E_818]: (k2_partfun1(k4_subset_1(A_819, C_815, '#skF_6'), '#skF_4', k1_tmap_1(A_819, '#skF_4', C_815, '#skF_6', E_818, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_819, '#skF_4', C_815, '#skF_6', E_818, '#skF_8')) | k2_partfun1(C_815, '#skF_4', E_818, k9_subset_1(A_819, C_815, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_819, C_815, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_818, k1_zfmisc_1(k2_zfmisc_1(C_815, '#skF_4'))) | ~v1_funct_2(E_818, C_815, '#skF_4') | ~v1_funct_1(E_818) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_819)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_815, k1_zfmisc_1(A_819)) | v1_xboole_0(C_815) | v1_xboole_0('#skF_4') | v1_xboole_0(A_819))), inference(resolution, [status(thm)], [c_60, c_5284])).
% 9.32/3.31  tff(c_5294, plain, (![A_819, C_815, E_818]: (k2_partfun1(k4_subset_1(A_819, C_815, '#skF_6'), '#skF_4', k1_tmap_1(A_819, '#skF_4', C_815, '#skF_6', E_818, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_819, '#skF_4', C_815, '#skF_6', E_818, '#skF_8')) | k2_partfun1(C_815, '#skF_4', E_818, k9_subset_1(A_819, C_815, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_819, C_815, '#skF_6')) | ~m1_subset_1(E_818, k1_zfmisc_1(k2_zfmisc_1(C_815, '#skF_4'))) | ~v1_funct_2(E_818, C_815, '#skF_4') | ~v1_funct_1(E_818) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_819)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_815, k1_zfmisc_1(A_819)) | v1_xboole_0(C_815) | v1_xboole_0('#skF_4') | v1_xboole_0(A_819))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1540, c_5288])).
% 9.32/3.31  tff(c_5918, plain, (![A_866, C_867, E_868]: (k2_partfun1(k4_subset_1(A_866, C_867, '#skF_6'), '#skF_4', k1_tmap_1(A_866, '#skF_4', C_867, '#skF_6', E_868, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_866, '#skF_4', C_867, '#skF_6', E_868, '#skF_8')) | k2_partfun1(C_867, '#skF_4', E_868, k9_subset_1(A_866, C_867, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_866, C_867, '#skF_6')) | ~m1_subset_1(E_868, k1_zfmisc_1(k2_zfmisc_1(C_867, '#skF_4'))) | ~v1_funct_2(E_868, C_867, '#skF_4') | ~v1_funct_1(E_868) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_866)) | ~m1_subset_1(C_867, k1_zfmisc_1(A_866)) | v1_xboole_0(C_867) | v1_xboole_0(A_866))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_5294])).
% 9.32/3.31  tff(c_5925, plain, (![A_866]: (k2_partfun1(k4_subset_1(A_866, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_866, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_866, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_866, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_866, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_866)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_866)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_866))), inference(resolution, [status(thm)], [c_66, c_5918])).
% 9.32/3.31  tff(c_5935, plain, (![A_866]: (k2_partfun1(k4_subset_1(A_866, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_866, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_866, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_866, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_866, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_866)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_866)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_866))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1543, c_5925])).
% 9.32/3.31  tff(c_5945, plain, (![A_869]: (k2_partfun1(k4_subset_1(A_869, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_869, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_869, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_869, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_869, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_869)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_869)) | v1_xboole_0(A_869))), inference(negUnitSimplification, [status(thm)], [c_80, c_5935])).
% 9.32/3.31  tff(c_135, plain, (![C_247, A_248, B_249]: (v1_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.32/3.31  tff(c_143, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_135])).
% 9.32/3.31  tff(c_243, plain, (![B_271, A_272]: (k7_relat_1(B_271, A_272)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_271), A_272) | ~v1_relat_1(B_271))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.32/3.31  tff(c_279, plain, (![B_274]: (k7_relat_1(B_274, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_274))), inference(resolution, [status(thm)], [c_16, c_243])).
% 9.32/3.31  tff(c_286, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_143, c_279])).
% 9.32/3.31  tff(c_470, plain, (![A_305, B_306, C_307, D_308]: (k2_partfun1(A_305, B_306, C_307, D_308)=k7_relat_1(C_307, D_308) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | ~v1_funct_1(C_307))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.32/3.31  tff(c_474, plain, (![D_308]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_308)=k7_relat_1('#skF_7', D_308) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_470])).
% 9.32/3.31  tff(c_480, plain, (![D_308]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_308)=k7_relat_1('#skF_7', D_308))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_474])).
% 9.32/3.31  tff(c_142, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_135])).
% 9.32/3.31  tff(c_287, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_279])).
% 9.32/3.31  tff(c_472, plain, (![D_308]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_308)=k7_relat_1('#skF_8', D_308) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_470])).
% 9.32/3.31  tff(c_477, plain, (![D_308]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_308)=k7_relat_1('#skF_8', D_308))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_472])).
% 9.32/3.31  tff(c_316, plain, (![A_281, B_282]: (r1_xboole_0(A_281, B_282) | ~r1_subset_1(A_281, B_282) | v1_xboole_0(B_282) | v1_xboole_0(A_281))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.32/3.31  tff(c_458, plain, (![A_303, B_304]: (k3_xboole_0(A_303, B_304)=k1_xboole_0 | ~r1_subset_1(A_303, B_304) | v1_xboole_0(B_304) | v1_xboole_0(A_303))), inference(resolution, [status(thm)], [c_316, c_6])).
% 9.32/3.31  tff(c_461, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_458])).
% 9.32/3.31  tff(c_464, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_76, c_461])).
% 9.32/3.31  tff(c_371, plain, (![A_289, B_290, C_291]: (k9_subset_1(A_289, B_290, C_291)=k3_xboole_0(B_290, C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(A_289)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.32/3.31  tff(c_383, plain, (![B_290]: (k9_subset_1('#skF_3', B_290, '#skF_6')=k3_xboole_0(B_290, '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_371])).
% 9.32/3.31  tff(c_58, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.32/3.31  tff(c_109, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_58])).
% 9.32/3.31  tff(c_393, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_383, c_109])).
% 9.32/3.31  tff(c_465, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k1_xboole_0)!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_464, c_464, c_393])).
% 9.32/3.31  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_480, c_287, c_477, c_465])).
% 9.32/3.31  tff(c_501, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 9.32/3.31  tff(c_546, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_501])).
% 9.32/3.31  tff(c_5956, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5945, c_546])).
% 9.32/3.31  tff(c_5970, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_713, c_1608, c_712, c_1608, c_771, c_771, c_2109, c_5956])).
% 9.32/3.31  tff(c_5972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_5970])).
% 9.32/3.31  tff(c_5973, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_501])).
% 9.32/3.31  tff(c_11098, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11089, c_5973])).
% 9.32/3.31  tff(c_11109, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_6106, c_7193, c_6105, c_7193, c_7099, c_7099, c_7848, c_11098])).
% 9.32/3.31  tff(c_11111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_11109])).
% 9.32/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.31  
% 9.32/3.31  Inference rules
% 9.32/3.31  ----------------------
% 9.32/3.31  #Ref     : 0
% 9.32/3.31  #Sup     : 2248
% 9.32/3.31  #Fact    : 0
% 9.32/3.31  #Define  : 0
% 9.32/3.31  #Split   : 30
% 9.32/3.31  #Chain   : 0
% 9.32/3.31  #Close   : 0
% 9.32/3.31  
% 9.32/3.31  Ordering : KBO
% 9.32/3.31  
% 9.32/3.31  Simplification rules
% 9.32/3.31  ----------------------
% 9.32/3.31  #Subsume      : 547
% 9.32/3.31  #Demod        : 1373
% 9.32/3.31  #Tautology    : 742
% 9.32/3.31  #SimpNegUnit  : 384
% 9.32/3.31  #BackRed      : 11
% 9.32/3.31  
% 9.32/3.31  #Partial instantiations: 0
% 9.32/3.31  #Strategies tried      : 1
% 9.32/3.31  
% 9.32/3.31  Timing (in seconds)
% 9.32/3.31  ----------------------
% 9.36/3.31  Preprocessing        : 0.40
% 9.36/3.31  Parsing              : 0.19
% 9.36/3.31  CNF conversion       : 0.06
% 9.36/3.31  Main loop            : 2.07
% 9.36/3.31  Inferencing          : 0.73
% 9.36/3.31  Reduction            : 0.68
% 9.36/3.31  Demodulation         : 0.47
% 9.36/3.31  BG Simplification    : 0.06
% 9.36/3.31  Subsumption          : 0.45
% 9.36/3.31  Abstraction          : 0.08
% 9.36/3.31  MUC search           : 0.00
% 9.36/3.31  Cooper               : 0.00
% 9.36/3.31  Total                : 2.55
% 9.36/3.31  Index Insertion      : 0.00
% 9.36/3.31  Index Deletion       : 0.00
% 9.36/3.31  Index Matching       : 0.00
% 9.36/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
