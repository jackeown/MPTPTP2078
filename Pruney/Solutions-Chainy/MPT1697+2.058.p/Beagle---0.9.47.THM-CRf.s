%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:18 EST 2020

% Result     : Theorem 9.20s
% Output     : CNFRefutation 9.52s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 831 expanded)
%              Number of leaves         :   47 ( 307 expanded)
%              Depth                    :   18
%              Number of atoms          :  724 (3995 expanded)
%              Number of equality atoms :  146 ( 744 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_233,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_191,axiom,(
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

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_157,axiom,(
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

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_97,plain,(
    ! [C_229,A_230,B_231] :
      ( v1_relat_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_105,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_97])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [B_226,A_227] :
      ( r1_xboole_0(B_226,A_227)
      | ~ r1_xboole_0(A_227,B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_851,plain,(
    ! [A_321,B_322] :
      ( k7_relat_1(A_321,B_322) = k1_xboole_0
      | ~ r1_xboole_0(B_322,k1_relat_1(A_321))
      | ~ v1_relat_1(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_873,plain,(
    ! [A_324] :
      ( k7_relat_1(A_324,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_324) ) ),
    inference(resolution,[status(thm)],[c_91,c_851])).

tff(c_880,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_873])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_66,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | ~ r1_subset_1(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_104,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_97])).

tff(c_804,plain,(
    ! [C_311,A_312,B_313] :
      ( v4_relat_1(C_311,A_312)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_811,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_804])).

tff(c_813,plain,(
    ! [B_314,A_315] :
      ( k7_relat_1(B_314,A_315) = B_314
      | ~ v4_relat_1(B_314,A_315)
      | ~ v1_relat_1(B_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_819,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_811,c_813])).

tff(c_825,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_819])).

tff(c_5069,plain,(
    ! [C_934,A_935,B_936] :
      ( k7_relat_1(k7_relat_1(C_934,A_935),B_936) = k1_xboole_0
      | ~ r1_xboole_0(A_935,B_936)
      | ~ v1_relat_1(C_934) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5090,plain,(
    ! [B_936] :
      ( k7_relat_1('#skF_5',B_936) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_936)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_5069])).

tff(c_5116,plain,(
    ! [B_938] :
      ( k7_relat_1('#skF_5',B_938) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_938) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5090])).

tff(c_5124,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_5116])).

tff(c_5159,plain,(
    ! [B_941] :
      ( k7_relat_1('#skF_5',B_941) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_941)
      | v1_xboole_0(B_941) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5124])).

tff(c_5162,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_5159])).

tff(c_5165,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5162])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_5265,plain,(
    ! [B_953,A_954] :
      ( k1_relat_1(B_953) = A_954
      | ~ v1_partfun1(B_953,A_954)
      | ~ v4_relat_1(B_953,A_954)
      | ~ v1_relat_1(B_953) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5271,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_811,c_5265])).

tff(c_5277,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5271])).

tff(c_5599,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5277])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_5885,plain,(
    ! [C_1010,A_1011,B_1012] :
      ( v1_partfun1(C_1010,A_1011)
      | ~ v1_funct_2(C_1010,A_1011,B_1012)
      | ~ v1_funct_1(C_1010)
      | ~ m1_subset_1(C_1010,k1_zfmisc_1(k2_zfmisc_1(A_1011,B_1012)))
      | v1_xboole_0(B_1012) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5888,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_5885])).

tff(c_5894,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_5888])).

tff(c_5896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5599,c_5894])).

tff(c_5897,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5277])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k3_xboole_0(k1_relat_1(B_16),A_15) = k1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5902,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_15)) = k3_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5897,c_18])).

tff(c_5957,plain,(
    ! [A_1015] : k1_relat_1(k7_relat_1('#skF_5',A_1015)) = k3_xboole_0('#skF_3',A_1015) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5902])).

tff(c_5975,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5165,c_5957])).

tff(c_5985,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5975])).

tff(c_881,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_873])).

tff(c_5191,plain,(
    ! [A_943,B_944,C_945] :
      ( k9_subset_1(A_943,B_944,C_945) = k3_xboole_0(B_944,C_945)
      | ~ m1_subset_1(C_945,k1_zfmisc_1(A_943)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5203,plain,(
    ! [B_944] : k9_subset_1('#skF_1',B_944,'#skF_4') = k3_xboole_0(B_944,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_5191])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_6367,plain,(
    ! [E_1050,B_1046,C_1051,D_1048,A_1049,F_1047] :
      ( v1_funct_1(k1_tmap_1(A_1049,B_1046,C_1051,D_1048,E_1050,F_1047))
      | ~ m1_subset_1(F_1047,k1_zfmisc_1(k2_zfmisc_1(D_1048,B_1046)))
      | ~ v1_funct_2(F_1047,D_1048,B_1046)
      | ~ v1_funct_1(F_1047)
      | ~ m1_subset_1(E_1050,k1_zfmisc_1(k2_zfmisc_1(C_1051,B_1046)))
      | ~ v1_funct_2(E_1050,C_1051,B_1046)
      | ~ v1_funct_1(E_1050)
      | ~ m1_subset_1(D_1048,k1_zfmisc_1(A_1049))
      | v1_xboole_0(D_1048)
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(A_1049))
      | v1_xboole_0(C_1051)
      | v1_xboole_0(B_1046)
      | v1_xboole_0(A_1049) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_6371,plain,(
    ! [A_1049,C_1051,E_1050] :
      ( v1_funct_1(k1_tmap_1(A_1049,'#skF_2',C_1051,'#skF_4',E_1050,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1050,k1_zfmisc_1(k2_zfmisc_1(C_1051,'#skF_2')))
      | ~ v1_funct_2(E_1050,C_1051,'#skF_2')
      | ~ v1_funct_1(E_1050)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1049))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(A_1049))
      | v1_xboole_0(C_1051)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1049) ) ),
    inference(resolution,[status(thm)],[c_54,c_6367])).

tff(c_6378,plain,(
    ! [A_1049,C_1051,E_1050] :
      ( v1_funct_1(k1_tmap_1(A_1049,'#skF_2',C_1051,'#skF_4',E_1050,'#skF_6'))
      | ~ m1_subset_1(E_1050,k1_zfmisc_1(k2_zfmisc_1(C_1051,'#skF_2')))
      | ~ v1_funct_2(E_1050,C_1051,'#skF_2')
      | ~ v1_funct_1(E_1050)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1049))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(A_1049))
      | v1_xboole_0(C_1051)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1049) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_6371])).

tff(c_6395,plain,(
    ! [A_1054,C_1055,E_1056] :
      ( v1_funct_1(k1_tmap_1(A_1054,'#skF_2',C_1055,'#skF_4',E_1056,'#skF_6'))
      | ~ m1_subset_1(E_1056,k1_zfmisc_1(k2_zfmisc_1(C_1055,'#skF_2')))
      | ~ v1_funct_2(E_1056,C_1055,'#skF_2')
      | ~ v1_funct_1(E_1056)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1054))
      | ~ m1_subset_1(C_1055,k1_zfmisc_1(A_1054))
      | v1_xboole_0(C_1055)
      | v1_xboole_0(A_1054) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_6378])).

tff(c_6397,plain,(
    ! [A_1054] :
      ( v1_funct_1(k1_tmap_1(A_1054,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1054))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1054))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1054) ) ),
    inference(resolution,[status(thm)],[c_60,c_6395])).

tff(c_6402,plain,(
    ! [A_1054] :
      ( v1_funct_1(k1_tmap_1(A_1054,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1054))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1054))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1054) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6397])).

tff(c_6416,plain,(
    ! [A_1058] :
      ( v1_funct_1(k1_tmap_1(A_1058,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1058))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1058))
      | v1_xboole_0(A_1058) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_6402])).

tff(c_6419,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_6416])).

tff(c_6422,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6419])).

tff(c_6423,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6422])).

tff(c_6032,plain,(
    ! [A_1017,B_1018,C_1019,D_1020] :
      ( k2_partfun1(A_1017,B_1018,C_1019,D_1020) = k7_relat_1(C_1019,D_1020)
      | ~ m1_subset_1(C_1019,k1_zfmisc_1(k2_zfmisc_1(A_1017,B_1018)))
      | ~ v1_funct_1(C_1019) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6034,plain,(
    ! [D_1020] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1020) = k7_relat_1('#skF_5',D_1020)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_6032])).

tff(c_6039,plain,(
    ! [D_1020] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1020) = k7_relat_1('#skF_5',D_1020) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6034])).

tff(c_6036,plain,(
    ! [D_1020] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1020) = k7_relat_1('#skF_6',D_1020)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_6032])).

tff(c_6042,plain,(
    ! [D_1020] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1020) = k7_relat_1('#skF_6',D_1020) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6036])).

tff(c_48,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_46,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_6671,plain,(
    ! [A_1099,C_1103,D_1102,F_1098,E_1100,B_1101] :
      ( k2_partfun1(k4_subset_1(A_1099,C_1103,D_1102),B_1101,k1_tmap_1(A_1099,B_1101,C_1103,D_1102,E_1100,F_1098),C_1103) = E_1100
      | ~ m1_subset_1(k1_tmap_1(A_1099,B_1101,C_1103,D_1102,E_1100,F_1098),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1099,C_1103,D_1102),B_1101)))
      | ~ v1_funct_2(k1_tmap_1(A_1099,B_1101,C_1103,D_1102,E_1100,F_1098),k4_subset_1(A_1099,C_1103,D_1102),B_1101)
      | ~ v1_funct_1(k1_tmap_1(A_1099,B_1101,C_1103,D_1102,E_1100,F_1098))
      | k2_partfun1(D_1102,B_1101,F_1098,k9_subset_1(A_1099,C_1103,D_1102)) != k2_partfun1(C_1103,B_1101,E_1100,k9_subset_1(A_1099,C_1103,D_1102))
      | ~ m1_subset_1(F_1098,k1_zfmisc_1(k2_zfmisc_1(D_1102,B_1101)))
      | ~ v1_funct_2(F_1098,D_1102,B_1101)
      | ~ v1_funct_1(F_1098)
      | ~ m1_subset_1(E_1100,k1_zfmisc_1(k2_zfmisc_1(C_1103,B_1101)))
      | ~ v1_funct_2(E_1100,C_1103,B_1101)
      | ~ v1_funct_1(E_1100)
      | ~ m1_subset_1(D_1102,k1_zfmisc_1(A_1099))
      | v1_xboole_0(D_1102)
      | ~ m1_subset_1(C_1103,k1_zfmisc_1(A_1099))
      | v1_xboole_0(C_1103)
      | v1_xboole_0(B_1101)
      | v1_xboole_0(A_1099) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_8096,plain,(
    ! [B_1306,C_1311,D_1308,A_1309,F_1307,E_1310] :
      ( k2_partfun1(k4_subset_1(A_1309,C_1311,D_1308),B_1306,k1_tmap_1(A_1309,B_1306,C_1311,D_1308,E_1310,F_1307),C_1311) = E_1310
      | ~ v1_funct_2(k1_tmap_1(A_1309,B_1306,C_1311,D_1308,E_1310,F_1307),k4_subset_1(A_1309,C_1311,D_1308),B_1306)
      | ~ v1_funct_1(k1_tmap_1(A_1309,B_1306,C_1311,D_1308,E_1310,F_1307))
      | k2_partfun1(D_1308,B_1306,F_1307,k9_subset_1(A_1309,C_1311,D_1308)) != k2_partfun1(C_1311,B_1306,E_1310,k9_subset_1(A_1309,C_1311,D_1308))
      | ~ m1_subset_1(F_1307,k1_zfmisc_1(k2_zfmisc_1(D_1308,B_1306)))
      | ~ v1_funct_2(F_1307,D_1308,B_1306)
      | ~ v1_funct_1(F_1307)
      | ~ m1_subset_1(E_1310,k1_zfmisc_1(k2_zfmisc_1(C_1311,B_1306)))
      | ~ v1_funct_2(E_1310,C_1311,B_1306)
      | ~ v1_funct_1(E_1310)
      | ~ m1_subset_1(D_1308,k1_zfmisc_1(A_1309))
      | v1_xboole_0(D_1308)
      | ~ m1_subset_1(C_1311,k1_zfmisc_1(A_1309))
      | v1_xboole_0(C_1311)
      | v1_xboole_0(B_1306)
      | v1_xboole_0(A_1309) ) ),
    inference(resolution,[status(thm)],[c_46,c_6671])).

tff(c_8963,plain,(
    ! [C_1488,A_1486,E_1487,D_1485,F_1484,B_1483] :
      ( k2_partfun1(k4_subset_1(A_1486,C_1488,D_1485),B_1483,k1_tmap_1(A_1486,B_1483,C_1488,D_1485,E_1487,F_1484),C_1488) = E_1487
      | ~ v1_funct_1(k1_tmap_1(A_1486,B_1483,C_1488,D_1485,E_1487,F_1484))
      | k2_partfun1(D_1485,B_1483,F_1484,k9_subset_1(A_1486,C_1488,D_1485)) != k2_partfun1(C_1488,B_1483,E_1487,k9_subset_1(A_1486,C_1488,D_1485))
      | ~ m1_subset_1(F_1484,k1_zfmisc_1(k2_zfmisc_1(D_1485,B_1483)))
      | ~ v1_funct_2(F_1484,D_1485,B_1483)
      | ~ v1_funct_1(F_1484)
      | ~ m1_subset_1(E_1487,k1_zfmisc_1(k2_zfmisc_1(C_1488,B_1483)))
      | ~ v1_funct_2(E_1487,C_1488,B_1483)
      | ~ v1_funct_1(E_1487)
      | ~ m1_subset_1(D_1485,k1_zfmisc_1(A_1486))
      | v1_xboole_0(D_1485)
      | ~ m1_subset_1(C_1488,k1_zfmisc_1(A_1486))
      | v1_xboole_0(C_1488)
      | v1_xboole_0(B_1483)
      | v1_xboole_0(A_1486) ) ),
    inference(resolution,[status(thm)],[c_48,c_8096])).

tff(c_8969,plain,(
    ! [A_1486,C_1488,E_1487] :
      ( k2_partfun1(k4_subset_1(A_1486,C_1488,'#skF_4'),'#skF_2',k1_tmap_1(A_1486,'#skF_2',C_1488,'#skF_4',E_1487,'#skF_6'),C_1488) = E_1487
      | ~ v1_funct_1(k1_tmap_1(A_1486,'#skF_2',C_1488,'#skF_4',E_1487,'#skF_6'))
      | k2_partfun1(C_1488,'#skF_2',E_1487,k9_subset_1(A_1486,C_1488,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1486,C_1488,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1487,k1_zfmisc_1(k2_zfmisc_1(C_1488,'#skF_2')))
      | ~ v1_funct_2(E_1487,C_1488,'#skF_2')
      | ~ v1_funct_1(E_1487)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1486))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1488,k1_zfmisc_1(A_1486))
      | v1_xboole_0(C_1488)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1486) ) ),
    inference(resolution,[status(thm)],[c_54,c_8963])).

tff(c_8977,plain,(
    ! [A_1486,C_1488,E_1487] :
      ( k2_partfun1(k4_subset_1(A_1486,C_1488,'#skF_4'),'#skF_2',k1_tmap_1(A_1486,'#skF_2',C_1488,'#skF_4',E_1487,'#skF_6'),C_1488) = E_1487
      | ~ v1_funct_1(k1_tmap_1(A_1486,'#skF_2',C_1488,'#skF_4',E_1487,'#skF_6'))
      | k2_partfun1(C_1488,'#skF_2',E_1487,k9_subset_1(A_1486,C_1488,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1486,C_1488,'#skF_4'))
      | ~ m1_subset_1(E_1487,k1_zfmisc_1(k2_zfmisc_1(C_1488,'#skF_2')))
      | ~ v1_funct_2(E_1487,C_1488,'#skF_2')
      | ~ v1_funct_1(E_1487)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1486))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1488,k1_zfmisc_1(A_1486))
      | v1_xboole_0(C_1488)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_6042,c_8969])).

tff(c_9289,plain,(
    ! [A_1539,C_1540,E_1541] :
      ( k2_partfun1(k4_subset_1(A_1539,C_1540,'#skF_4'),'#skF_2',k1_tmap_1(A_1539,'#skF_2',C_1540,'#skF_4',E_1541,'#skF_6'),C_1540) = E_1541
      | ~ v1_funct_1(k1_tmap_1(A_1539,'#skF_2',C_1540,'#skF_4',E_1541,'#skF_6'))
      | k2_partfun1(C_1540,'#skF_2',E_1541,k9_subset_1(A_1539,C_1540,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1539,C_1540,'#skF_4'))
      | ~ m1_subset_1(E_1541,k1_zfmisc_1(k2_zfmisc_1(C_1540,'#skF_2')))
      | ~ v1_funct_2(E_1541,C_1540,'#skF_2')
      | ~ v1_funct_1(E_1541)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1539))
      | ~ m1_subset_1(C_1540,k1_zfmisc_1(A_1539))
      | v1_xboole_0(C_1540)
      | v1_xboole_0(A_1539) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_8977])).

tff(c_9294,plain,(
    ! [A_1539] :
      ( k2_partfun1(k4_subset_1(A_1539,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1539,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1539,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1539,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1539,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1539))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1539))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1539) ) ),
    inference(resolution,[status(thm)],[c_60,c_9289])).

tff(c_9302,plain,(
    ! [A_1539] :
      ( k2_partfun1(k4_subset_1(A_1539,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1539,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1539,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1539,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1539,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1539))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1539))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_6039,c_9294])).

tff(c_9308,plain,(
    ! [A_1542] :
      ( k2_partfun1(k4_subset_1(A_1542,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1542,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1542,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1542,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1542,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1542))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1542))
      | v1_xboole_0(A_1542) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_9302])).

tff(c_918,plain,(
    ! [C_329,A_330,B_331] :
      ( k7_relat_1(k7_relat_1(C_329,A_330),B_331) = k1_xboole_0
      | ~ r1_xboole_0(A_330,B_331)
      | ~ v1_relat_1(C_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_939,plain,(
    ! [B_331] :
      ( k7_relat_1('#skF_5',B_331) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_331)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_918])).

tff(c_965,plain,(
    ! [B_333] :
      ( k7_relat_1('#skF_5',B_333) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_939])).

tff(c_969,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_965])).

tff(c_979,plain,(
    ! [B_334] :
      ( k7_relat_1('#skF_5',B_334) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_334)
      | v1_xboole_0(B_334) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_969])).

tff(c_982,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_979])).

tff(c_985,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_982])).

tff(c_1127,plain,(
    ! [B_350,A_351] :
      ( k1_relat_1(B_350) = A_351
      | ~ v1_partfun1(B_350,A_351)
      | ~ v4_relat_1(B_350,A_351)
      | ~ v1_relat_1(B_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1133,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_811,c_1127])).

tff(c_1139,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1133])).

tff(c_1452,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_1658,plain,(
    ! [C_399,A_400,B_401] :
      ( v1_partfun1(C_399,A_400)
      | ~ v1_funct_2(C_399,A_400,B_401)
      | ~ v1_funct_1(C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401)))
      | v1_xboole_0(B_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1661,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1658])).

tff(c_1667,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1661])).

tff(c_1669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1452,c_1667])).

tff(c_1670,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_1675,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_15)) = k3_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1670,c_18])).

tff(c_1692,plain,(
    ! [A_402] : k1_relat_1(k7_relat_1('#skF_5',A_402)) = k3_xboole_0('#skF_3',A_402) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1675])).

tff(c_1710,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_1692])).

tff(c_1720,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1710])).

tff(c_1044,plain,(
    ! [A_340,B_341,C_342] :
      ( k9_subset_1(A_340,B_341,C_342) = k3_xboole_0(B_341,C_342)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(A_340)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1056,plain,(
    ! [B_341] : k9_subset_1('#skF_1',B_341,'#skF_4') = k3_xboole_0(B_341,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1044])).

tff(c_2119,plain,(
    ! [C_439,D_436,B_434,A_437,F_435,E_438] :
      ( v1_funct_1(k1_tmap_1(A_437,B_434,C_439,D_436,E_438,F_435))
      | ~ m1_subset_1(F_435,k1_zfmisc_1(k2_zfmisc_1(D_436,B_434)))
      | ~ v1_funct_2(F_435,D_436,B_434)
      | ~ v1_funct_1(F_435)
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(C_439,B_434)))
      | ~ v1_funct_2(E_438,C_439,B_434)
      | ~ v1_funct_1(E_438)
      | ~ m1_subset_1(D_436,k1_zfmisc_1(A_437))
      | v1_xboole_0(D_436)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(A_437))
      | v1_xboole_0(C_439)
      | v1_xboole_0(B_434)
      | v1_xboole_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2123,plain,(
    ! [A_437,C_439,E_438] :
      ( v1_funct_1(k1_tmap_1(A_437,'#skF_2',C_439,'#skF_4',E_438,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(C_439,'#skF_2')))
      | ~ v1_funct_2(E_438,C_439,'#skF_2')
      | ~ v1_funct_1(E_438)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_437))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_439,k1_zfmisc_1(A_437))
      | v1_xboole_0(C_439)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_437) ) ),
    inference(resolution,[status(thm)],[c_54,c_2119])).

tff(c_2130,plain,(
    ! [A_437,C_439,E_438] :
      ( v1_funct_1(k1_tmap_1(A_437,'#skF_2',C_439,'#skF_4',E_438,'#skF_6'))
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(C_439,'#skF_2')))
      | ~ v1_funct_2(E_438,C_439,'#skF_2')
      | ~ v1_funct_1(E_438)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_437))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_439,k1_zfmisc_1(A_437))
      | v1_xboole_0(C_439)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2123])).

tff(c_2252,plain,(
    ! [A_456,C_457,E_458] :
      ( v1_funct_1(k1_tmap_1(A_456,'#skF_2',C_457,'#skF_4',E_458,'#skF_6'))
      | ~ m1_subset_1(E_458,k1_zfmisc_1(k2_zfmisc_1(C_457,'#skF_2')))
      | ~ v1_funct_2(E_458,C_457,'#skF_2')
      | ~ v1_funct_1(E_458)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_456))
      | ~ m1_subset_1(C_457,k1_zfmisc_1(A_456))
      | v1_xboole_0(C_457)
      | v1_xboole_0(A_456) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_2130])).

tff(c_2254,plain,(
    ! [A_456] :
      ( v1_funct_1(k1_tmap_1(A_456,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_456))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_456))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_456) ) ),
    inference(resolution,[status(thm)],[c_60,c_2252])).

tff(c_2259,plain,(
    ! [A_456] :
      ( v1_funct_1(k1_tmap_1(A_456,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_456))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_456))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2254])).

tff(c_2272,plain,(
    ! [A_460] :
      ( v1_funct_1(k1_tmap_1(A_460,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_460))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_460))
      | v1_xboole_0(A_460) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2259])).

tff(c_2275,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_2272])).

tff(c_2278,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2275])).

tff(c_2279,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2278])).

tff(c_1771,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( k2_partfun1(A_404,B_405,C_406,D_407) = k7_relat_1(C_406,D_407)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_404,B_405)))
      | ~ v1_funct_1(C_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1773,plain,(
    ! [D_407] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_407) = k7_relat_1('#skF_5',D_407)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_1771])).

tff(c_1778,plain,(
    ! [D_407] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_407) = k7_relat_1('#skF_5',D_407) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1773])).

tff(c_1775,plain,(
    ! [D_407] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_407) = k7_relat_1('#skF_6',D_407)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_1771])).

tff(c_1781,plain,(
    ! [D_407] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_407) = k7_relat_1('#skF_6',D_407) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1775])).

tff(c_2427,plain,(
    ! [A_485,C_489,D_488,E_486,B_487,F_484] :
      ( k2_partfun1(k4_subset_1(A_485,C_489,D_488),B_487,k1_tmap_1(A_485,B_487,C_489,D_488,E_486,F_484),D_488) = F_484
      | ~ m1_subset_1(k1_tmap_1(A_485,B_487,C_489,D_488,E_486,F_484),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_485,C_489,D_488),B_487)))
      | ~ v1_funct_2(k1_tmap_1(A_485,B_487,C_489,D_488,E_486,F_484),k4_subset_1(A_485,C_489,D_488),B_487)
      | ~ v1_funct_1(k1_tmap_1(A_485,B_487,C_489,D_488,E_486,F_484))
      | k2_partfun1(D_488,B_487,F_484,k9_subset_1(A_485,C_489,D_488)) != k2_partfun1(C_489,B_487,E_486,k9_subset_1(A_485,C_489,D_488))
      | ~ m1_subset_1(F_484,k1_zfmisc_1(k2_zfmisc_1(D_488,B_487)))
      | ~ v1_funct_2(F_484,D_488,B_487)
      | ~ v1_funct_1(F_484)
      | ~ m1_subset_1(E_486,k1_zfmisc_1(k2_zfmisc_1(C_489,B_487)))
      | ~ v1_funct_2(E_486,C_489,B_487)
      | ~ v1_funct_1(E_486)
      | ~ m1_subset_1(D_488,k1_zfmisc_1(A_485))
      | v1_xboole_0(D_488)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(A_485))
      | v1_xboole_0(C_489)
      | v1_xboole_0(B_487)
      | v1_xboole_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3637,plain,(
    ! [B_664,A_667,C_669,D_666,E_668,F_665] :
      ( k2_partfun1(k4_subset_1(A_667,C_669,D_666),B_664,k1_tmap_1(A_667,B_664,C_669,D_666,E_668,F_665),D_666) = F_665
      | ~ v1_funct_2(k1_tmap_1(A_667,B_664,C_669,D_666,E_668,F_665),k4_subset_1(A_667,C_669,D_666),B_664)
      | ~ v1_funct_1(k1_tmap_1(A_667,B_664,C_669,D_666,E_668,F_665))
      | k2_partfun1(D_666,B_664,F_665,k9_subset_1(A_667,C_669,D_666)) != k2_partfun1(C_669,B_664,E_668,k9_subset_1(A_667,C_669,D_666))
      | ~ m1_subset_1(F_665,k1_zfmisc_1(k2_zfmisc_1(D_666,B_664)))
      | ~ v1_funct_2(F_665,D_666,B_664)
      | ~ v1_funct_1(F_665)
      | ~ m1_subset_1(E_668,k1_zfmisc_1(k2_zfmisc_1(C_669,B_664)))
      | ~ v1_funct_2(E_668,C_669,B_664)
      | ~ v1_funct_1(E_668)
      | ~ m1_subset_1(D_666,k1_zfmisc_1(A_667))
      | v1_xboole_0(D_666)
      | ~ m1_subset_1(C_669,k1_zfmisc_1(A_667))
      | v1_xboole_0(C_669)
      | v1_xboole_0(B_664)
      | v1_xboole_0(A_667) ) ),
    inference(resolution,[status(thm)],[c_46,c_2427])).

tff(c_4725,plain,(
    ! [E_878,D_876,F_875,B_874,C_879,A_877] :
      ( k2_partfun1(k4_subset_1(A_877,C_879,D_876),B_874,k1_tmap_1(A_877,B_874,C_879,D_876,E_878,F_875),D_876) = F_875
      | ~ v1_funct_1(k1_tmap_1(A_877,B_874,C_879,D_876,E_878,F_875))
      | k2_partfun1(D_876,B_874,F_875,k9_subset_1(A_877,C_879,D_876)) != k2_partfun1(C_879,B_874,E_878,k9_subset_1(A_877,C_879,D_876))
      | ~ m1_subset_1(F_875,k1_zfmisc_1(k2_zfmisc_1(D_876,B_874)))
      | ~ v1_funct_2(F_875,D_876,B_874)
      | ~ v1_funct_1(F_875)
      | ~ m1_subset_1(E_878,k1_zfmisc_1(k2_zfmisc_1(C_879,B_874)))
      | ~ v1_funct_2(E_878,C_879,B_874)
      | ~ v1_funct_1(E_878)
      | ~ m1_subset_1(D_876,k1_zfmisc_1(A_877))
      | v1_xboole_0(D_876)
      | ~ m1_subset_1(C_879,k1_zfmisc_1(A_877))
      | v1_xboole_0(C_879)
      | v1_xboole_0(B_874)
      | v1_xboole_0(A_877) ) ),
    inference(resolution,[status(thm)],[c_48,c_3637])).

tff(c_4731,plain,(
    ! [A_877,C_879,E_878] :
      ( k2_partfun1(k4_subset_1(A_877,C_879,'#skF_4'),'#skF_2',k1_tmap_1(A_877,'#skF_2',C_879,'#skF_4',E_878,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_877,'#skF_2',C_879,'#skF_4',E_878,'#skF_6'))
      | k2_partfun1(C_879,'#skF_2',E_878,k9_subset_1(A_877,C_879,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_877,C_879,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_878,k1_zfmisc_1(k2_zfmisc_1(C_879,'#skF_2')))
      | ~ v1_funct_2(E_878,C_879,'#skF_2')
      | ~ v1_funct_1(E_878)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_877))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_879,k1_zfmisc_1(A_877))
      | v1_xboole_0(C_879)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_877) ) ),
    inference(resolution,[status(thm)],[c_54,c_4725])).

tff(c_4739,plain,(
    ! [A_877,C_879,E_878] :
      ( k2_partfun1(k4_subset_1(A_877,C_879,'#skF_4'),'#skF_2',k1_tmap_1(A_877,'#skF_2',C_879,'#skF_4',E_878,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_877,'#skF_2',C_879,'#skF_4',E_878,'#skF_6'))
      | k2_partfun1(C_879,'#skF_2',E_878,k9_subset_1(A_877,C_879,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_877,C_879,'#skF_4'))
      | ~ m1_subset_1(E_878,k1_zfmisc_1(k2_zfmisc_1(C_879,'#skF_2')))
      | ~ v1_funct_2(E_878,C_879,'#skF_2')
      | ~ v1_funct_1(E_878)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_877))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_879,k1_zfmisc_1(A_877))
      | v1_xboole_0(C_879)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_877) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1781,c_4731])).

tff(c_4907,plain,(
    ! [A_908,C_909,E_910] :
      ( k2_partfun1(k4_subset_1(A_908,C_909,'#skF_4'),'#skF_2',k1_tmap_1(A_908,'#skF_2',C_909,'#skF_4',E_910,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_908,'#skF_2',C_909,'#skF_4',E_910,'#skF_6'))
      | k2_partfun1(C_909,'#skF_2',E_910,k9_subset_1(A_908,C_909,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_908,C_909,'#skF_4'))
      | ~ m1_subset_1(E_910,k1_zfmisc_1(k2_zfmisc_1(C_909,'#skF_2')))
      | ~ v1_funct_2(E_910,C_909,'#skF_2')
      | ~ v1_funct_1(E_910)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_908))
      | ~ m1_subset_1(C_909,k1_zfmisc_1(A_908))
      | v1_xboole_0(C_909)
      | v1_xboole_0(A_908) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_4739])).

tff(c_4912,plain,(
    ! [A_908] :
      ( k2_partfun1(k4_subset_1(A_908,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_908,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_908,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_908,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_908,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_908))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_908))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_908) ) ),
    inference(resolution,[status(thm)],[c_60,c_4907])).

tff(c_4920,plain,(
    ! [A_908] :
      ( k2_partfun1(k4_subset_1(A_908,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_908,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_908,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_908,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_908,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_908))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_908))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_908) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1778,c_4912])).

tff(c_4995,plain,(
    ! [A_927] :
      ( k2_partfun1(k4_subset_1(A_927,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_927,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_927,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_927,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_927,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_927))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_927))
      | v1_xboole_0(A_927) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4920])).

tff(c_168,plain,(
    ! [A_245,B_246] :
      ( k7_relat_1(A_245,B_246) = k1_xboole_0
      | ~ r1_xboole_0(B_246,k1_relat_1(A_245))
      | ~ v1_relat_1(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_197,plain,(
    ! [A_249] :
      ( k7_relat_1(A_249,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_249) ) ),
    inference(resolution,[status(thm)],[c_91,c_168])).

tff(c_204,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_197])).

tff(c_776,plain,(
    ! [A_306,B_307,C_308,D_309] :
      ( k2_partfun1(A_306,B_307,C_308,D_309) = k7_relat_1(C_308,D_309)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | ~ v1_funct_1(C_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_780,plain,(
    ! [D_309] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_309) = k7_relat_1('#skF_6',D_309)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_776])).

tff(c_786,plain,(
    ! [D_309] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_309) = k7_relat_1('#skF_6',D_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_780])).

tff(c_205,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_197])).

tff(c_778,plain,(
    ! [D_309] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_309) = k7_relat_1('#skF_5',D_309)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_776])).

tff(c_783,plain,(
    ! [D_309] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_309) = k7_relat_1('#skF_5',D_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_778])).

tff(c_146,plain,(
    ! [A_240,B_241] :
      ( r1_xboole_0(A_240,B_241)
      | ~ r1_subset_1(A_240,B_241)
      | v1_xboole_0(B_241)
      | v1_xboole_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_610,plain,(
    ! [B_294,A_295] :
      ( r1_xboole_0(B_294,A_295)
      | ~ r1_subset_1(A_295,B_294)
      | v1_xboole_0(B_294)
      | v1_xboole_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_117,plain,(
    ! [C_237,A_238,B_239] :
      ( v4_relat_1(C_237,A_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_124,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_117])).

tff(c_215,plain,(
    ! [B_250,A_251] :
      ( k1_relat_1(B_250) = A_251
      | ~ v1_partfun1(B_250,A_251)
      | ~ v4_relat_1(B_250,A_251)
      | ~ v1_relat_1(B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_221,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_124,c_215])).

tff(c_227,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_221])).

tff(c_229,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_475,plain,(
    ! [C_281,A_282,B_283] :
      ( v1_partfun1(C_281,A_282)
      | ~ v1_funct_2(C_281,A_282,B_283)
      | ~ v1_funct_1(C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | v1_xboole_0(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_478,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_475])).

tff(c_484,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_478])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_229,c_484])).

tff(c_487,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_8,plain,(
    ! [A_7,B_9] :
      ( k7_relat_1(A_7,B_9) = k1_xboole_0
      | ~ r1_xboole_0(B_9,k1_relat_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_492,plain,(
    ! [B_9] :
      ( k7_relat_1('#skF_5',B_9) = k1_xboole_0
      | ~ r1_xboole_0(B_9,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_8])).

tff(c_502,plain,(
    ! [B_9] :
      ( k7_relat_1('#skF_5',B_9) = k1_xboole_0
      | ~ r1_xboole_0(B_9,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_492])).

tff(c_614,plain,(
    ! [B_294] :
      ( k7_relat_1('#skF_5',B_294) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_294)
      | v1_xboole_0(B_294)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_610,c_502])).

tff(c_630,plain,(
    ! [B_296] :
      ( k7_relat_1('#skF_5',B_296) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_296)
      | v1_xboole_0(B_296) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_614])).

tff(c_633,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_630])).

tff(c_636,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_633])).

tff(c_495,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_15)) = k3_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_18])).

tff(c_504,plain,(
    ! [A_15] : k1_relat_1(k7_relat_1('#skF_5',A_15)) = k3_xboole_0('#skF_3',A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_495])).

tff(c_640,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_504])).

tff(c_643,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_640])).

tff(c_560,plain,(
    ! [A_287,B_288,C_289] :
      ( k9_subset_1(A_287,B_288,C_289) = k3_xboole_0(B_288,C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(A_287)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_572,plain,(
    ! [B_288] : k9_subset_1('#skF_1',B_288,'#skF_4') = k3_xboole_0(B_288,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_560])).

tff(c_52,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_106,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_582,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_572,c_106])).

tff(c_718,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) != k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_643,c_582])).

tff(c_787,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) != k7_relat_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_718])).

tff(c_788,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_787])).

tff(c_798,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_788])).

tff(c_801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_798])).

tff(c_802,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_890,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_5006,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4995,c_890])).

tff(c_5020,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_880,c_1720,c_881,c_1720,c_1056,c_1056,c_2279,c_5006])).

tff(c_5022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5020])).

tff(c_5023,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_9317,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9308,c_5023])).

tff(c_9328,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_880,c_5985,c_881,c_5985,c_5203,c_5203,c_6423,c_9317])).

tff(c_9330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:05:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.20/3.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.20/3.47  
% 9.20/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.20/3.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.20/3.47  
% 9.20/3.47  %Foreground sorts:
% 9.20/3.47  
% 9.20/3.47  
% 9.20/3.47  %Background operators:
% 9.20/3.47  
% 9.20/3.47  
% 9.20/3.47  %Foreground operators:
% 9.20/3.47  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 9.20/3.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.20/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.20/3.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.20/3.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.20/3.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.20/3.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.20/3.47  tff('#skF_5', type, '#skF_5': $i).
% 9.20/3.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.20/3.47  tff('#skF_6', type, '#skF_6': $i).
% 9.20/3.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.20/3.47  tff('#skF_2', type, '#skF_2': $i).
% 9.20/3.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.20/3.47  tff('#skF_3', type, '#skF_3': $i).
% 9.20/3.47  tff('#skF_1', type, '#skF_1': $i).
% 9.20/3.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.20/3.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.20/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.20/3.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.20/3.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.20/3.47  tff('#skF_4', type, '#skF_4': $i).
% 9.20/3.47  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.20/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.20/3.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.20/3.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.20/3.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.20/3.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.20/3.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.20/3.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.20/3.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.20/3.47  
% 9.52/3.50  tff(f_233, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 9.52/3.50  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.52/3.50  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.52/3.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.52/3.50  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 9.52/3.50  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 9.52/3.50  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 9.52/3.50  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.52/3.50  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.52/3.50  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 9.52/3.50  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 9.52/3.50  tff(f_95, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 9.52/3.50  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 9.52/3.50  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.52/3.50  tff(f_191, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 9.52/3.50  tff(f_109, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.52/3.50  tff(f_157, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 9.52/3.50  tff(c_78, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_97, plain, (![C_229, A_230, B_231]: (v1_relat_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.52/3.50  tff(c_105, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_97])).
% 9.52/3.50  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.52/3.50  tff(c_88, plain, (![B_226, A_227]: (r1_xboole_0(B_226, A_227) | ~r1_xboole_0(A_227, B_226))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.52/3.50  tff(c_91, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_4, c_88])).
% 9.52/3.50  tff(c_851, plain, (![A_321, B_322]: (k7_relat_1(A_321, B_322)=k1_xboole_0 | ~r1_xboole_0(B_322, k1_relat_1(A_321)) | ~v1_relat_1(A_321))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.52/3.50  tff(c_873, plain, (![A_324]: (k7_relat_1(A_324, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_324))), inference(resolution, [status(thm)], [c_91, c_851])).
% 9.52/3.50  tff(c_880, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_873])).
% 9.52/3.50  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.52/3.50  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_66, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | ~r1_subset_1(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.52/3.50  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_104, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_97])).
% 9.52/3.50  tff(c_804, plain, (![C_311, A_312, B_313]: (v4_relat_1(C_311, A_312) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.52/3.50  tff(c_811, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_804])).
% 9.52/3.50  tff(c_813, plain, (![B_314, A_315]: (k7_relat_1(B_314, A_315)=B_314 | ~v4_relat_1(B_314, A_315) | ~v1_relat_1(B_314))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.52/3.50  tff(c_819, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_811, c_813])).
% 9.52/3.50  tff(c_825, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_819])).
% 9.52/3.50  tff(c_5069, plain, (![C_934, A_935, B_936]: (k7_relat_1(k7_relat_1(C_934, A_935), B_936)=k1_xboole_0 | ~r1_xboole_0(A_935, B_936) | ~v1_relat_1(C_934))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.52/3.50  tff(c_5090, plain, (![B_936]: (k7_relat_1('#skF_5', B_936)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_936) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_825, c_5069])).
% 9.52/3.50  tff(c_5116, plain, (![B_938]: (k7_relat_1('#skF_5', B_938)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_938))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5090])).
% 9.52/3.50  tff(c_5124, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_5116])).
% 9.52/3.50  tff(c_5159, plain, (![B_941]: (k7_relat_1('#skF_5', B_941)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_941) | v1_xboole_0(B_941))), inference(negUnitSimplification, [status(thm)], [c_74, c_5124])).
% 9.52/3.50  tff(c_5162, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_5159])).
% 9.52/3.50  tff(c_5165, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_5162])).
% 9.52/3.50  tff(c_76, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_5265, plain, (![B_953, A_954]: (k1_relat_1(B_953)=A_954 | ~v1_partfun1(B_953, A_954) | ~v4_relat_1(B_953, A_954) | ~v1_relat_1(B_953))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.52/3.50  tff(c_5271, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_811, c_5265])).
% 9.52/3.50  tff(c_5277, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5271])).
% 9.52/3.50  tff(c_5599, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_5277])).
% 9.52/3.50  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_5885, plain, (![C_1010, A_1011, B_1012]: (v1_partfun1(C_1010, A_1011) | ~v1_funct_2(C_1010, A_1011, B_1012) | ~v1_funct_1(C_1010) | ~m1_subset_1(C_1010, k1_zfmisc_1(k2_zfmisc_1(A_1011, B_1012))) | v1_xboole_0(B_1012))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.52/3.50  tff(c_5888, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_5885])).
% 9.52/3.50  tff(c_5894, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_5888])).
% 9.52/3.50  tff(c_5896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5599, c_5894])).
% 9.52/3.50  tff(c_5897, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_5277])).
% 9.52/3.50  tff(c_18, plain, (![B_16, A_15]: (k3_xboole_0(k1_relat_1(B_16), A_15)=k1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.52/3.50  tff(c_5902, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_5', A_15))=k3_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5897, c_18])).
% 9.52/3.50  tff(c_5957, plain, (![A_1015]: (k1_relat_1(k7_relat_1('#skF_5', A_1015))=k3_xboole_0('#skF_3', A_1015))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5902])).
% 9.52/3.50  tff(c_5975, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5165, c_5957])).
% 9.52/3.50  tff(c_5985, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5975])).
% 9.52/3.50  tff(c_881, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_873])).
% 9.52/3.50  tff(c_5191, plain, (![A_943, B_944, C_945]: (k9_subset_1(A_943, B_944, C_945)=k3_xboole_0(B_944, C_945) | ~m1_subset_1(C_945, k1_zfmisc_1(A_943)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.52/3.50  tff(c_5203, plain, (![B_944]: (k9_subset_1('#skF_1', B_944, '#skF_4')=k3_xboole_0(B_944, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_5191])).
% 9.52/3.50  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.50  tff(c_6367, plain, (![E_1050, B_1046, C_1051, D_1048, A_1049, F_1047]: (v1_funct_1(k1_tmap_1(A_1049, B_1046, C_1051, D_1048, E_1050, F_1047)) | ~m1_subset_1(F_1047, k1_zfmisc_1(k2_zfmisc_1(D_1048, B_1046))) | ~v1_funct_2(F_1047, D_1048, B_1046) | ~v1_funct_1(F_1047) | ~m1_subset_1(E_1050, k1_zfmisc_1(k2_zfmisc_1(C_1051, B_1046))) | ~v1_funct_2(E_1050, C_1051, B_1046) | ~v1_funct_1(E_1050) | ~m1_subset_1(D_1048, k1_zfmisc_1(A_1049)) | v1_xboole_0(D_1048) | ~m1_subset_1(C_1051, k1_zfmisc_1(A_1049)) | v1_xboole_0(C_1051) | v1_xboole_0(B_1046) | v1_xboole_0(A_1049))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.52/3.50  tff(c_6371, plain, (![A_1049, C_1051, E_1050]: (v1_funct_1(k1_tmap_1(A_1049, '#skF_2', C_1051, '#skF_4', E_1050, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1050, k1_zfmisc_1(k2_zfmisc_1(C_1051, '#skF_2'))) | ~v1_funct_2(E_1050, C_1051, '#skF_2') | ~v1_funct_1(E_1050) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1049)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1051, k1_zfmisc_1(A_1049)) | v1_xboole_0(C_1051) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1049))), inference(resolution, [status(thm)], [c_54, c_6367])).
% 9.52/3.50  tff(c_6378, plain, (![A_1049, C_1051, E_1050]: (v1_funct_1(k1_tmap_1(A_1049, '#skF_2', C_1051, '#skF_4', E_1050, '#skF_6')) | ~m1_subset_1(E_1050, k1_zfmisc_1(k2_zfmisc_1(C_1051, '#skF_2'))) | ~v1_funct_2(E_1050, C_1051, '#skF_2') | ~v1_funct_1(E_1050) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1049)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1051, k1_zfmisc_1(A_1049)) | v1_xboole_0(C_1051) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1049))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_6371])).
% 9.52/3.50  tff(c_6395, plain, (![A_1054, C_1055, E_1056]: (v1_funct_1(k1_tmap_1(A_1054, '#skF_2', C_1055, '#skF_4', E_1056, '#skF_6')) | ~m1_subset_1(E_1056, k1_zfmisc_1(k2_zfmisc_1(C_1055, '#skF_2'))) | ~v1_funct_2(E_1056, C_1055, '#skF_2') | ~v1_funct_1(E_1056) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1054)) | ~m1_subset_1(C_1055, k1_zfmisc_1(A_1054)) | v1_xboole_0(C_1055) | v1_xboole_0(A_1054))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_6378])).
% 9.52/3.50  tff(c_6397, plain, (![A_1054]: (v1_funct_1(k1_tmap_1(A_1054, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1054)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1054)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1054))), inference(resolution, [status(thm)], [c_60, c_6395])).
% 9.52/3.50  tff(c_6402, plain, (![A_1054]: (v1_funct_1(k1_tmap_1(A_1054, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1054)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1054)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1054))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6397])).
% 9.52/3.50  tff(c_6416, plain, (![A_1058]: (v1_funct_1(k1_tmap_1(A_1058, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1058)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1058)) | v1_xboole_0(A_1058))), inference(negUnitSimplification, [status(thm)], [c_74, c_6402])).
% 9.52/3.50  tff(c_6419, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_6416])).
% 9.52/3.50  tff(c_6422, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6419])).
% 9.52/3.50  tff(c_6423, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6422])).
% 9.52/3.50  tff(c_6032, plain, (![A_1017, B_1018, C_1019, D_1020]: (k2_partfun1(A_1017, B_1018, C_1019, D_1020)=k7_relat_1(C_1019, D_1020) | ~m1_subset_1(C_1019, k1_zfmisc_1(k2_zfmisc_1(A_1017, B_1018))) | ~v1_funct_1(C_1019))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.52/3.50  tff(c_6034, plain, (![D_1020]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1020)=k7_relat_1('#skF_5', D_1020) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_6032])).
% 9.52/3.50  tff(c_6039, plain, (![D_1020]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1020)=k7_relat_1('#skF_5', D_1020))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6034])).
% 9.52/3.50  tff(c_6036, plain, (![D_1020]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1020)=k7_relat_1('#skF_6', D_1020) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_6032])).
% 9.52/3.50  tff(c_6042, plain, (![D_1020]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1020)=k7_relat_1('#skF_6', D_1020))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6036])).
% 9.52/3.50  tff(c_48, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (v1_funct_2(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k4_subset_1(A_162, C_164, D_165), B_163) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.52/3.50  tff(c_46, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (m1_subset_1(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162, C_164, D_165), B_163))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.52/3.50  tff(c_6671, plain, (![A_1099, C_1103, D_1102, F_1098, E_1100, B_1101]: (k2_partfun1(k4_subset_1(A_1099, C_1103, D_1102), B_1101, k1_tmap_1(A_1099, B_1101, C_1103, D_1102, E_1100, F_1098), C_1103)=E_1100 | ~m1_subset_1(k1_tmap_1(A_1099, B_1101, C_1103, D_1102, E_1100, F_1098), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1099, C_1103, D_1102), B_1101))) | ~v1_funct_2(k1_tmap_1(A_1099, B_1101, C_1103, D_1102, E_1100, F_1098), k4_subset_1(A_1099, C_1103, D_1102), B_1101) | ~v1_funct_1(k1_tmap_1(A_1099, B_1101, C_1103, D_1102, E_1100, F_1098)) | k2_partfun1(D_1102, B_1101, F_1098, k9_subset_1(A_1099, C_1103, D_1102))!=k2_partfun1(C_1103, B_1101, E_1100, k9_subset_1(A_1099, C_1103, D_1102)) | ~m1_subset_1(F_1098, k1_zfmisc_1(k2_zfmisc_1(D_1102, B_1101))) | ~v1_funct_2(F_1098, D_1102, B_1101) | ~v1_funct_1(F_1098) | ~m1_subset_1(E_1100, k1_zfmisc_1(k2_zfmisc_1(C_1103, B_1101))) | ~v1_funct_2(E_1100, C_1103, B_1101) | ~v1_funct_1(E_1100) | ~m1_subset_1(D_1102, k1_zfmisc_1(A_1099)) | v1_xboole_0(D_1102) | ~m1_subset_1(C_1103, k1_zfmisc_1(A_1099)) | v1_xboole_0(C_1103) | v1_xboole_0(B_1101) | v1_xboole_0(A_1099))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.52/3.50  tff(c_8096, plain, (![B_1306, C_1311, D_1308, A_1309, F_1307, E_1310]: (k2_partfun1(k4_subset_1(A_1309, C_1311, D_1308), B_1306, k1_tmap_1(A_1309, B_1306, C_1311, D_1308, E_1310, F_1307), C_1311)=E_1310 | ~v1_funct_2(k1_tmap_1(A_1309, B_1306, C_1311, D_1308, E_1310, F_1307), k4_subset_1(A_1309, C_1311, D_1308), B_1306) | ~v1_funct_1(k1_tmap_1(A_1309, B_1306, C_1311, D_1308, E_1310, F_1307)) | k2_partfun1(D_1308, B_1306, F_1307, k9_subset_1(A_1309, C_1311, D_1308))!=k2_partfun1(C_1311, B_1306, E_1310, k9_subset_1(A_1309, C_1311, D_1308)) | ~m1_subset_1(F_1307, k1_zfmisc_1(k2_zfmisc_1(D_1308, B_1306))) | ~v1_funct_2(F_1307, D_1308, B_1306) | ~v1_funct_1(F_1307) | ~m1_subset_1(E_1310, k1_zfmisc_1(k2_zfmisc_1(C_1311, B_1306))) | ~v1_funct_2(E_1310, C_1311, B_1306) | ~v1_funct_1(E_1310) | ~m1_subset_1(D_1308, k1_zfmisc_1(A_1309)) | v1_xboole_0(D_1308) | ~m1_subset_1(C_1311, k1_zfmisc_1(A_1309)) | v1_xboole_0(C_1311) | v1_xboole_0(B_1306) | v1_xboole_0(A_1309))), inference(resolution, [status(thm)], [c_46, c_6671])).
% 9.52/3.50  tff(c_8963, plain, (![C_1488, A_1486, E_1487, D_1485, F_1484, B_1483]: (k2_partfun1(k4_subset_1(A_1486, C_1488, D_1485), B_1483, k1_tmap_1(A_1486, B_1483, C_1488, D_1485, E_1487, F_1484), C_1488)=E_1487 | ~v1_funct_1(k1_tmap_1(A_1486, B_1483, C_1488, D_1485, E_1487, F_1484)) | k2_partfun1(D_1485, B_1483, F_1484, k9_subset_1(A_1486, C_1488, D_1485))!=k2_partfun1(C_1488, B_1483, E_1487, k9_subset_1(A_1486, C_1488, D_1485)) | ~m1_subset_1(F_1484, k1_zfmisc_1(k2_zfmisc_1(D_1485, B_1483))) | ~v1_funct_2(F_1484, D_1485, B_1483) | ~v1_funct_1(F_1484) | ~m1_subset_1(E_1487, k1_zfmisc_1(k2_zfmisc_1(C_1488, B_1483))) | ~v1_funct_2(E_1487, C_1488, B_1483) | ~v1_funct_1(E_1487) | ~m1_subset_1(D_1485, k1_zfmisc_1(A_1486)) | v1_xboole_0(D_1485) | ~m1_subset_1(C_1488, k1_zfmisc_1(A_1486)) | v1_xboole_0(C_1488) | v1_xboole_0(B_1483) | v1_xboole_0(A_1486))), inference(resolution, [status(thm)], [c_48, c_8096])).
% 9.52/3.50  tff(c_8969, plain, (![A_1486, C_1488, E_1487]: (k2_partfun1(k4_subset_1(A_1486, C_1488, '#skF_4'), '#skF_2', k1_tmap_1(A_1486, '#skF_2', C_1488, '#skF_4', E_1487, '#skF_6'), C_1488)=E_1487 | ~v1_funct_1(k1_tmap_1(A_1486, '#skF_2', C_1488, '#skF_4', E_1487, '#skF_6')) | k2_partfun1(C_1488, '#skF_2', E_1487, k9_subset_1(A_1486, C_1488, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1486, C_1488, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1487, k1_zfmisc_1(k2_zfmisc_1(C_1488, '#skF_2'))) | ~v1_funct_2(E_1487, C_1488, '#skF_2') | ~v1_funct_1(E_1487) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1486)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1488, k1_zfmisc_1(A_1486)) | v1_xboole_0(C_1488) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1486))), inference(resolution, [status(thm)], [c_54, c_8963])).
% 9.52/3.50  tff(c_8977, plain, (![A_1486, C_1488, E_1487]: (k2_partfun1(k4_subset_1(A_1486, C_1488, '#skF_4'), '#skF_2', k1_tmap_1(A_1486, '#skF_2', C_1488, '#skF_4', E_1487, '#skF_6'), C_1488)=E_1487 | ~v1_funct_1(k1_tmap_1(A_1486, '#skF_2', C_1488, '#skF_4', E_1487, '#skF_6')) | k2_partfun1(C_1488, '#skF_2', E_1487, k9_subset_1(A_1486, C_1488, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1486, C_1488, '#skF_4')) | ~m1_subset_1(E_1487, k1_zfmisc_1(k2_zfmisc_1(C_1488, '#skF_2'))) | ~v1_funct_2(E_1487, C_1488, '#skF_2') | ~v1_funct_1(E_1487) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1486)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1488, k1_zfmisc_1(A_1486)) | v1_xboole_0(C_1488) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1486))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_6042, c_8969])).
% 9.52/3.50  tff(c_9289, plain, (![A_1539, C_1540, E_1541]: (k2_partfun1(k4_subset_1(A_1539, C_1540, '#skF_4'), '#skF_2', k1_tmap_1(A_1539, '#skF_2', C_1540, '#skF_4', E_1541, '#skF_6'), C_1540)=E_1541 | ~v1_funct_1(k1_tmap_1(A_1539, '#skF_2', C_1540, '#skF_4', E_1541, '#skF_6')) | k2_partfun1(C_1540, '#skF_2', E_1541, k9_subset_1(A_1539, C_1540, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1539, C_1540, '#skF_4')) | ~m1_subset_1(E_1541, k1_zfmisc_1(k2_zfmisc_1(C_1540, '#skF_2'))) | ~v1_funct_2(E_1541, C_1540, '#skF_2') | ~v1_funct_1(E_1541) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1539)) | ~m1_subset_1(C_1540, k1_zfmisc_1(A_1539)) | v1_xboole_0(C_1540) | v1_xboole_0(A_1539))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_8977])).
% 9.52/3.50  tff(c_9294, plain, (![A_1539]: (k2_partfun1(k4_subset_1(A_1539, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1539, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1539, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1539, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1539, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1539)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1539)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1539))), inference(resolution, [status(thm)], [c_60, c_9289])).
% 9.52/3.50  tff(c_9302, plain, (![A_1539]: (k2_partfun1(k4_subset_1(A_1539, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1539, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1539, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1539, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1539, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1539)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1539)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1539))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_6039, c_9294])).
% 9.52/3.50  tff(c_9308, plain, (![A_1542]: (k2_partfun1(k4_subset_1(A_1542, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1542, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1542, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1542, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1542, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1542)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1542)) | v1_xboole_0(A_1542))), inference(negUnitSimplification, [status(thm)], [c_74, c_9302])).
% 9.52/3.50  tff(c_918, plain, (![C_329, A_330, B_331]: (k7_relat_1(k7_relat_1(C_329, A_330), B_331)=k1_xboole_0 | ~r1_xboole_0(A_330, B_331) | ~v1_relat_1(C_329))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.52/3.50  tff(c_939, plain, (![B_331]: (k7_relat_1('#skF_5', B_331)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_331) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_825, c_918])).
% 9.52/3.50  tff(c_965, plain, (![B_333]: (k7_relat_1('#skF_5', B_333)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_333))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_939])).
% 9.52/3.50  tff(c_969, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_965])).
% 9.52/3.50  tff(c_979, plain, (![B_334]: (k7_relat_1('#skF_5', B_334)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_334) | v1_xboole_0(B_334))), inference(negUnitSimplification, [status(thm)], [c_74, c_969])).
% 9.52/3.50  tff(c_982, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_979])).
% 9.52/3.50  tff(c_985, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_982])).
% 9.52/3.50  tff(c_1127, plain, (![B_350, A_351]: (k1_relat_1(B_350)=A_351 | ~v1_partfun1(B_350, A_351) | ~v4_relat_1(B_350, A_351) | ~v1_relat_1(B_350))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.52/3.50  tff(c_1133, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_811, c_1127])).
% 9.52/3.50  tff(c_1139, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1133])).
% 9.52/3.50  tff(c_1452, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1139])).
% 9.52/3.50  tff(c_1658, plain, (![C_399, A_400, B_401]: (v1_partfun1(C_399, A_400) | ~v1_funct_2(C_399, A_400, B_401) | ~v1_funct_1(C_399) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))) | v1_xboole_0(B_401))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.52/3.50  tff(c_1661, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1658])).
% 9.52/3.50  tff(c_1667, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1661])).
% 9.52/3.50  tff(c_1669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1452, c_1667])).
% 9.52/3.50  tff(c_1670, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1139])).
% 9.52/3.50  tff(c_1675, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_5', A_15))=k3_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1670, c_18])).
% 9.52/3.50  tff(c_1692, plain, (![A_402]: (k1_relat_1(k7_relat_1('#skF_5', A_402))=k3_xboole_0('#skF_3', A_402))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1675])).
% 9.52/3.50  tff(c_1710, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_985, c_1692])).
% 9.52/3.50  tff(c_1720, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1710])).
% 9.52/3.50  tff(c_1044, plain, (![A_340, B_341, C_342]: (k9_subset_1(A_340, B_341, C_342)=k3_xboole_0(B_341, C_342) | ~m1_subset_1(C_342, k1_zfmisc_1(A_340)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.52/3.50  tff(c_1056, plain, (![B_341]: (k9_subset_1('#skF_1', B_341, '#skF_4')=k3_xboole_0(B_341, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1044])).
% 9.52/3.50  tff(c_2119, plain, (![C_439, D_436, B_434, A_437, F_435, E_438]: (v1_funct_1(k1_tmap_1(A_437, B_434, C_439, D_436, E_438, F_435)) | ~m1_subset_1(F_435, k1_zfmisc_1(k2_zfmisc_1(D_436, B_434))) | ~v1_funct_2(F_435, D_436, B_434) | ~v1_funct_1(F_435) | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(C_439, B_434))) | ~v1_funct_2(E_438, C_439, B_434) | ~v1_funct_1(E_438) | ~m1_subset_1(D_436, k1_zfmisc_1(A_437)) | v1_xboole_0(D_436) | ~m1_subset_1(C_439, k1_zfmisc_1(A_437)) | v1_xboole_0(C_439) | v1_xboole_0(B_434) | v1_xboole_0(A_437))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.52/3.50  tff(c_2123, plain, (![A_437, C_439, E_438]: (v1_funct_1(k1_tmap_1(A_437, '#skF_2', C_439, '#skF_4', E_438, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(C_439, '#skF_2'))) | ~v1_funct_2(E_438, C_439, '#skF_2') | ~v1_funct_1(E_438) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_437)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_439, k1_zfmisc_1(A_437)) | v1_xboole_0(C_439) | v1_xboole_0('#skF_2') | v1_xboole_0(A_437))), inference(resolution, [status(thm)], [c_54, c_2119])).
% 9.52/3.50  tff(c_2130, plain, (![A_437, C_439, E_438]: (v1_funct_1(k1_tmap_1(A_437, '#skF_2', C_439, '#skF_4', E_438, '#skF_6')) | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(C_439, '#skF_2'))) | ~v1_funct_2(E_438, C_439, '#skF_2') | ~v1_funct_1(E_438) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_437)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_439, k1_zfmisc_1(A_437)) | v1_xboole_0(C_439) | v1_xboole_0('#skF_2') | v1_xboole_0(A_437))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2123])).
% 9.52/3.50  tff(c_2252, plain, (![A_456, C_457, E_458]: (v1_funct_1(k1_tmap_1(A_456, '#skF_2', C_457, '#skF_4', E_458, '#skF_6')) | ~m1_subset_1(E_458, k1_zfmisc_1(k2_zfmisc_1(C_457, '#skF_2'))) | ~v1_funct_2(E_458, C_457, '#skF_2') | ~v1_funct_1(E_458) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_456)) | ~m1_subset_1(C_457, k1_zfmisc_1(A_456)) | v1_xboole_0(C_457) | v1_xboole_0(A_456))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_2130])).
% 9.52/3.50  tff(c_2254, plain, (![A_456]: (v1_funct_1(k1_tmap_1(A_456, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_456)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_456)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_456))), inference(resolution, [status(thm)], [c_60, c_2252])).
% 9.52/3.50  tff(c_2259, plain, (![A_456]: (v1_funct_1(k1_tmap_1(A_456, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_456)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_456)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_456))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2254])).
% 9.52/3.51  tff(c_2272, plain, (![A_460]: (v1_funct_1(k1_tmap_1(A_460, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_460)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_460)) | v1_xboole_0(A_460))), inference(negUnitSimplification, [status(thm)], [c_74, c_2259])).
% 9.52/3.51  tff(c_2275, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_2272])).
% 9.52/3.51  tff(c_2278, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2275])).
% 9.52/3.51  tff(c_2279, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_2278])).
% 9.52/3.51  tff(c_1771, plain, (![A_404, B_405, C_406, D_407]: (k2_partfun1(A_404, B_405, C_406, D_407)=k7_relat_1(C_406, D_407) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))) | ~v1_funct_1(C_406))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.52/3.51  tff(c_1773, plain, (![D_407]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_407)=k7_relat_1('#skF_5', D_407) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_1771])).
% 9.52/3.51  tff(c_1778, plain, (![D_407]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_407)=k7_relat_1('#skF_5', D_407))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1773])).
% 9.52/3.51  tff(c_1775, plain, (![D_407]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_407)=k7_relat_1('#skF_6', D_407) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_1771])).
% 9.52/3.51  tff(c_1781, plain, (![D_407]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_407)=k7_relat_1('#skF_6', D_407))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1775])).
% 9.52/3.51  tff(c_2427, plain, (![A_485, C_489, D_488, E_486, B_487, F_484]: (k2_partfun1(k4_subset_1(A_485, C_489, D_488), B_487, k1_tmap_1(A_485, B_487, C_489, D_488, E_486, F_484), D_488)=F_484 | ~m1_subset_1(k1_tmap_1(A_485, B_487, C_489, D_488, E_486, F_484), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_485, C_489, D_488), B_487))) | ~v1_funct_2(k1_tmap_1(A_485, B_487, C_489, D_488, E_486, F_484), k4_subset_1(A_485, C_489, D_488), B_487) | ~v1_funct_1(k1_tmap_1(A_485, B_487, C_489, D_488, E_486, F_484)) | k2_partfun1(D_488, B_487, F_484, k9_subset_1(A_485, C_489, D_488))!=k2_partfun1(C_489, B_487, E_486, k9_subset_1(A_485, C_489, D_488)) | ~m1_subset_1(F_484, k1_zfmisc_1(k2_zfmisc_1(D_488, B_487))) | ~v1_funct_2(F_484, D_488, B_487) | ~v1_funct_1(F_484) | ~m1_subset_1(E_486, k1_zfmisc_1(k2_zfmisc_1(C_489, B_487))) | ~v1_funct_2(E_486, C_489, B_487) | ~v1_funct_1(E_486) | ~m1_subset_1(D_488, k1_zfmisc_1(A_485)) | v1_xboole_0(D_488) | ~m1_subset_1(C_489, k1_zfmisc_1(A_485)) | v1_xboole_0(C_489) | v1_xboole_0(B_487) | v1_xboole_0(A_485))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.52/3.51  tff(c_3637, plain, (![B_664, A_667, C_669, D_666, E_668, F_665]: (k2_partfun1(k4_subset_1(A_667, C_669, D_666), B_664, k1_tmap_1(A_667, B_664, C_669, D_666, E_668, F_665), D_666)=F_665 | ~v1_funct_2(k1_tmap_1(A_667, B_664, C_669, D_666, E_668, F_665), k4_subset_1(A_667, C_669, D_666), B_664) | ~v1_funct_1(k1_tmap_1(A_667, B_664, C_669, D_666, E_668, F_665)) | k2_partfun1(D_666, B_664, F_665, k9_subset_1(A_667, C_669, D_666))!=k2_partfun1(C_669, B_664, E_668, k9_subset_1(A_667, C_669, D_666)) | ~m1_subset_1(F_665, k1_zfmisc_1(k2_zfmisc_1(D_666, B_664))) | ~v1_funct_2(F_665, D_666, B_664) | ~v1_funct_1(F_665) | ~m1_subset_1(E_668, k1_zfmisc_1(k2_zfmisc_1(C_669, B_664))) | ~v1_funct_2(E_668, C_669, B_664) | ~v1_funct_1(E_668) | ~m1_subset_1(D_666, k1_zfmisc_1(A_667)) | v1_xboole_0(D_666) | ~m1_subset_1(C_669, k1_zfmisc_1(A_667)) | v1_xboole_0(C_669) | v1_xboole_0(B_664) | v1_xboole_0(A_667))), inference(resolution, [status(thm)], [c_46, c_2427])).
% 9.52/3.51  tff(c_4725, plain, (![E_878, D_876, F_875, B_874, C_879, A_877]: (k2_partfun1(k4_subset_1(A_877, C_879, D_876), B_874, k1_tmap_1(A_877, B_874, C_879, D_876, E_878, F_875), D_876)=F_875 | ~v1_funct_1(k1_tmap_1(A_877, B_874, C_879, D_876, E_878, F_875)) | k2_partfun1(D_876, B_874, F_875, k9_subset_1(A_877, C_879, D_876))!=k2_partfun1(C_879, B_874, E_878, k9_subset_1(A_877, C_879, D_876)) | ~m1_subset_1(F_875, k1_zfmisc_1(k2_zfmisc_1(D_876, B_874))) | ~v1_funct_2(F_875, D_876, B_874) | ~v1_funct_1(F_875) | ~m1_subset_1(E_878, k1_zfmisc_1(k2_zfmisc_1(C_879, B_874))) | ~v1_funct_2(E_878, C_879, B_874) | ~v1_funct_1(E_878) | ~m1_subset_1(D_876, k1_zfmisc_1(A_877)) | v1_xboole_0(D_876) | ~m1_subset_1(C_879, k1_zfmisc_1(A_877)) | v1_xboole_0(C_879) | v1_xboole_0(B_874) | v1_xboole_0(A_877))), inference(resolution, [status(thm)], [c_48, c_3637])).
% 9.52/3.51  tff(c_4731, plain, (![A_877, C_879, E_878]: (k2_partfun1(k4_subset_1(A_877, C_879, '#skF_4'), '#skF_2', k1_tmap_1(A_877, '#skF_2', C_879, '#skF_4', E_878, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_877, '#skF_2', C_879, '#skF_4', E_878, '#skF_6')) | k2_partfun1(C_879, '#skF_2', E_878, k9_subset_1(A_877, C_879, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_877, C_879, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_878, k1_zfmisc_1(k2_zfmisc_1(C_879, '#skF_2'))) | ~v1_funct_2(E_878, C_879, '#skF_2') | ~v1_funct_1(E_878) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_877)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_879, k1_zfmisc_1(A_877)) | v1_xboole_0(C_879) | v1_xboole_0('#skF_2') | v1_xboole_0(A_877))), inference(resolution, [status(thm)], [c_54, c_4725])).
% 9.52/3.51  tff(c_4739, plain, (![A_877, C_879, E_878]: (k2_partfun1(k4_subset_1(A_877, C_879, '#skF_4'), '#skF_2', k1_tmap_1(A_877, '#skF_2', C_879, '#skF_4', E_878, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_877, '#skF_2', C_879, '#skF_4', E_878, '#skF_6')) | k2_partfun1(C_879, '#skF_2', E_878, k9_subset_1(A_877, C_879, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_877, C_879, '#skF_4')) | ~m1_subset_1(E_878, k1_zfmisc_1(k2_zfmisc_1(C_879, '#skF_2'))) | ~v1_funct_2(E_878, C_879, '#skF_2') | ~v1_funct_1(E_878) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_877)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_879, k1_zfmisc_1(A_877)) | v1_xboole_0(C_879) | v1_xboole_0('#skF_2') | v1_xboole_0(A_877))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1781, c_4731])).
% 9.52/3.51  tff(c_4907, plain, (![A_908, C_909, E_910]: (k2_partfun1(k4_subset_1(A_908, C_909, '#skF_4'), '#skF_2', k1_tmap_1(A_908, '#skF_2', C_909, '#skF_4', E_910, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_908, '#skF_2', C_909, '#skF_4', E_910, '#skF_6')) | k2_partfun1(C_909, '#skF_2', E_910, k9_subset_1(A_908, C_909, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_908, C_909, '#skF_4')) | ~m1_subset_1(E_910, k1_zfmisc_1(k2_zfmisc_1(C_909, '#skF_2'))) | ~v1_funct_2(E_910, C_909, '#skF_2') | ~v1_funct_1(E_910) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_908)) | ~m1_subset_1(C_909, k1_zfmisc_1(A_908)) | v1_xboole_0(C_909) | v1_xboole_0(A_908))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_4739])).
% 9.52/3.51  tff(c_4912, plain, (![A_908]: (k2_partfun1(k4_subset_1(A_908, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_908, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_908, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_908, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_908, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_908)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_908)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_908))), inference(resolution, [status(thm)], [c_60, c_4907])).
% 9.52/3.51  tff(c_4920, plain, (![A_908]: (k2_partfun1(k4_subset_1(A_908, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_908, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_908, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_908, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_908, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_908)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_908)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_908))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1778, c_4912])).
% 9.52/3.51  tff(c_4995, plain, (![A_927]: (k2_partfun1(k4_subset_1(A_927, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_927, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_927, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_927, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_927, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_927)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_927)) | v1_xboole_0(A_927))), inference(negUnitSimplification, [status(thm)], [c_74, c_4920])).
% 9.52/3.51  tff(c_168, plain, (![A_245, B_246]: (k7_relat_1(A_245, B_246)=k1_xboole_0 | ~r1_xboole_0(B_246, k1_relat_1(A_245)) | ~v1_relat_1(A_245))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.52/3.51  tff(c_197, plain, (![A_249]: (k7_relat_1(A_249, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_249))), inference(resolution, [status(thm)], [c_91, c_168])).
% 9.52/3.51  tff(c_204, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_197])).
% 9.52/3.51  tff(c_776, plain, (![A_306, B_307, C_308, D_309]: (k2_partfun1(A_306, B_307, C_308, D_309)=k7_relat_1(C_308, D_309) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | ~v1_funct_1(C_308))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.52/3.51  tff(c_780, plain, (![D_309]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_309)=k7_relat_1('#skF_6', D_309) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_776])).
% 9.52/3.51  tff(c_786, plain, (![D_309]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_309)=k7_relat_1('#skF_6', D_309))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_780])).
% 9.52/3.51  tff(c_205, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_197])).
% 9.52/3.51  tff(c_778, plain, (![D_309]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_309)=k7_relat_1('#skF_5', D_309) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_776])).
% 9.52/3.51  tff(c_783, plain, (![D_309]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_309)=k7_relat_1('#skF_5', D_309))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_778])).
% 9.52/3.51  tff(c_146, plain, (![A_240, B_241]: (r1_xboole_0(A_240, B_241) | ~r1_subset_1(A_240, B_241) | v1_xboole_0(B_241) | v1_xboole_0(A_240))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.52/3.51  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.52/3.51  tff(c_610, plain, (![B_294, A_295]: (r1_xboole_0(B_294, A_295) | ~r1_subset_1(A_295, B_294) | v1_xboole_0(B_294) | v1_xboole_0(A_295))), inference(resolution, [status(thm)], [c_146, c_2])).
% 9.52/3.51  tff(c_117, plain, (![C_237, A_238, B_239]: (v4_relat_1(C_237, A_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.52/3.51  tff(c_124, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_117])).
% 9.52/3.51  tff(c_215, plain, (![B_250, A_251]: (k1_relat_1(B_250)=A_251 | ~v1_partfun1(B_250, A_251) | ~v4_relat_1(B_250, A_251) | ~v1_relat_1(B_250))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.52/3.51  tff(c_221, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_124, c_215])).
% 9.52/3.51  tff(c_227, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_221])).
% 9.52/3.51  tff(c_229, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_227])).
% 9.52/3.51  tff(c_475, plain, (![C_281, A_282, B_283]: (v1_partfun1(C_281, A_282) | ~v1_funct_2(C_281, A_282, B_283) | ~v1_funct_1(C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | v1_xboole_0(B_283))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.52/3.51  tff(c_478, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_475])).
% 9.52/3.51  tff(c_484, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_478])).
% 9.52/3.51  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_229, c_484])).
% 9.52/3.51  tff(c_487, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_227])).
% 9.52/3.51  tff(c_8, plain, (![A_7, B_9]: (k7_relat_1(A_7, B_9)=k1_xboole_0 | ~r1_xboole_0(B_9, k1_relat_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.52/3.51  tff(c_492, plain, (![B_9]: (k7_relat_1('#skF_5', B_9)=k1_xboole_0 | ~r1_xboole_0(B_9, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_8])).
% 9.52/3.51  tff(c_502, plain, (![B_9]: (k7_relat_1('#skF_5', B_9)=k1_xboole_0 | ~r1_xboole_0(B_9, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_492])).
% 9.52/3.51  tff(c_614, plain, (![B_294]: (k7_relat_1('#skF_5', B_294)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_294) | v1_xboole_0(B_294) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_610, c_502])).
% 9.52/3.51  tff(c_630, plain, (![B_296]: (k7_relat_1('#skF_5', B_296)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_296) | v1_xboole_0(B_296))), inference(negUnitSimplification, [status(thm)], [c_74, c_614])).
% 9.52/3.51  tff(c_633, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_630])).
% 9.52/3.51  tff(c_636, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_633])).
% 9.52/3.51  tff(c_495, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_5', A_15))=k3_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_18])).
% 9.52/3.51  tff(c_504, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_5', A_15))=k3_xboole_0('#skF_3', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_495])).
% 9.52/3.51  tff(c_640, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_636, c_504])).
% 9.52/3.51  tff(c_643, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_640])).
% 9.52/3.51  tff(c_560, plain, (![A_287, B_288, C_289]: (k9_subset_1(A_287, B_288, C_289)=k3_xboole_0(B_288, C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(A_287)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.52/3.51  tff(c_572, plain, (![B_288]: (k9_subset_1('#skF_1', B_288, '#skF_4')=k3_xboole_0(B_288, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_560])).
% 9.52/3.51  tff(c_52, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 9.52/3.51  tff(c_106, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 9.52/3.51  tff(c_582, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_572, c_572, c_106])).
% 9.52/3.51  tff(c_718, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_643, c_643, c_582])).
% 9.52/3.51  tff(c_787, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)!=k7_relat_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_783, c_718])).
% 9.52/3.51  tff(c_788, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_205, c_787])).
% 9.52/3.51  tff(c_798, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_786, c_788])).
% 9.52/3.51  tff(c_801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_798])).
% 9.52/3.51  tff(c_802, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 9.52/3.51  tff(c_890, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_802])).
% 9.52/3.51  tff(c_5006, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4995, c_890])).
% 9.52/3.51  tff(c_5020, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_880, c_1720, c_881, c_1720, c_1056, c_1056, c_2279, c_5006])).
% 9.52/3.51  tff(c_5022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5020])).
% 9.52/3.51  tff(c_5023, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_802])).
% 9.52/3.51  tff(c_9317, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9308, c_5023])).
% 9.52/3.51  tff(c_9328, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_880, c_5985, c_881, c_5985, c_5203, c_5203, c_6423, c_9317])).
% 9.52/3.51  tff(c_9330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_9328])).
% 9.52/3.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.52/3.51  
% 9.52/3.51  Inference rules
% 9.52/3.51  ----------------------
% 9.52/3.51  #Ref     : 0
% 9.52/3.51  #Sup     : 1988
% 9.52/3.51  #Fact    : 0
% 9.52/3.51  #Define  : 0
% 9.52/3.51  #Split   : 25
% 9.52/3.51  #Chain   : 0
% 9.52/3.51  #Close   : 0
% 9.52/3.51  
% 9.52/3.51  Ordering : KBO
% 9.52/3.51  
% 9.52/3.51  Simplification rules
% 9.52/3.51  ----------------------
% 9.52/3.51  #Subsume      : 847
% 9.52/3.51  #Demod        : 5418
% 9.52/3.51  #Tautology    : 472
% 9.52/3.51  #SimpNegUnit  : 275
% 9.52/3.51  #BackRed      : 14
% 9.52/3.51  
% 9.52/3.51  #Partial instantiations: 0
% 9.52/3.51  #Strategies tried      : 1
% 9.52/3.51  
% 9.52/3.51  Timing (in seconds)
% 9.52/3.51  ----------------------
% 9.52/3.51  Preprocessing        : 0.41
% 9.52/3.51  Parsing              : 0.20
% 9.52/3.51  CNF conversion       : 0.06
% 9.52/3.51  Main loop            : 2.30
% 9.52/3.51  Inferencing          : 0.77
% 9.52/3.51  Reduction            : 0.91
% 9.52/3.51  Demodulation         : 0.70
% 9.52/3.51  BG Simplification    : 0.06
% 9.52/3.51  Subsumption          : 0.44
% 9.52/3.51  Abstraction          : 0.09
% 9.52/3.51  MUC search           : 0.00
% 9.52/3.51  Cooper               : 0.00
% 9.52/3.51  Total                : 2.78
% 9.52/3.51  Index Insertion      : 0.00
% 9.52/3.51  Index Deletion       : 0.00
% 9.52/3.51  Index Matching       : 0.00
% 9.52/3.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
