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
% DateTime   : Thu Dec  3 10:26:14 EST 2020

% Result     : Theorem 34.82s
% Output     : CNFRefutation 35.10s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 884 expanded)
%              Number of leaves         :   41 ( 329 expanded)
%              Depth                    :   20
%              Number of atoms          :  731 (4579 expanded)
%              Number of equality atoms :  159 ( 844 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_214,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_84,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_172,axiom,(
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

tff(f_138,axiom,(
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

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_54,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | ~ r1_subset_1(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_95,plain,(
    ! [C_225,A_226,B_227] :
      ( v1_relat_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_102,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_44882,plain,(
    ! [B_1979,A_1980] :
      ( r1_subset_1(B_1979,A_1980)
      | ~ r1_subset_1(A_1980,B_1979)
      | v1_xboole_0(B_1979)
      | v1_xboole_0(A_1980) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44884,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_44882])).

tff(c_44887,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_44884])).

tff(c_507,plain,(
    ! [C_278,A_279,B_280] :
      ( v4_relat_1(C_278,A_279)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_514,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_507])).

tff(c_12,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_519,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_514,c_12])).

tff(c_522,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_519])).

tff(c_44906,plain,(
    ! [C_1984,A_1985,B_1986] :
      ( k7_relat_1(k7_relat_1(C_1984,A_1985),B_1986) = k1_xboole_0
      | ~ r1_xboole_0(A_1985,B_1986)
      | ~ v1_relat_1(C_1984) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44924,plain,(
    ! [B_1986] :
      ( k7_relat_1('#skF_6',B_1986) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_1986)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_44906])).

tff(c_44967,plain,(
    ! [B_1991] :
      ( k7_relat_1('#skF_6',B_1991) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_1991) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_44924])).

tff(c_44971,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_44967])).

tff(c_44984,plain,(
    ! [B_1993] :
      ( k7_relat_1('#skF_6',B_1993) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_1993)
      | v1_xboole_0(B_1993) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_44971])).

tff(c_44987,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44887,c_44984])).

tff(c_44990,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_44987])).

tff(c_10,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44994,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44990,c_10])).

tff(c_45000,plain,(
    ! [B_1994] :
      ( k7_relat_1(k1_xboole_0,B_1994) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_1994) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_44994])).

tff(c_45004,plain,(
    ! [B_18] :
      ( k7_relat_1(k1_xboole_0,B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_45000])).

tff(c_45155,plain,(
    ! [B_2004] :
      ( k7_relat_1(k1_xboole_0,B_2004) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_2004)
      | v1_xboole_0(B_2004) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_45004])).

tff(c_45158,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_45155])).

tff(c_45161,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_45158])).

tff(c_45008,plain,(
    ! [C_1995,A_1996,B_1997] :
      ( k7_relat_1(k7_relat_1(C_1995,A_1996),B_1997) = k7_relat_1(C_1995,k3_xboole_0(A_1996,B_1997))
      | ~ v1_relat_1(C_1995) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45029,plain,(
    ! [B_1997] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_1997)) = k7_relat_1(k1_xboole_0,B_1997)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44990,c_45008])).

tff(c_45045,plain,(
    ! [B_1997] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_1997)) = k7_relat_1(k1_xboole_0,B_1997) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_45029])).

tff(c_44893,plain,(
    ! [A_1981,B_1982,C_1983] :
      ( k9_subset_1(A_1981,B_1982,C_1983) = k3_xboole_0(B_1982,C_1983)
      | ~ m1_subset_1(C_1983,k1_zfmisc_1(A_1981)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44904,plain,(
    ! [B_1982] : k9_subset_1('#skF_1',B_1982,'#skF_4') = k3_xboole_0(B_1982,'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_44893])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_45426,plain,(
    ! [A_2028,B_2029,C_2030,D_2031] :
      ( k2_partfun1(A_2028,B_2029,C_2030,D_2031) = k7_relat_1(C_2030,D_2031)
      | ~ m1_subset_1(C_2030,k1_zfmisc_1(k2_zfmisc_1(A_2028,B_2029)))
      | ~ v1_funct_1(C_2030) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_45428,plain,(
    ! [D_2031] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_2031) = k7_relat_1('#skF_6',D_2031)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_45426])).

tff(c_45433,plain,(
    ! [D_2031] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_2031) = k7_relat_1('#skF_6',D_2031) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_45428])).

tff(c_147,plain,(
    ! [B_238,A_239] :
      ( r1_subset_1(B_238,A_239)
      | ~ r1_subset_1(A_239,B_238)
      | v1_xboole_0(B_238)
      | v1_xboole_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_149,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_147])).

tff(c_152,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_149])).

tff(c_108,plain,(
    ! [C_230,A_231,B_232] :
      ( v4_relat_1(C_230,A_231)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_115,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_108])).

tff(c_128,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_115,c_12])).

tff(c_131,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_128])).

tff(c_212,plain,(
    ! [C_249,A_250,B_251] :
      ( k7_relat_1(k7_relat_1(C_249,A_250),B_251) = k1_xboole_0
      | ~ r1_xboole_0(A_250,B_251)
      | ~ v1_relat_1(C_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_227,plain,(
    ! [B_251] :
      ( k7_relat_1('#skF_6',B_251) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_251)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_212])).

tff(c_237,plain,(
    ! [B_252] :
      ( k7_relat_1('#skF_6',B_252) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_227])).

tff(c_241,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_237])).

tff(c_253,plain,(
    ! [B_254] :
      ( k7_relat_1('#skF_6',B_254) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_254)
      | v1_xboole_0(B_254) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_241])).

tff(c_256,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_152,c_253])).

tff(c_259,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_256])).

tff(c_303,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_10])).

tff(c_311,plain,(
    ! [B_258] :
      ( k7_relat_1(k1_xboole_0,B_258) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_303])).

tff(c_315,plain,(
    ! [B_18] :
      ( k7_relat_1(k1_xboole_0,B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_311])).

tff(c_470,plain,(
    ! [B_272] :
      ( k7_relat_1(k1_xboole_0,B_272) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_272)
      | v1_xboole_0(B_272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_315])).

tff(c_473,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_470])).

tff(c_476,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_473])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_103,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_95])).

tff(c_116,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_108])).

tff(c_134,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_12])).

tff(c_137,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_134])).

tff(c_230,plain,(
    ! [B_251] :
      ( k7_relat_1('#skF_5',B_251) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_251)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_212])).

tff(c_245,plain,(
    ! [B_253] :
      ( k7_relat_1('#skF_5',B_253) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_230])).

tff(c_249,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_245])).

tff(c_338,plain,(
    ! [B_260] :
      ( k7_relat_1('#skF_5',B_260) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_260)
      | v1_xboole_0(B_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_249])).

tff(c_341,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_338])).

tff(c_344,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_341])).

tff(c_260,plain,(
    ! [C_255,A_256,B_257] :
      ( k7_relat_1(k7_relat_1(C_255,A_256),B_257) = k7_relat_1(C_255,k3_xboole_0(A_256,B_257))
      | ~ v1_relat_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_290,plain,(
    ! [B_257] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_257)) = k7_relat_1('#skF_5',B_257)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_260])).

tff(c_296,plain,(
    ! [B_257] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_257)) = k7_relat_1('#skF_5',B_257) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_290])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_424,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( k2_partfun1(A_265,B_266,C_267,D_268) = k7_relat_1(C_267,D_268)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_428,plain,(
    ! [D_268] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_268) = k7_relat_1('#skF_5',D_268)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_424])).

tff(c_434,plain,(
    ! [D_268] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_268) = k7_relat_1('#skF_5',D_268) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_428])).

tff(c_8,plain,(
    ! [C_11,A_9,B_10] :
      ( k7_relat_1(k7_relat_1(C_11,A_9),B_10) = k7_relat_1(C_11,k3_xboole_0(A_9,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_300,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_8])).

tff(c_307,plain,(
    ! [B_10] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_300])).

tff(c_426,plain,(
    ! [D_268] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_268) = k7_relat_1('#skF_6',D_268)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_424])).

tff(c_431,plain,(
    ! [D_268] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_268) = k7_relat_1('#skF_6',D_268) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_426])).

tff(c_163,plain,(
    ! [A_242,B_243,C_244] :
      ( k9_subset_1(A_242,B_243,C_244) = k3_xboole_0(B_243,C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_174,plain,(
    ! [B_243] : k9_subset_1('#skF_1',B_243,'#skF_4') = k3_xboole_0(B_243,'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_163])).

tff(c_40,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_105,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_344,c_296,c_434,c_307,c_431,c_174,c_174,c_105])).

tff(c_491,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44931,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44904,c_44904,c_491])).

tff(c_45437,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45433,c_44931])).

tff(c_45438,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45161,c_45045,c_45437])).

tff(c_45430,plain,(
    ! [D_2031] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_2031) = k7_relat_1('#skF_5',D_2031)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_45426])).

tff(c_45436,plain,(
    ! [D_2031] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_2031) = k7_relat_1('#skF_5',D_2031) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_45430])).

tff(c_45460,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_45438,c_45436])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_45526,plain,(
    ! [C_2048,B_2047,F_2044,E_2046,D_2049,A_2045] :
      ( v1_funct_1(k1_tmap_1(A_2045,B_2047,C_2048,D_2049,E_2046,F_2044))
      | ~ m1_subset_1(F_2044,k1_zfmisc_1(k2_zfmisc_1(D_2049,B_2047)))
      | ~ v1_funct_2(F_2044,D_2049,B_2047)
      | ~ v1_funct_1(F_2044)
      | ~ m1_subset_1(E_2046,k1_zfmisc_1(k2_zfmisc_1(C_2048,B_2047)))
      | ~ v1_funct_2(E_2046,C_2048,B_2047)
      | ~ v1_funct_1(E_2046)
      | ~ m1_subset_1(D_2049,k1_zfmisc_1(A_2045))
      | v1_xboole_0(D_2049)
      | ~ m1_subset_1(C_2048,k1_zfmisc_1(A_2045))
      | v1_xboole_0(C_2048)
      | v1_xboole_0(B_2047)
      | v1_xboole_0(A_2045) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_45528,plain,(
    ! [A_2045,C_2048,E_2046] :
      ( v1_funct_1(k1_tmap_1(A_2045,'#skF_2',C_2048,'#skF_4',E_2046,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2046,k1_zfmisc_1(k2_zfmisc_1(C_2048,'#skF_2')))
      | ~ v1_funct_2(E_2046,C_2048,'#skF_2')
      | ~ v1_funct_1(E_2046)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2045))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2048,k1_zfmisc_1(A_2045))
      | v1_xboole_0(C_2048)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2045) ) ),
    inference(resolution,[status(thm)],[c_42,c_45526])).

tff(c_45533,plain,(
    ! [A_2045,C_2048,E_2046] :
      ( v1_funct_1(k1_tmap_1(A_2045,'#skF_2',C_2048,'#skF_4',E_2046,'#skF_6'))
      | ~ m1_subset_1(E_2046,k1_zfmisc_1(k2_zfmisc_1(C_2048,'#skF_2')))
      | ~ v1_funct_2(E_2046,C_2048,'#skF_2')
      | ~ v1_funct_1(E_2046)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2045))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2048,k1_zfmisc_1(A_2045))
      | v1_xboole_0(C_2048)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2045) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_45528])).

tff(c_45544,plain,(
    ! [A_2054,C_2055,E_2056] :
      ( v1_funct_1(k1_tmap_1(A_2054,'#skF_2',C_2055,'#skF_4',E_2056,'#skF_6'))
      | ~ m1_subset_1(E_2056,k1_zfmisc_1(k2_zfmisc_1(C_2055,'#skF_2')))
      | ~ v1_funct_2(E_2056,C_2055,'#skF_2')
      | ~ v1_funct_1(E_2056)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2054))
      | ~ m1_subset_1(C_2055,k1_zfmisc_1(A_2054))
      | v1_xboole_0(C_2055)
      | v1_xboole_0(A_2054) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_45533])).

tff(c_45548,plain,(
    ! [A_2054] :
      ( v1_funct_1(k1_tmap_1(A_2054,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2054))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2054))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2054) ) ),
    inference(resolution,[status(thm)],[c_48,c_45544])).

tff(c_45555,plain,(
    ! [A_2054] :
      ( v1_funct_1(k1_tmap_1(A_2054,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2054))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2054))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2054) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_45548])).

tff(c_45810,plain,(
    ! [A_2080] :
      ( v1_funct_1(k1_tmap_1(A_2080,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2080))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2080))
      | v1_xboole_0(A_2080) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_45555])).

tff(c_45813,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_45810])).

tff(c_45816,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_45813])).

tff(c_45817,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_45816])).

tff(c_36,plain,(
    ! [F_163,C_160,E_162,B_159,D_161,A_158] :
      ( v1_funct_2(k1_tmap_1(A_158,B_159,C_160,D_161,E_162,F_163),k4_subset_1(A_158,C_160,D_161),B_159)
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(D_161,B_159)))
      | ~ v1_funct_2(F_163,D_161,B_159)
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(C_160,B_159)))
      | ~ v1_funct_2(E_162,C_160,B_159)
      | ~ v1_funct_1(E_162)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(A_158))
      | v1_xboole_0(D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(A_158))
      | v1_xboole_0(C_160)
      | v1_xboole_0(B_159)
      | v1_xboole_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_34,plain,(
    ! [F_163,C_160,E_162,B_159,D_161,A_158] :
      ( m1_subset_1(k1_tmap_1(A_158,B_159,C_160,D_161,E_162,F_163),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_158,C_160,D_161),B_159)))
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(D_161,B_159)))
      | ~ v1_funct_2(F_163,D_161,B_159)
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(C_160,B_159)))
      | ~ v1_funct_2(E_162,C_160,B_159)
      | ~ v1_funct_1(E_162)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(A_158))
      | v1_xboole_0(D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(A_158))
      | v1_xboole_0(C_160)
      | v1_xboole_0(B_159)
      | v1_xboole_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_46244,plain,(
    ! [B_2105,D_2102,C_2104,F_2106,A_2103,E_2101] :
      ( k2_partfun1(k4_subset_1(A_2103,C_2104,D_2102),B_2105,k1_tmap_1(A_2103,B_2105,C_2104,D_2102,E_2101,F_2106),C_2104) = E_2101
      | ~ m1_subset_1(k1_tmap_1(A_2103,B_2105,C_2104,D_2102,E_2101,F_2106),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2103,C_2104,D_2102),B_2105)))
      | ~ v1_funct_2(k1_tmap_1(A_2103,B_2105,C_2104,D_2102,E_2101,F_2106),k4_subset_1(A_2103,C_2104,D_2102),B_2105)
      | ~ v1_funct_1(k1_tmap_1(A_2103,B_2105,C_2104,D_2102,E_2101,F_2106))
      | k2_partfun1(D_2102,B_2105,F_2106,k9_subset_1(A_2103,C_2104,D_2102)) != k2_partfun1(C_2104,B_2105,E_2101,k9_subset_1(A_2103,C_2104,D_2102))
      | ~ m1_subset_1(F_2106,k1_zfmisc_1(k2_zfmisc_1(D_2102,B_2105)))
      | ~ v1_funct_2(F_2106,D_2102,B_2105)
      | ~ v1_funct_1(F_2106)
      | ~ m1_subset_1(E_2101,k1_zfmisc_1(k2_zfmisc_1(C_2104,B_2105)))
      | ~ v1_funct_2(E_2101,C_2104,B_2105)
      | ~ v1_funct_1(E_2101)
      | ~ m1_subset_1(D_2102,k1_zfmisc_1(A_2103))
      | v1_xboole_0(D_2102)
      | ~ m1_subset_1(C_2104,k1_zfmisc_1(A_2103))
      | v1_xboole_0(C_2104)
      | v1_xboole_0(B_2105)
      | v1_xboole_0(A_2103) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_48814,plain,(
    ! [D_2284,F_2279,E_2281,C_2283,B_2282,A_2280] :
      ( k2_partfun1(k4_subset_1(A_2280,C_2283,D_2284),B_2282,k1_tmap_1(A_2280,B_2282,C_2283,D_2284,E_2281,F_2279),C_2283) = E_2281
      | ~ v1_funct_2(k1_tmap_1(A_2280,B_2282,C_2283,D_2284,E_2281,F_2279),k4_subset_1(A_2280,C_2283,D_2284),B_2282)
      | ~ v1_funct_1(k1_tmap_1(A_2280,B_2282,C_2283,D_2284,E_2281,F_2279))
      | k2_partfun1(D_2284,B_2282,F_2279,k9_subset_1(A_2280,C_2283,D_2284)) != k2_partfun1(C_2283,B_2282,E_2281,k9_subset_1(A_2280,C_2283,D_2284))
      | ~ m1_subset_1(F_2279,k1_zfmisc_1(k2_zfmisc_1(D_2284,B_2282)))
      | ~ v1_funct_2(F_2279,D_2284,B_2282)
      | ~ v1_funct_1(F_2279)
      | ~ m1_subset_1(E_2281,k1_zfmisc_1(k2_zfmisc_1(C_2283,B_2282)))
      | ~ v1_funct_2(E_2281,C_2283,B_2282)
      | ~ v1_funct_1(E_2281)
      | ~ m1_subset_1(D_2284,k1_zfmisc_1(A_2280))
      | v1_xboole_0(D_2284)
      | ~ m1_subset_1(C_2283,k1_zfmisc_1(A_2280))
      | v1_xboole_0(C_2283)
      | v1_xboole_0(B_2282)
      | v1_xboole_0(A_2280) ) ),
    inference(resolution,[status(thm)],[c_34,c_46244])).

tff(c_85745,plain,(
    ! [C_3634,A_3631,B_3633,D_3635,F_3630,E_3632] :
      ( k2_partfun1(k4_subset_1(A_3631,C_3634,D_3635),B_3633,k1_tmap_1(A_3631,B_3633,C_3634,D_3635,E_3632,F_3630),C_3634) = E_3632
      | ~ v1_funct_1(k1_tmap_1(A_3631,B_3633,C_3634,D_3635,E_3632,F_3630))
      | k2_partfun1(D_3635,B_3633,F_3630,k9_subset_1(A_3631,C_3634,D_3635)) != k2_partfun1(C_3634,B_3633,E_3632,k9_subset_1(A_3631,C_3634,D_3635))
      | ~ m1_subset_1(F_3630,k1_zfmisc_1(k2_zfmisc_1(D_3635,B_3633)))
      | ~ v1_funct_2(F_3630,D_3635,B_3633)
      | ~ v1_funct_1(F_3630)
      | ~ m1_subset_1(E_3632,k1_zfmisc_1(k2_zfmisc_1(C_3634,B_3633)))
      | ~ v1_funct_2(E_3632,C_3634,B_3633)
      | ~ v1_funct_1(E_3632)
      | ~ m1_subset_1(D_3635,k1_zfmisc_1(A_3631))
      | v1_xboole_0(D_3635)
      | ~ m1_subset_1(C_3634,k1_zfmisc_1(A_3631))
      | v1_xboole_0(C_3634)
      | v1_xboole_0(B_3633)
      | v1_xboole_0(A_3631) ) ),
    inference(resolution,[status(thm)],[c_36,c_48814])).

tff(c_85749,plain,(
    ! [A_3631,C_3634,E_3632] :
      ( k2_partfun1(k4_subset_1(A_3631,C_3634,'#skF_4'),'#skF_2',k1_tmap_1(A_3631,'#skF_2',C_3634,'#skF_4',E_3632,'#skF_6'),C_3634) = E_3632
      | ~ v1_funct_1(k1_tmap_1(A_3631,'#skF_2',C_3634,'#skF_4',E_3632,'#skF_6'))
      | k2_partfun1(C_3634,'#skF_2',E_3632,k9_subset_1(A_3631,C_3634,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_3631,C_3634,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3632,k1_zfmisc_1(k2_zfmisc_1(C_3634,'#skF_2')))
      | ~ v1_funct_2(E_3632,C_3634,'#skF_2')
      | ~ v1_funct_1(E_3632)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3631))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3634,k1_zfmisc_1(A_3631))
      | v1_xboole_0(C_3634)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3631) ) ),
    inference(resolution,[status(thm)],[c_42,c_85745])).

tff(c_85755,plain,(
    ! [A_3631,C_3634,E_3632] :
      ( k2_partfun1(k4_subset_1(A_3631,C_3634,'#skF_4'),'#skF_2',k1_tmap_1(A_3631,'#skF_2',C_3634,'#skF_4',E_3632,'#skF_6'),C_3634) = E_3632
      | ~ v1_funct_1(k1_tmap_1(A_3631,'#skF_2',C_3634,'#skF_4',E_3632,'#skF_6'))
      | k2_partfun1(C_3634,'#skF_2',E_3632,k9_subset_1(A_3631,C_3634,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3631,C_3634,'#skF_4'))
      | ~ m1_subset_1(E_3632,k1_zfmisc_1(k2_zfmisc_1(C_3634,'#skF_2')))
      | ~ v1_funct_2(E_3632,C_3634,'#skF_2')
      | ~ v1_funct_1(E_3632)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3631))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3634,k1_zfmisc_1(A_3631))
      | v1_xboole_0(C_3634)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_45433,c_85749])).

tff(c_102232,plain,(
    ! [A_4114,C_4115,E_4116] :
      ( k2_partfun1(k4_subset_1(A_4114,C_4115,'#skF_4'),'#skF_2',k1_tmap_1(A_4114,'#skF_2',C_4115,'#skF_4',E_4116,'#skF_6'),C_4115) = E_4116
      | ~ v1_funct_1(k1_tmap_1(A_4114,'#skF_2',C_4115,'#skF_4',E_4116,'#skF_6'))
      | k2_partfun1(C_4115,'#skF_2',E_4116,k9_subset_1(A_4114,C_4115,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4114,C_4115,'#skF_4'))
      | ~ m1_subset_1(E_4116,k1_zfmisc_1(k2_zfmisc_1(C_4115,'#skF_2')))
      | ~ v1_funct_2(E_4116,C_4115,'#skF_2')
      | ~ v1_funct_1(E_4116)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4114))
      | ~ m1_subset_1(C_4115,k1_zfmisc_1(A_4114))
      | v1_xboole_0(C_4115)
      | v1_xboole_0(A_4114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_85755])).

tff(c_102239,plain,(
    ! [A_4114] :
      ( k2_partfun1(k4_subset_1(A_4114,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4114,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4114,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_4114,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4114,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4114))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4114))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4114) ) ),
    inference(resolution,[status(thm)],[c_48,c_102232])).

tff(c_102249,plain,(
    ! [A_4114] :
      ( k2_partfun1(k4_subset_1(A_4114,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4114,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4114,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4114,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4114,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4114))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4114))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_45436,c_102239])).

tff(c_102997,plain,(
    ! [A_4127] :
      ( k2_partfun1(k4_subset_1(A_4127,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4127,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4127,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4127,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4127,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4127))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4127))
      | v1_xboole_0(A_4127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_102249])).

tff(c_543,plain,(
    ! [B_285,A_286] :
      ( r1_subset_1(B_285,A_286)
      | ~ r1_subset_1(A_286,B_285)
      | v1_xboole_0(B_285)
      | v1_xboole_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_545,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_543])).

tff(c_548,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_545])).

tff(c_567,plain,(
    ! [C_290,A_291,B_292] :
      ( k7_relat_1(k7_relat_1(C_290,A_291),B_292) = k1_xboole_0
      | ~ r1_xboole_0(A_291,B_292)
      | ~ v1_relat_1(C_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_585,plain,(
    ! [B_292] :
      ( k7_relat_1('#skF_6',B_292) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_292)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_567])).

tff(c_628,plain,(
    ! [B_297] :
      ( k7_relat_1('#skF_6',B_297) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_585])).

tff(c_632,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_6',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_628])).

tff(c_768,plain,(
    ! [B_307] :
      ( k7_relat_1('#skF_6',B_307) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_307)
      | v1_xboole_0(B_307) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_632])).

tff(c_771,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_548,c_768])).

tff(c_774,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_771])).

tff(c_781,plain,(
    ! [B_13] :
      ( k7_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_13)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_10])).

tff(c_789,plain,(
    ! [B_308] :
      ( k7_relat_1(k1_xboole_0,B_308) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_781])).

tff(c_793,plain,(
    ! [B_18] :
      ( k7_relat_1(k1_xboole_0,B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_789])).

tff(c_833,plain,(
    ! [B_311] :
      ( k7_relat_1(k1_xboole_0,B_311) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_311)
      | v1_xboole_0(B_311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_793])).

tff(c_836,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_833])).

tff(c_839,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_836])).

tff(c_778,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_8])).

tff(c_785,plain,(
    ! [B_10] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_778])).

tff(c_515,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_507])).

tff(c_525,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_515,c_12])).

tff(c_528,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_525])).

tff(c_582,plain,(
    ! [B_292] :
      ( k7_relat_1('#skF_5',B_292) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_292)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_567])).

tff(c_611,plain,(
    ! [B_295] :
      ( k7_relat_1('#skF_5',B_295) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_582])).

tff(c_615,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_611])).

tff(c_645,plain,(
    ! [B_299] :
      ( k7_relat_1('#skF_5',B_299) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_299)
      | v1_xboole_0(B_299) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_615])).

tff(c_648,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_645])).

tff(c_651,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_648])).

tff(c_669,plain,(
    ! [C_301,A_302,B_303] :
      ( k7_relat_1(k7_relat_1(C_301,A_302),B_303) = k7_relat_1(C_301,k3_xboole_0(A_302,B_303))
      | ~ v1_relat_1(C_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_699,plain,(
    ! [B_303] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_303)) = k7_relat_1('#skF_5',B_303)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_669])).

tff(c_708,plain,(
    ! [B_303] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_303)) = k7_relat_1('#skF_5',B_303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_699])).

tff(c_554,plain,(
    ! [A_287,B_288,C_289] :
      ( k9_subset_1(A_287,B_288,C_289) = k3_xboole_0(B_288,C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(A_287)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_565,plain,(
    ! [B_288] : k9_subset_1('#skF_1',B_288,'#skF_4') = k3_xboole_0(B_288,'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_554])).

tff(c_1103,plain,(
    ! [E_339,F_337,C_341,B_340,A_338,D_342] :
      ( v1_funct_1(k1_tmap_1(A_338,B_340,C_341,D_342,E_339,F_337))
      | ~ m1_subset_1(F_337,k1_zfmisc_1(k2_zfmisc_1(D_342,B_340)))
      | ~ v1_funct_2(F_337,D_342,B_340)
      | ~ v1_funct_1(F_337)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(C_341,B_340)))
      | ~ v1_funct_2(E_339,C_341,B_340)
      | ~ v1_funct_1(E_339)
      | ~ m1_subset_1(D_342,k1_zfmisc_1(A_338))
      | v1_xboole_0(D_342)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(A_338))
      | v1_xboole_0(C_341)
      | v1_xboole_0(B_340)
      | v1_xboole_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1105,plain,(
    ! [A_338,C_341,E_339] :
      ( v1_funct_1(k1_tmap_1(A_338,'#skF_2',C_341,'#skF_4',E_339,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(C_341,'#skF_2')))
      | ~ v1_funct_2(E_339,C_341,'#skF_2')
      | ~ v1_funct_1(E_339)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_338))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_341,k1_zfmisc_1(A_338))
      | v1_xboole_0(C_341)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_338) ) ),
    inference(resolution,[status(thm)],[c_42,c_1103])).

tff(c_1110,plain,(
    ! [A_338,C_341,E_339] :
      ( v1_funct_1(k1_tmap_1(A_338,'#skF_2',C_341,'#skF_4',E_339,'#skF_6'))
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(C_341,'#skF_2')))
      | ~ v1_funct_2(E_339,C_341,'#skF_2')
      | ~ v1_funct_1(E_339)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_338))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_341,k1_zfmisc_1(A_338))
      | v1_xboole_0(C_341)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1105])).

tff(c_1128,plain,(
    ! [A_349,C_350,E_351] :
      ( v1_funct_1(k1_tmap_1(A_349,'#skF_2',C_350,'#skF_4',E_351,'#skF_6'))
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(C_350,'#skF_2')))
      | ~ v1_funct_2(E_351,C_350,'#skF_2')
      | ~ v1_funct_1(E_351)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_349))
      | ~ m1_subset_1(C_350,k1_zfmisc_1(A_349))
      | v1_xboole_0(C_350)
      | v1_xboole_0(A_349) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_1110])).

tff(c_1132,plain,(
    ! [A_349] :
      ( v1_funct_1(k1_tmap_1(A_349,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_349))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_349))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_349) ) ),
    inference(resolution,[status(thm)],[c_48,c_1128])).

tff(c_1139,plain,(
    ! [A_349] :
      ( v1_funct_1(k1_tmap_1(A_349,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_349))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_349))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1132])).

tff(c_1225,plain,(
    ! [A_375] :
      ( v1_funct_1(k1_tmap_1(A_375,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_375))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_375))
      | v1_xboole_0(A_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1139])).

tff(c_1228,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1225])).

tff(c_1231,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1228])).

tff(c_1232,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1231])).

tff(c_870,plain,(
    ! [A_318,B_319,C_320,D_321] :
      ( k2_partfun1(A_318,B_319,C_320,D_321) = k7_relat_1(C_320,D_321)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319)))
      | ~ v1_funct_1(C_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_874,plain,(
    ! [D_321] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_321) = k7_relat_1('#skF_5',D_321)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_870])).

tff(c_880,plain,(
    ! [D_321] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_321) = k7_relat_1('#skF_5',D_321) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_874])).

tff(c_872,plain,(
    ! [D_321] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_321) = k7_relat_1('#skF_6',D_321)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_870])).

tff(c_877,plain,(
    ! [D_321] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_321) = k7_relat_1('#skF_6',D_321) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_872])).

tff(c_1828,plain,(
    ! [B_410,A_408,D_407,C_409,F_411,E_406] :
      ( k2_partfun1(k4_subset_1(A_408,C_409,D_407),B_410,k1_tmap_1(A_408,B_410,C_409,D_407,E_406,F_411),D_407) = F_411
      | ~ m1_subset_1(k1_tmap_1(A_408,B_410,C_409,D_407,E_406,F_411),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_408,C_409,D_407),B_410)))
      | ~ v1_funct_2(k1_tmap_1(A_408,B_410,C_409,D_407,E_406,F_411),k4_subset_1(A_408,C_409,D_407),B_410)
      | ~ v1_funct_1(k1_tmap_1(A_408,B_410,C_409,D_407,E_406,F_411))
      | k2_partfun1(D_407,B_410,F_411,k9_subset_1(A_408,C_409,D_407)) != k2_partfun1(C_409,B_410,E_406,k9_subset_1(A_408,C_409,D_407))
      | ~ m1_subset_1(F_411,k1_zfmisc_1(k2_zfmisc_1(D_407,B_410)))
      | ~ v1_funct_2(F_411,D_407,B_410)
      | ~ v1_funct_1(F_411)
      | ~ m1_subset_1(E_406,k1_zfmisc_1(k2_zfmisc_1(C_409,B_410)))
      | ~ v1_funct_2(E_406,C_409,B_410)
      | ~ v1_funct_1(E_406)
      | ~ m1_subset_1(D_407,k1_zfmisc_1(A_408))
      | v1_xboole_0(D_407)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(A_408))
      | v1_xboole_0(C_409)
      | v1_xboole_0(B_410)
      | v1_xboole_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4153,plain,(
    ! [E_588,F_586,D_591,C_590,A_587,B_589] :
      ( k2_partfun1(k4_subset_1(A_587,C_590,D_591),B_589,k1_tmap_1(A_587,B_589,C_590,D_591,E_588,F_586),D_591) = F_586
      | ~ v1_funct_2(k1_tmap_1(A_587,B_589,C_590,D_591,E_588,F_586),k4_subset_1(A_587,C_590,D_591),B_589)
      | ~ v1_funct_1(k1_tmap_1(A_587,B_589,C_590,D_591,E_588,F_586))
      | k2_partfun1(D_591,B_589,F_586,k9_subset_1(A_587,C_590,D_591)) != k2_partfun1(C_590,B_589,E_588,k9_subset_1(A_587,C_590,D_591))
      | ~ m1_subset_1(F_586,k1_zfmisc_1(k2_zfmisc_1(D_591,B_589)))
      | ~ v1_funct_2(F_586,D_591,B_589)
      | ~ v1_funct_1(F_586)
      | ~ m1_subset_1(E_588,k1_zfmisc_1(k2_zfmisc_1(C_590,B_589)))
      | ~ v1_funct_2(E_588,C_590,B_589)
      | ~ v1_funct_1(E_588)
      | ~ m1_subset_1(D_591,k1_zfmisc_1(A_587))
      | v1_xboole_0(D_591)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(A_587))
      | v1_xboole_0(C_590)
      | v1_xboole_0(B_589)
      | v1_xboole_0(A_587) ) ),
    inference(resolution,[status(thm)],[c_34,c_1828])).

tff(c_26792,plain,(
    ! [C_1466,F_1462,D_1467,E_1464,B_1465,A_1463] :
      ( k2_partfun1(k4_subset_1(A_1463,C_1466,D_1467),B_1465,k1_tmap_1(A_1463,B_1465,C_1466,D_1467,E_1464,F_1462),D_1467) = F_1462
      | ~ v1_funct_1(k1_tmap_1(A_1463,B_1465,C_1466,D_1467,E_1464,F_1462))
      | k2_partfun1(D_1467,B_1465,F_1462,k9_subset_1(A_1463,C_1466,D_1467)) != k2_partfun1(C_1466,B_1465,E_1464,k9_subset_1(A_1463,C_1466,D_1467))
      | ~ m1_subset_1(F_1462,k1_zfmisc_1(k2_zfmisc_1(D_1467,B_1465)))
      | ~ v1_funct_2(F_1462,D_1467,B_1465)
      | ~ v1_funct_1(F_1462)
      | ~ m1_subset_1(E_1464,k1_zfmisc_1(k2_zfmisc_1(C_1466,B_1465)))
      | ~ v1_funct_2(E_1464,C_1466,B_1465)
      | ~ v1_funct_1(E_1464)
      | ~ m1_subset_1(D_1467,k1_zfmisc_1(A_1463))
      | v1_xboole_0(D_1467)
      | ~ m1_subset_1(C_1466,k1_zfmisc_1(A_1463))
      | v1_xboole_0(C_1466)
      | v1_xboole_0(B_1465)
      | v1_xboole_0(A_1463) ) ),
    inference(resolution,[status(thm)],[c_36,c_4153])).

tff(c_26796,plain,(
    ! [A_1463,C_1466,E_1464] :
      ( k2_partfun1(k4_subset_1(A_1463,C_1466,'#skF_4'),'#skF_2',k1_tmap_1(A_1463,'#skF_2',C_1466,'#skF_4',E_1464,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1463,'#skF_2',C_1466,'#skF_4',E_1464,'#skF_6'))
      | k2_partfun1(C_1466,'#skF_2',E_1464,k9_subset_1(A_1463,C_1466,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1463,C_1466,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1464,k1_zfmisc_1(k2_zfmisc_1(C_1466,'#skF_2')))
      | ~ v1_funct_2(E_1464,C_1466,'#skF_2')
      | ~ v1_funct_1(E_1464)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1463))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1466,k1_zfmisc_1(A_1463))
      | v1_xboole_0(C_1466)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1463) ) ),
    inference(resolution,[status(thm)],[c_42,c_26792])).

tff(c_26802,plain,(
    ! [A_1463,C_1466,E_1464] :
      ( k2_partfun1(k4_subset_1(A_1463,C_1466,'#skF_4'),'#skF_2',k1_tmap_1(A_1463,'#skF_2',C_1466,'#skF_4',E_1464,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1463,'#skF_2',C_1466,'#skF_4',E_1464,'#skF_6'))
      | k2_partfun1(C_1466,'#skF_2',E_1464,k9_subset_1(A_1463,C_1466,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1463,C_1466,'#skF_4'))
      | ~ m1_subset_1(E_1464,k1_zfmisc_1(k2_zfmisc_1(C_1466,'#skF_2')))
      | ~ v1_funct_2(E_1464,C_1466,'#skF_2')
      | ~ v1_funct_1(E_1464)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1463))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1466,k1_zfmisc_1(A_1463))
      | v1_xboole_0(C_1466)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1463) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_877,c_26796])).

tff(c_44690,plain,(
    ! [A_1960,C_1961,E_1962] :
      ( k2_partfun1(k4_subset_1(A_1960,C_1961,'#skF_4'),'#skF_2',k1_tmap_1(A_1960,'#skF_2',C_1961,'#skF_4',E_1962,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1960,'#skF_2',C_1961,'#skF_4',E_1962,'#skF_6'))
      | k2_partfun1(C_1961,'#skF_2',E_1962,k9_subset_1(A_1960,C_1961,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1960,C_1961,'#skF_4'))
      | ~ m1_subset_1(E_1962,k1_zfmisc_1(k2_zfmisc_1(C_1961,'#skF_2')))
      | ~ v1_funct_2(E_1962,C_1961,'#skF_2')
      | ~ v1_funct_1(E_1962)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1960))
      | ~ m1_subset_1(C_1961,k1_zfmisc_1(A_1960))
      | v1_xboole_0(C_1961)
      | v1_xboole_0(A_1960) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_26802])).

tff(c_44697,plain,(
    ! [A_1960] :
      ( k2_partfun1(k4_subset_1(A_1960,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1960,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1960,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1960,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1960,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1960))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1960))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1960) ) ),
    inference(resolution,[status(thm)],[c_48,c_44690])).

tff(c_44707,plain,(
    ! [A_1960] :
      ( k2_partfun1(k4_subset_1(A_1960,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1960,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1960,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1960,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1960,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1960))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1960))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1960) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_880,c_44697])).

tff(c_44843,plain,(
    ! [A_1976] :
      ( k2_partfun1(k4_subset_1(A_1976,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1976,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1976,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1976,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1976,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1976))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1976))
      | v1_xboole_0(A_1976) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_44707])).

tff(c_490,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_533,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_44854,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44843,c_533])).

tff(c_44868,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_839,c_785,c_651,c_708,c_565,c_565,c_1232,c_44854])).

tff(c_44870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_44868])).

tff(c_44871,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_103009,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_102997,c_44871])).

tff(c_103023,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_45161,c_45045,c_44904,c_45460,c_44904,c_45817,c_103009])).

tff(c_103025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_103023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:13:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.82/24.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.82/24.84  
% 34.82/24.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.82/24.84  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 34.82/24.84  
% 34.82/24.84  %Foreground sorts:
% 34.82/24.84  
% 34.82/24.84  
% 34.82/24.84  %Background operators:
% 34.82/24.84  
% 34.82/24.84  
% 34.82/24.84  %Foreground operators:
% 34.82/24.84  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 34.82/24.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 34.82/24.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.82/24.84  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 34.82/24.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 34.82/24.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 34.82/24.84  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 34.82/24.84  tff('#skF_5', type, '#skF_5': $i).
% 34.82/24.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 34.82/24.84  tff('#skF_6', type, '#skF_6': $i).
% 34.82/24.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 34.82/24.84  tff('#skF_2', type, '#skF_2': $i).
% 34.82/24.84  tff('#skF_3', type, '#skF_3': $i).
% 34.82/24.84  tff('#skF_1', type, '#skF_1': $i).
% 34.82/24.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 34.82/24.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.82/24.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.82/24.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.82/24.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 34.82/24.84  tff('#skF_4', type, '#skF_4': $i).
% 34.82/24.84  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 34.82/24.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.82/24.84  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 34.82/24.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 34.82/24.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 34.82/24.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 34.82/24.84  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 34.82/24.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.82/24.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 34.82/24.84  
% 35.10/24.88  tff(f_214, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 35.10/24.88  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 35.10/24.88  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 35.10/24.88  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) => r1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 35.10/24.88  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 35.10/24.88  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 35.10/24.88  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 35.10/24.88  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 35.10/24.88  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 35.10/24.88  tff(f_90, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 35.10/24.88  tff(f_172, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 35.10/24.88  tff(f_138, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 35.10/24.88  tff(c_66, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_54, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_62, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_16, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | ~r1_subset_1(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 35.10/24.88  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_95, plain, (![C_225, A_226, B_227]: (v1_relat_1(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 35.10/24.88  tff(c_102, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_95])).
% 35.10/24.88  tff(c_44882, plain, (![B_1979, A_1980]: (r1_subset_1(B_1979, A_1980) | ~r1_subset_1(A_1980, B_1979) | v1_xboole_0(B_1979) | v1_xboole_0(A_1980))), inference(cnfTransformation, [status(thm)], [f_74])).
% 35.10/24.88  tff(c_44884, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_44882])).
% 35.10/24.88  tff(c_44887, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_44884])).
% 35.10/24.88  tff(c_507, plain, (![C_278, A_279, B_280]: (v4_relat_1(C_278, A_279) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 35.10/24.88  tff(c_514, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_507])).
% 35.10/24.88  tff(c_12, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 35.10/24.88  tff(c_519, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_514, c_12])).
% 35.10/24.88  tff(c_522, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_519])).
% 35.10/24.88  tff(c_44906, plain, (![C_1984, A_1985, B_1986]: (k7_relat_1(k7_relat_1(C_1984, A_1985), B_1986)=k1_xboole_0 | ~r1_xboole_0(A_1985, B_1986) | ~v1_relat_1(C_1984))), inference(cnfTransformation, [status(thm)], [f_48])).
% 35.10/24.88  tff(c_44924, plain, (![B_1986]: (k7_relat_1('#skF_6', B_1986)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_1986) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_522, c_44906])).
% 35.10/24.88  tff(c_44967, plain, (![B_1991]: (k7_relat_1('#skF_6', B_1991)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_1991))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_44924])).
% 35.10/24.88  tff(c_44971, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_44967])).
% 35.10/24.88  tff(c_44984, plain, (![B_1993]: (k7_relat_1('#skF_6', B_1993)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_1993) | v1_xboole_0(B_1993))), inference(negUnitSimplification, [status(thm)], [c_58, c_44971])).
% 35.10/24.88  tff(c_44987, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44887, c_44984])).
% 35.10/24.88  tff(c_44990, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_44987])).
% 35.10/24.88  tff(c_10, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 35.10/24.88  tff(c_44994, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44990, c_10])).
% 35.10/24.88  tff(c_45000, plain, (![B_1994]: (k7_relat_1(k1_xboole_0, B_1994)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_1994))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_44994])).
% 35.10/24.88  tff(c_45004, plain, (![B_18]: (k7_relat_1(k1_xboole_0, B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_45000])).
% 35.10/24.88  tff(c_45155, plain, (![B_2004]: (k7_relat_1(k1_xboole_0, B_2004)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_2004) | v1_xboole_0(B_2004))), inference(negUnitSimplification, [status(thm)], [c_62, c_45004])).
% 35.10/24.88  tff(c_45158, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_45155])).
% 35.10/24.88  tff(c_45161, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_45158])).
% 35.10/24.88  tff(c_45008, plain, (![C_1995, A_1996, B_1997]: (k7_relat_1(k7_relat_1(C_1995, A_1996), B_1997)=k7_relat_1(C_1995, k3_xboole_0(A_1996, B_1997)) | ~v1_relat_1(C_1995))), inference(cnfTransformation, [status(thm)], [f_42])).
% 35.10/24.88  tff(c_45029, plain, (![B_1997]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_1997))=k7_relat_1(k1_xboole_0, B_1997) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44990, c_45008])).
% 35.10/24.88  tff(c_45045, plain, (![B_1997]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_1997))=k7_relat_1(k1_xboole_0, B_1997))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_45029])).
% 35.10/24.88  tff(c_44893, plain, (![A_1981, B_1982, C_1983]: (k9_subset_1(A_1981, B_1982, C_1983)=k3_xboole_0(B_1982, C_1983) | ~m1_subset_1(C_1983, k1_zfmisc_1(A_1981)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 35.10/24.88  tff(c_44904, plain, (![B_1982]: (k9_subset_1('#skF_1', B_1982, '#skF_4')=k3_xboole_0(B_1982, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_44893])).
% 35.10/24.88  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_45426, plain, (![A_2028, B_2029, C_2030, D_2031]: (k2_partfun1(A_2028, B_2029, C_2030, D_2031)=k7_relat_1(C_2030, D_2031) | ~m1_subset_1(C_2030, k1_zfmisc_1(k2_zfmisc_1(A_2028, B_2029))) | ~v1_funct_1(C_2030))), inference(cnfTransformation, [status(thm)], [f_90])).
% 35.10/24.88  tff(c_45428, plain, (![D_2031]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_2031)=k7_relat_1('#skF_6', D_2031) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_45426])).
% 35.10/24.88  tff(c_45433, plain, (![D_2031]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_2031)=k7_relat_1('#skF_6', D_2031))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_45428])).
% 35.10/24.88  tff(c_147, plain, (![B_238, A_239]: (r1_subset_1(B_238, A_239) | ~r1_subset_1(A_239, B_238) | v1_xboole_0(B_238) | v1_xboole_0(A_239))), inference(cnfTransformation, [status(thm)], [f_74])).
% 35.10/24.88  tff(c_149, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_147])).
% 35.10/24.88  tff(c_152, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_149])).
% 35.10/24.88  tff(c_108, plain, (![C_230, A_231, B_232]: (v4_relat_1(C_230, A_231) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 35.10/24.88  tff(c_115, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_108])).
% 35.10/24.88  tff(c_128, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_115, c_12])).
% 35.10/24.88  tff(c_131, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_128])).
% 35.10/24.88  tff(c_212, plain, (![C_249, A_250, B_251]: (k7_relat_1(k7_relat_1(C_249, A_250), B_251)=k1_xboole_0 | ~r1_xboole_0(A_250, B_251) | ~v1_relat_1(C_249))), inference(cnfTransformation, [status(thm)], [f_48])).
% 35.10/24.88  tff(c_227, plain, (![B_251]: (k7_relat_1('#skF_6', B_251)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_251) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_212])).
% 35.10/24.88  tff(c_237, plain, (![B_252]: (k7_relat_1('#skF_6', B_252)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_252))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_227])).
% 35.10/24.88  tff(c_241, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_237])).
% 35.10/24.88  tff(c_253, plain, (![B_254]: (k7_relat_1('#skF_6', B_254)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_254) | v1_xboole_0(B_254))), inference(negUnitSimplification, [status(thm)], [c_58, c_241])).
% 35.10/24.88  tff(c_256, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_152, c_253])).
% 35.10/24.88  tff(c_259, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_256])).
% 35.10/24.88  tff(c_303, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_10])).
% 35.10/24.88  tff(c_311, plain, (![B_258]: (k7_relat_1(k1_xboole_0, B_258)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_258))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_303])).
% 35.10/24.88  tff(c_315, plain, (![B_18]: (k7_relat_1(k1_xboole_0, B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_311])).
% 35.10/24.88  tff(c_470, plain, (![B_272]: (k7_relat_1(k1_xboole_0, B_272)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_272) | v1_xboole_0(B_272))), inference(negUnitSimplification, [status(thm)], [c_62, c_315])).
% 35.10/24.88  tff(c_473, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_470])).
% 35.10/24.88  tff(c_476, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_473])).
% 35.10/24.88  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_103, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_95])).
% 35.10/24.88  tff(c_116, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_108])).
% 35.10/24.88  tff(c_134, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_116, c_12])).
% 35.10/24.88  tff(c_137, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_134])).
% 35.10/24.88  tff(c_230, plain, (![B_251]: (k7_relat_1('#skF_5', B_251)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_251) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_212])).
% 35.10/24.88  tff(c_245, plain, (![B_253]: (k7_relat_1('#skF_5', B_253)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_253))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_230])).
% 35.10/24.88  tff(c_249, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_245])).
% 35.10/24.88  tff(c_338, plain, (![B_260]: (k7_relat_1('#skF_5', B_260)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_260) | v1_xboole_0(B_260))), inference(negUnitSimplification, [status(thm)], [c_62, c_249])).
% 35.10/24.88  tff(c_341, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_338])).
% 35.10/24.88  tff(c_344, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_341])).
% 35.10/24.88  tff(c_260, plain, (![C_255, A_256, B_257]: (k7_relat_1(k7_relat_1(C_255, A_256), B_257)=k7_relat_1(C_255, k3_xboole_0(A_256, B_257)) | ~v1_relat_1(C_255))), inference(cnfTransformation, [status(thm)], [f_42])).
% 35.10/24.88  tff(c_290, plain, (![B_257]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_257))=k7_relat_1('#skF_5', B_257) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_260])).
% 35.10/24.88  tff(c_296, plain, (![B_257]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_257))=k7_relat_1('#skF_5', B_257))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_290])).
% 35.10/24.88  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_424, plain, (![A_265, B_266, C_267, D_268]: (k2_partfun1(A_265, B_266, C_267, D_268)=k7_relat_1(C_267, D_268) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_1(C_267))), inference(cnfTransformation, [status(thm)], [f_90])).
% 35.10/24.88  tff(c_428, plain, (![D_268]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_268)=k7_relat_1('#skF_5', D_268) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_424])).
% 35.10/24.88  tff(c_434, plain, (![D_268]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_268)=k7_relat_1('#skF_5', D_268))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_428])).
% 35.10/24.88  tff(c_8, plain, (![C_11, A_9, B_10]: (k7_relat_1(k7_relat_1(C_11, A_9), B_10)=k7_relat_1(C_11, k3_xboole_0(A_9, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 35.10/24.88  tff(c_300, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_8])).
% 35.10/24.88  tff(c_307, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_300])).
% 35.10/24.88  tff(c_426, plain, (![D_268]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_268)=k7_relat_1('#skF_6', D_268) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_424])).
% 35.10/24.88  tff(c_431, plain, (![D_268]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_268)=k7_relat_1('#skF_6', D_268))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_426])).
% 35.10/24.88  tff(c_163, plain, (![A_242, B_243, C_244]: (k9_subset_1(A_242, B_243, C_244)=k3_xboole_0(B_243, C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 35.10/24.88  tff(c_174, plain, (![B_243]: (k9_subset_1('#skF_1', B_243, '#skF_4')=k3_xboole_0(B_243, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_163])).
% 35.10/24.88  tff(c_40, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_105, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 35.10/24.88  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_476, c_344, c_296, c_434, c_307, c_431, c_174, c_174, c_105])).
% 35.10/24.88  tff(c_491, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 35.10/24.88  tff(c_44931, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44904, c_44904, c_491])).
% 35.10/24.88  tff(c_45437, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_45433, c_44931])).
% 35.10/24.88  tff(c_45438, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_45161, c_45045, c_45437])).
% 35.10/24.88  tff(c_45430, plain, (![D_2031]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_2031)=k7_relat_1('#skF_5', D_2031) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_45426])).
% 35.10/24.88  tff(c_45436, plain, (![D_2031]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_2031)=k7_relat_1('#skF_5', D_2031))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_45430])).
% 35.10/24.88  tff(c_45460, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_45438, c_45436])).
% 35.10/24.88  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_64, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 35.10/24.88  tff(c_45526, plain, (![C_2048, B_2047, F_2044, E_2046, D_2049, A_2045]: (v1_funct_1(k1_tmap_1(A_2045, B_2047, C_2048, D_2049, E_2046, F_2044)) | ~m1_subset_1(F_2044, k1_zfmisc_1(k2_zfmisc_1(D_2049, B_2047))) | ~v1_funct_2(F_2044, D_2049, B_2047) | ~v1_funct_1(F_2044) | ~m1_subset_1(E_2046, k1_zfmisc_1(k2_zfmisc_1(C_2048, B_2047))) | ~v1_funct_2(E_2046, C_2048, B_2047) | ~v1_funct_1(E_2046) | ~m1_subset_1(D_2049, k1_zfmisc_1(A_2045)) | v1_xboole_0(D_2049) | ~m1_subset_1(C_2048, k1_zfmisc_1(A_2045)) | v1_xboole_0(C_2048) | v1_xboole_0(B_2047) | v1_xboole_0(A_2045))), inference(cnfTransformation, [status(thm)], [f_172])).
% 35.10/24.88  tff(c_45528, plain, (![A_2045, C_2048, E_2046]: (v1_funct_1(k1_tmap_1(A_2045, '#skF_2', C_2048, '#skF_4', E_2046, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2046, k1_zfmisc_1(k2_zfmisc_1(C_2048, '#skF_2'))) | ~v1_funct_2(E_2046, C_2048, '#skF_2') | ~v1_funct_1(E_2046) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2045)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2048, k1_zfmisc_1(A_2045)) | v1_xboole_0(C_2048) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2045))), inference(resolution, [status(thm)], [c_42, c_45526])).
% 35.10/24.88  tff(c_45533, plain, (![A_2045, C_2048, E_2046]: (v1_funct_1(k1_tmap_1(A_2045, '#skF_2', C_2048, '#skF_4', E_2046, '#skF_6')) | ~m1_subset_1(E_2046, k1_zfmisc_1(k2_zfmisc_1(C_2048, '#skF_2'))) | ~v1_funct_2(E_2046, C_2048, '#skF_2') | ~v1_funct_1(E_2046) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2045)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2048, k1_zfmisc_1(A_2045)) | v1_xboole_0(C_2048) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2045))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_45528])).
% 35.10/24.88  tff(c_45544, plain, (![A_2054, C_2055, E_2056]: (v1_funct_1(k1_tmap_1(A_2054, '#skF_2', C_2055, '#skF_4', E_2056, '#skF_6')) | ~m1_subset_1(E_2056, k1_zfmisc_1(k2_zfmisc_1(C_2055, '#skF_2'))) | ~v1_funct_2(E_2056, C_2055, '#skF_2') | ~v1_funct_1(E_2056) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2054)) | ~m1_subset_1(C_2055, k1_zfmisc_1(A_2054)) | v1_xboole_0(C_2055) | v1_xboole_0(A_2054))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_45533])).
% 35.10/24.88  tff(c_45548, plain, (![A_2054]: (v1_funct_1(k1_tmap_1(A_2054, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2054)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2054)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2054))), inference(resolution, [status(thm)], [c_48, c_45544])).
% 35.10/24.88  tff(c_45555, plain, (![A_2054]: (v1_funct_1(k1_tmap_1(A_2054, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2054)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2054)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2054))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_45548])).
% 35.10/24.88  tff(c_45810, plain, (![A_2080]: (v1_funct_1(k1_tmap_1(A_2080, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2080)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2080)) | v1_xboole_0(A_2080))), inference(negUnitSimplification, [status(thm)], [c_62, c_45555])).
% 35.10/24.88  tff(c_45813, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_45810])).
% 35.10/24.88  tff(c_45816, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_45813])).
% 35.10/24.88  tff(c_45817, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_45816])).
% 35.10/24.88  tff(c_36, plain, (![F_163, C_160, E_162, B_159, D_161, A_158]: (v1_funct_2(k1_tmap_1(A_158, B_159, C_160, D_161, E_162, F_163), k4_subset_1(A_158, C_160, D_161), B_159) | ~m1_subset_1(F_163, k1_zfmisc_1(k2_zfmisc_1(D_161, B_159))) | ~v1_funct_2(F_163, D_161, B_159) | ~v1_funct_1(F_163) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(C_160, B_159))) | ~v1_funct_2(E_162, C_160, B_159) | ~v1_funct_1(E_162) | ~m1_subset_1(D_161, k1_zfmisc_1(A_158)) | v1_xboole_0(D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(A_158)) | v1_xboole_0(C_160) | v1_xboole_0(B_159) | v1_xboole_0(A_158))), inference(cnfTransformation, [status(thm)], [f_172])).
% 35.10/24.88  tff(c_34, plain, (![F_163, C_160, E_162, B_159, D_161, A_158]: (m1_subset_1(k1_tmap_1(A_158, B_159, C_160, D_161, E_162, F_163), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_158, C_160, D_161), B_159))) | ~m1_subset_1(F_163, k1_zfmisc_1(k2_zfmisc_1(D_161, B_159))) | ~v1_funct_2(F_163, D_161, B_159) | ~v1_funct_1(F_163) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(C_160, B_159))) | ~v1_funct_2(E_162, C_160, B_159) | ~v1_funct_1(E_162) | ~m1_subset_1(D_161, k1_zfmisc_1(A_158)) | v1_xboole_0(D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(A_158)) | v1_xboole_0(C_160) | v1_xboole_0(B_159) | v1_xboole_0(A_158))), inference(cnfTransformation, [status(thm)], [f_172])).
% 35.10/24.88  tff(c_46244, plain, (![B_2105, D_2102, C_2104, F_2106, A_2103, E_2101]: (k2_partfun1(k4_subset_1(A_2103, C_2104, D_2102), B_2105, k1_tmap_1(A_2103, B_2105, C_2104, D_2102, E_2101, F_2106), C_2104)=E_2101 | ~m1_subset_1(k1_tmap_1(A_2103, B_2105, C_2104, D_2102, E_2101, F_2106), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_2103, C_2104, D_2102), B_2105))) | ~v1_funct_2(k1_tmap_1(A_2103, B_2105, C_2104, D_2102, E_2101, F_2106), k4_subset_1(A_2103, C_2104, D_2102), B_2105) | ~v1_funct_1(k1_tmap_1(A_2103, B_2105, C_2104, D_2102, E_2101, F_2106)) | k2_partfun1(D_2102, B_2105, F_2106, k9_subset_1(A_2103, C_2104, D_2102))!=k2_partfun1(C_2104, B_2105, E_2101, k9_subset_1(A_2103, C_2104, D_2102)) | ~m1_subset_1(F_2106, k1_zfmisc_1(k2_zfmisc_1(D_2102, B_2105))) | ~v1_funct_2(F_2106, D_2102, B_2105) | ~v1_funct_1(F_2106) | ~m1_subset_1(E_2101, k1_zfmisc_1(k2_zfmisc_1(C_2104, B_2105))) | ~v1_funct_2(E_2101, C_2104, B_2105) | ~v1_funct_1(E_2101) | ~m1_subset_1(D_2102, k1_zfmisc_1(A_2103)) | v1_xboole_0(D_2102) | ~m1_subset_1(C_2104, k1_zfmisc_1(A_2103)) | v1_xboole_0(C_2104) | v1_xboole_0(B_2105) | v1_xboole_0(A_2103))), inference(cnfTransformation, [status(thm)], [f_138])).
% 35.10/24.88  tff(c_48814, plain, (![D_2284, F_2279, E_2281, C_2283, B_2282, A_2280]: (k2_partfun1(k4_subset_1(A_2280, C_2283, D_2284), B_2282, k1_tmap_1(A_2280, B_2282, C_2283, D_2284, E_2281, F_2279), C_2283)=E_2281 | ~v1_funct_2(k1_tmap_1(A_2280, B_2282, C_2283, D_2284, E_2281, F_2279), k4_subset_1(A_2280, C_2283, D_2284), B_2282) | ~v1_funct_1(k1_tmap_1(A_2280, B_2282, C_2283, D_2284, E_2281, F_2279)) | k2_partfun1(D_2284, B_2282, F_2279, k9_subset_1(A_2280, C_2283, D_2284))!=k2_partfun1(C_2283, B_2282, E_2281, k9_subset_1(A_2280, C_2283, D_2284)) | ~m1_subset_1(F_2279, k1_zfmisc_1(k2_zfmisc_1(D_2284, B_2282))) | ~v1_funct_2(F_2279, D_2284, B_2282) | ~v1_funct_1(F_2279) | ~m1_subset_1(E_2281, k1_zfmisc_1(k2_zfmisc_1(C_2283, B_2282))) | ~v1_funct_2(E_2281, C_2283, B_2282) | ~v1_funct_1(E_2281) | ~m1_subset_1(D_2284, k1_zfmisc_1(A_2280)) | v1_xboole_0(D_2284) | ~m1_subset_1(C_2283, k1_zfmisc_1(A_2280)) | v1_xboole_0(C_2283) | v1_xboole_0(B_2282) | v1_xboole_0(A_2280))), inference(resolution, [status(thm)], [c_34, c_46244])).
% 35.10/24.88  tff(c_85745, plain, (![C_3634, A_3631, B_3633, D_3635, F_3630, E_3632]: (k2_partfun1(k4_subset_1(A_3631, C_3634, D_3635), B_3633, k1_tmap_1(A_3631, B_3633, C_3634, D_3635, E_3632, F_3630), C_3634)=E_3632 | ~v1_funct_1(k1_tmap_1(A_3631, B_3633, C_3634, D_3635, E_3632, F_3630)) | k2_partfun1(D_3635, B_3633, F_3630, k9_subset_1(A_3631, C_3634, D_3635))!=k2_partfun1(C_3634, B_3633, E_3632, k9_subset_1(A_3631, C_3634, D_3635)) | ~m1_subset_1(F_3630, k1_zfmisc_1(k2_zfmisc_1(D_3635, B_3633))) | ~v1_funct_2(F_3630, D_3635, B_3633) | ~v1_funct_1(F_3630) | ~m1_subset_1(E_3632, k1_zfmisc_1(k2_zfmisc_1(C_3634, B_3633))) | ~v1_funct_2(E_3632, C_3634, B_3633) | ~v1_funct_1(E_3632) | ~m1_subset_1(D_3635, k1_zfmisc_1(A_3631)) | v1_xboole_0(D_3635) | ~m1_subset_1(C_3634, k1_zfmisc_1(A_3631)) | v1_xboole_0(C_3634) | v1_xboole_0(B_3633) | v1_xboole_0(A_3631))), inference(resolution, [status(thm)], [c_36, c_48814])).
% 35.10/24.88  tff(c_85749, plain, (![A_3631, C_3634, E_3632]: (k2_partfun1(k4_subset_1(A_3631, C_3634, '#skF_4'), '#skF_2', k1_tmap_1(A_3631, '#skF_2', C_3634, '#skF_4', E_3632, '#skF_6'), C_3634)=E_3632 | ~v1_funct_1(k1_tmap_1(A_3631, '#skF_2', C_3634, '#skF_4', E_3632, '#skF_6')) | k2_partfun1(C_3634, '#skF_2', E_3632, k9_subset_1(A_3631, C_3634, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_3631, C_3634, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3632, k1_zfmisc_1(k2_zfmisc_1(C_3634, '#skF_2'))) | ~v1_funct_2(E_3632, C_3634, '#skF_2') | ~v1_funct_1(E_3632) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3631)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3634, k1_zfmisc_1(A_3631)) | v1_xboole_0(C_3634) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3631))), inference(resolution, [status(thm)], [c_42, c_85745])).
% 35.10/24.88  tff(c_85755, plain, (![A_3631, C_3634, E_3632]: (k2_partfun1(k4_subset_1(A_3631, C_3634, '#skF_4'), '#skF_2', k1_tmap_1(A_3631, '#skF_2', C_3634, '#skF_4', E_3632, '#skF_6'), C_3634)=E_3632 | ~v1_funct_1(k1_tmap_1(A_3631, '#skF_2', C_3634, '#skF_4', E_3632, '#skF_6')) | k2_partfun1(C_3634, '#skF_2', E_3632, k9_subset_1(A_3631, C_3634, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3631, C_3634, '#skF_4')) | ~m1_subset_1(E_3632, k1_zfmisc_1(k2_zfmisc_1(C_3634, '#skF_2'))) | ~v1_funct_2(E_3632, C_3634, '#skF_2') | ~v1_funct_1(E_3632) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3631)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3634, k1_zfmisc_1(A_3631)) | v1_xboole_0(C_3634) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3631))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_45433, c_85749])).
% 35.10/24.88  tff(c_102232, plain, (![A_4114, C_4115, E_4116]: (k2_partfun1(k4_subset_1(A_4114, C_4115, '#skF_4'), '#skF_2', k1_tmap_1(A_4114, '#skF_2', C_4115, '#skF_4', E_4116, '#skF_6'), C_4115)=E_4116 | ~v1_funct_1(k1_tmap_1(A_4114, '#skF_2', C_4115, '#skF_4', E_4116, '#skF_6')) | k2_partfun1(C_4115, '#skF_2', E_4116, k9_subset_1(A_4114, C_4115, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4114, C_4115, '#skF_4')) | ~m1_subset_1(E_4116, k1_zfmisc_1(k2_zfmisc_1(C_4115, '#skF_2'))) | ~v1_funct_2(E_4116, C_4115, '#skF_2') | ~v1_funct_1(E_4116) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4114)) | ~m1_subset_1(C_4115, k1_zfmisc_1(A_4114)) | v1_xboole_0(C_4115) | v1_xboole_0(A_4114))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_85755])).
% 35.10/24.88  tff(c_102239, plain, (![A_4114]: (k2_partfun1(k4_subset_1(A_4114, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4114, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4114, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_4114, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4114, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4114)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4114)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4114))), inference(resolution, [status(thm)], [c_48, c_102232])).
% 35.10/24.88  tff(c_102249, plain, (![A_4114]: (k2_partfun1(k4_subset_1(A_4114, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4114, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4114, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4114, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4114, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4114)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4114)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4114))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_45436, c_102239])).
% 35.10/24.88  tff(c_102997, plain, (![A_4127]: (k2_partfun1(k4_subset_1(A_4127, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4127, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4127, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4127, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4127, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4127)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4127)) | v1_xboole_0(A_4127))), inference(negUnitSimplification, [status(thm)], [c_62, c_102249])).
% 35.10/24.88  tff(c_543, plain, (![B_285, A_286]: (r1_subset_1(B_285, A_286) | ~r1_subset_1(A_286, B_285) | v1_xboole_0(B_285) | v1_xboole_0(A_286))), inference(cnfTransformation, [status(thm)], [f_74])).
% 35.10/24.88  tff(c_545, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_543])).
% 35.10/24.88  tff(c_548, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_545])).
% 35.10/24.88  tff(c_567, plain, (![C_290, A_291, B_292]: (k7_relat_1(k7_relat_1(C_290, A_291), B_292)=k1_xboole_0 | ~r1_xboole_0(A_291, B_292) | ~v1_relat_1(C_290))), inference(cnfTransformation, [status(thm)], [f_48])).
% 35.10/24.88  tff(c_585, plain, (![B_292]: (k7_relat_1('#skF_6', B_292)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_292) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_522, c_567])).
% 35.10/24.88  tff(c_628, plain, (![B_297]: (k7_relat_1('#skF_6', B_297)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_297))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_585])).
% 35.10/24.88  tff(c_632, plain, (![B_18]: (k7_relat_1('#skF_6', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_628])).
% 35.10/24.88  tff(c_768, plain, (![B_307]: (k7_relat_1('#skF_6', B_307)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_307) | v1_xboole_0(B_307))), inference(negUnitSimplification, [status(thm)], [c_58, c_632])).
% 35.10/24.88  tff(c_771, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_548, c_768])).
% 35.10/24.88  tff(c_774, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_62, c_771])).
% 35.10/24.88  tff(c_781, plain, (![B_13]: (k7_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_13) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_774, c_10])).
% 35.10/24.88  tff(c_789, plain, (![B_308]: (k7_relat_1(k1_xboole_0, B_308)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_308))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_781])).
% 35.10/24.88  tff(c_793, plain, (![B_18]: (k7_relat_1(k1_xboole_0, B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_789])).
% 35.10/24.88  tff(c_833, plain, (![B_311]: (k7_relat_1(k1_xboole_0, B_311)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_311) | v1_xboole_0(B_311))), inference(negUnitSimplification, [status(thm)], [c_62, c_793])).
% 35.10/24.88  tff(c_836, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_833])).
% 35.10/24.88  tff(c_839, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_836])).
% 35.10/24.88  tff(c_778, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_774, c_8])).
% 35.10/24.88  tff(c_785, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_778])).
% 35.10/24.88  tff(c_515, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_507])).
% 35.10/24.88  tff(c_525, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_515, c_12])).
% 35.10/24.88  tff(c_528, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_525])).
% 35.10/24.88  tff(c_582, plain, (![B_292]: (k7_relat_1('#skF_5', B_292)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_292) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_528, c_567])).
% 35.10/24.88  tff(c_611, plain, (![B_295]: (k7_relat_1('#skF_5', B_295)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_295))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_582])).
% 35.10/24.88  tff(c_615, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_611])).
% 35.10/24.88  tff(c_645, plain, (![B_299]: (k7_relat_1('#skF_5', B_299)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_299) | v1_xboole_0(B_299))), inference(negUnitSimplification, [status(thm)], [c_62, c_615])).
% 35.10/24.88  tff(c_648, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_645])).
% 35.10/24.88  tff(c_651, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_648])).
% 35.10/24.88  tff(c_669, plain, (![C_301, A_302, B_303]: (k7_relat_1(k7_relat_1(C_301, A_302), B_303)=k7_relat_1(C_301, k3_xboole_0(A_302, B_303)) | ~v1_relat_1(C_301))), inference(cnfTransformation, [status(thm)], [f_42])).
% 35.10/24.88  tff(c_699, plain, (![B_303]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_303))=k7_relat_1('#skF_5', B_303) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_528, c_669])).
% 35.10/24.88  tff(c_708, plain, (![B_303]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_303))=k7_relat_1('#skF_5', B_303))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_699])).
% 35.10/24.88  tff(c_554, plain, (![A_287, B_288, C_289]: (k9_subset_1(A_287, B_288, C_289)=k3_xboole_0(B_288, C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(A_287)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 35.10/24.88  tff(c_565, plain, (![B_288]: (k9_subset_1('#skF_1', B_288, '#skF_4')=k3_xboole_0(B_288, '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_554])).
% 35.10/24.88  tff(c_1103, plain, (![E_339, F_337, C_341, B_340, A_338, D_342]: (v1_funct_1(k1_tmap_1(A_338, B_340, C_341, D_342, E_339, F_337)) | ~m1_subset_1(F_337, k1_zfmisc_1(k2_zfmisc_1(D_342, B_340))) | ~v1_funct_2(F_337, D_342, B_340) | ~v1_funct_1(F_337) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(C_341, B_340))) | ~v1_funct_2(E_339, C_341, B_340) | ~v1_funct_1(E_339) | ~m1_subset_1(D_342, k1_zfmisc_1(A_338)) | v1_xboole_0(D_342) | ~m1_subset_1(C_341, k1_zfmisc_1(A_338)) | v1_xboole_0(C_341) | v1_xboole_0(B_340) | v1_xboole_0(A_338))), inference(cnfTransformation, [status(thm)], [f_172])).
% 35.10/24.88  tff(c_1105, plain, (![A_338, C_341, E_339]: (v1_funct_1(k1_tmap_1(A_338, '#skF_2', C_341, '#skF_4', E_339, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(C_341, '#skF_2'))) | ~v1_funct_2(E_339, C_341, '#skF_2') | ~v1_funct_1(E_339) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_338)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_341, k1_zfmisc_1(A_338)) | v1_xboole_0(C_341) | v1_xboole_0('#skF_2') | v1_xboole_0(A_338))), inference(resolution, [status(thm)], [c_42, c_1103])).
% 35.10/24.88  tff(c_1110, plain, (![A_338, C_341, E_339]: (v1_funct_1(k1_tmap_1(A_338, '#skF_2', C_341, '#skF_4', E_339, '#skF_6')) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(C_341, '#skF_2'))) | ~v1_funct_2(E_339, C_341, '#skF_2') | ~v1_funct_1(E_339) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_338)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_341, k1_zfmisc_1(A_338)) | v1_xboole_0(C_341) | v1_xboole_0('#skF_2') | v1_xboole_0(A_338))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1105])).
% 35.10/24.88  tff(c_1128, plain, (![A_349, C_350, E_351]: (v1_funct_1(k1_tmap_1(A_349, '#skF_2', C_350, '#skF_4', E_351, '#skF_6')) | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(C_350, '#skF_2'))) | ~v1_funct_2(E_351, C_350, '#skF_2') | ~v1_funct_1(E_351) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_349)) | ~m1_subset_1(C_350, k1_zfmisc_1(A_349)) | v1_xboole_0(C_350) | v1_xboole_0(A_349))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_1110])).
% 35.10/24.88  tff(c_1132, plain, (![A_349]: (v1_funct_1(k1_tmap_1(A_349, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_349)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_349)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_349))), inference(resolution, [status(thm)], [c_48, c_1128])).
% 35.10/24.88  tff(c_1139, plain, (![A_349]: (v1_funct_1(k1_tmap_1(A_349, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_349)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_349)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_349))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1132])).
% 35.10/24.88  tff(c_1225, plain, (![A_375]: (v1_funct_1(k1_tmap_1(A_375, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_375)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_375)) | v1_xboole_0(A_375))), inference(negUnitSimplification, [status(thm)], [c_62, c_1139])).
% 35.10/24.88  tff(c_1228, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_1225])).
% 35.10/24.88  tff(c_1231, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1228])).
% 35.10/24.88  tff(c_1232, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1231])).
% 35.10/24.88  tff(c_870, plain, (![A_318, B_319, C_320, D_321]: (k2_partfun1(A_318, B_319, C_320, D_321)=k7_relat_1(C_320, D_321) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))) | ~v1_funct_1(C_320))), inference(cnfTransformation, [status(thm)], [f_90])).
% 35.10/24.88  tff(c_874, plain, (![D_321]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_321)=k7_relat_1('#skF_5', D_321) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_870])).
% 35.10/24.88  tff(c_880, plain, (![D_321]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_321)=k7_relat_1('#skF_5', D_321))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_874])).
% 35.10/24.88  tff(c_872, plain, (![D_321]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_321)=k7_relat_1('#skF_6', D_321) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_42, c_870])).
% 35.10/24.88  tff(c_877, plain, (![D_321]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_321)=k7_relat_1('#skF_6', D_321))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_872])).
% 35.10/24.88  tff(c_1828, plain, (![B_410, A_408, D_407, C_409, F_411, E_406]: (k2_partfun1(k4_subset_1(A_408, C_409, D_407), B_410, k1_tmap_1(A_408, B_410, C_409, D_407, E_406, F_411), D_407)=F_411 | ~m1_subset_1(k1_tmap_1(A_408, B_410, C_409, D_407, E_406, F_411), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_408, C_409, D_407), B_410))) | ~v1_funct_2(k1_tmap_1(A_408, B_410, C_409, D_407, E_406, F_411), k4_subset_1(A_408, C_409, D_407), B_410) | ~v1_funct_1(k1_tmap_1(A_408, B_410, C_409, D_407, E_406, F_411)) | k2_partfun1(D_407, B_410, F_411, k9_subset_1(A_408, C_409, D_407))!=k2_partfun1(C_409, B_410, E_406, k9_subset_1(A_408, C_409, D_407)) | ~m1_subset_1(F_411, k1_zfmisc_1(k2_zfmisc_1(D_407, B_410))) | ~v1_funct_2(F_411, D_407, B_410) | ~v1_funct_1(F_411) | ~m1_subset_1(E_406, k1_zfmisc_1(k2_zfmisc_1(C_409, B_410))) | ~v1_funct_2(E_406, C_409, B_410) | ~v1_funct_1(E_406) | ~m1_subset_1(D_407, k1_zfmisc_1(A_408)) | v1_xboole_0(D_407) | ~m1_subset_1(C_409, k1_zfmisc_1(A_408)) | v1_xboole_0(C_409) | v1_xboole_0(B_410) | v1_xboole_0(A_408))), inference(cnfTransformation, [status(thm)], [f_138])).
% 35.10/24.88  tff(c_4153, plain, (![E_588, F_586, D_591, C_590, A_587, B_589]: (k2_partfun1(k4_subset_1(A_587, C_590, D_591), B_589, k1_tmap_1(A_587, B_589, C_590, D_591, E_588, F_586), D_591)=F_586 | ~v1_funct_2(k1_tmap_1(A_587, B_589, C_590, D_591, E_588, F_586), k4_subset_1(A_587, C_590, D_591), B_589) | ~v1_funct_1(k1_tmap_1(A_587, B_589, C_590, D_591, E_588, F_586)) | k2_partfun1(D_591, B_589, F_586, k9_subset_1(A_587, C_590, D_591))!=k2_partfun1(C_590, B_589, E_588, k9_subset_1(A_587, C_590, D_591)) | ~m1_subset_1(F_586, k1_zfmisc_1(k2_zfmisc_1(D_591, B_589))) | ~v1_funct_2(F_586, D_591, B_589) | ~v1_funct_1(F_586) | ~m1_subset_1(E_588, k1_zfmisc_1(k2_zfmisc_1(C_590, B_589))) | ~v1_funct_2(E_588, C_590, B_589) | ~v1_funct_1(E_588) | ~m1_subset_1(D_591, k1_zfmisc_1(A_587)) | v1_xboole_0(D_591) | ~m1_subset_1(C_590, k1_zfmisc_1(A_587)) | v1_xboole_0(C_590) | v1_xboole_0(B_589) | v1_xboole_0(A_587))), inference(resolution, [status(thm)], [c_34, c_1828])).
% 35.10/24.88  tff(c_26792, plain, (![C_1466, F_1462, D_1467, E_1464, B_1465, A_1463]: (k2_partfun1(k4_subset_1(A_1463, C_1466, D_1467), B_1465, k1_tmap_1(A_1463, B_1465, C_1466, D_1467, E_1464, F_1462), D_1467)=F_1462 | ~v1_funct_1(k1_tmap_1(A_1463, B_1465, C_1466, D_1467, E_1464, F_1462)) | k2_partfun1(D_1467, B_1465, F_1462, k9_subset_1(A_1463, C_1466, D_1467))!=k2_partfun1(C_1466, B_1465, E_1464, k9_subset_1(A_1463, C_1466, D_1467)) | ~m1_subset_1(F_1462, k1_zfmisc_1(k2_zfmisc_1(D_1467, B_1465))) | ~v1_funct_2(F_1462, D_1467, B_1465) | ~v1_funct_1(F_1462) | ~m1_subset_1(E_1464, k1_zfmisc_1(k2_zfmisc_1(C_1466, B_1465))) | ~v1_funct_2(E_1464, C_1466, B_1465) | ~v1_funct_1(E_1464) | ~m1_subset_1(D_1467, k1_zfmisc_1(A_1463)) | v1_xboole_0(D_1467) | ~m1_subset_1(C_1466, k1_zfmisc_1(A_1463)) | v1_xboole_0(C_1466) | v1_xboole_0(B_1465) | v1_xboole_0(A_1463))), inference(resolution, [status(thm)], [c_36, c_4153])).
% 35.10/24.88  tff(c_26796, plain, (![A_1463, C_1466, E_1464]: (k2_partfun1(k4_subset_1(A_1463, C_1466, '#skF_4'), '#skF_2', k1_tmap_1(A_1463, '#skF_2', C_1466, '#skF_4', E_1464, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1463, '#skF_2', C_1466, '#skF_4', E_1464, '#skF_6')) | k2_partfun1(C_1466, '#skF_2', E_1464, k9_subset_1(A_1463, C_1466, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1463, C_1466, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1464, k1_zfmisc_1(k2_zfmisc_1(C_1466, '#skF_2'))) | ~v1_funct_2(E_1464, C_1466, '#skF_2') | ~v1_funct_1(E_1464) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1463)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1466, k1_zfmisc_1(A_1463)) | v1_xboole_0(C_1466) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1463))), inference(resolution, [status(thm)], [c_42, c_26792])).
% 35.10/24.88  tff(c_26802, plain, (![A_1463, C_1466, E_1464]: (k2_partfun1(k4_subset_1(A_1463, C_1466, '#skF_4'), '#skF_2', k1_tmap_1(A_1463, '#skF_2', C_1466, '#skF_4', E_1464, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1463, '#skF_2', C_1466, '#skF_4', E_1464, '#skF_6')) | k2_partfun1(C_1466, '#skF_2', E_1464, k9_subset_1(A_1463, C_1466, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1463, C_1466, '#skF_4')) | ~m1_subset_1(E_1464, k1_zfmisc_1(k2_zfmisc_1(C_1466, '#skF_2'))) | ~v1_funct_2(E_1464, C_1466, '#skF_2') | ~v1_funct_1(E_1464) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1463)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1466, k1_zfmisc_1(A_1463)) | v1_xboole_0(C_1466) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1463))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_877, c_26796])).
% 35.10/24.88  tff(c_44690, plain, (![A_1960, C_1961, E_1962]: (k2_partfun1(k4_subset_1(A_1960, C_1961, '#skF_4'), '#skF_2', k1_tmap_1(A_1960, '#skF_2', C_1961, '#skF_4', E_1962, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1960, '#skF_2', C_1961, '#skF_4', E_1962, '#skF_6')) | k2_partfun1(C_1961, '#skF_2', E_1962, k9_subset_1(A_1960, C_1961, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1960, C_1961, '#skF_4')) | ~m1_subset_1(E_1962, k1_zfmisc_1(k2_zfmisc_1(C_1961, '#skF_2'))) | ~v1_funct_2(E_1962, C_1961, '#skF_2') | ~v1_funct_1(E_1962) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1960)) | ~m1_subset_1(C_1961, k1_zfmisc_1(A_1960)) | v1_xboole_0(C_1961) | v1_xboole_0(A_1960))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_26802])).
% 35.10/24.88  tff(c_44697, plain, (![A_1960]: (k2_partfun1(k4_subset_1(A_1960, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1960, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1960, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1960, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1960, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1960)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1960)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1960))), inference(resolution, [status(thm)], [c_48, c_44690])).
% 35.10/24.88  tff(c_44707, plain, (![A_1960]: (k2_partfun1(k4_subset_1(A_1960, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1960, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1960, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1960, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1960, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1960)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1960)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1960))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_880, c_44697])).
% 35.10/24.88  tff(c_44843, plain, (![A_1976]: (k2_partfun1(k4_subset_1(A_1976, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1976, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1976, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1976, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1976, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1976)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1976)) | v1_xboole_0(A_1976))), inference(negUnitSimplification, [status(thm)], [c_62, c_44707])).
% 35.10/24.88  tff(c_490, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 35.10/24.88  tff(c_533, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_490])).
% 35.10/24.88  tff(c_44854, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_44843, c_533])).
% 35.10/24.88  tff(c_44868, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_839, c_785, c_651, c_708, c_565, c_565, c_1232, c_44854])).
% 35.10/24.88  tff(c_44870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_44868])).
% 35.10/24.88  tff(c_44871, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_490])).
% 35.10/24.88  tff(c_103009, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102997, c_44871])).
% 35.10/24.88  tff(c_103023, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_45161, c_45045, c_44904, c_45460, c_44904, c_45817, c_103009])).
% 35.10/24.88  tff(c_103025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_103023])).
% 35.10/24.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.10/24.88  
% 35.10/24.88  Inference rules
% 35.10/24.88  ----------------------
% 35.10/24.88  #Ref     : 0
% 35.10/24.88  #Sup     : 24561
% 35.10/24.88  #Fact    : 0
% 35.10/24.88  #Define  : 0
% 35.10/24.88  #Split   : 50
% 35.10/24.88  #Chain   : 0
% 35.10/24.88  #Close   : 0
% 35.10/24.88  
% 35.10/24.88  Ordering : KBO
% 35.10/24.88  
% 35.10/24.88  Simplification rules
% 35.10/24.88  ----------------------
% 35.10/24.88  #Subsume      : 8827
% 35.10/24.88  #Demod        : 20837
% 35.10/24.88  #Tautology    : 2207
% 35.10/24.88  #SimpNegUnit  : 420
% 35.10/24.88  #BackRed      : 29
% 35.10/24.88  
% 35.10/24.88  #Partial instantiations: 0
% 35.10/24.88  #Strategies tried      : 1
% 35.10/24.88  
% 35.10/24.88  Timing (in seconds)
% 35.10/24.88  ----------------------
% 35.10/24.88  Preprocessing        : 0.41
% 35.10/24.88  Parsing              : 0.20
% 35.10/24.88  CNF conversion       : 0.06
% 35.10/24.88  Main loop            : 23.66
% 35.10/24.88  Inferencing          : 3.75
% 35.10/24.88  Reduction            : 8.46
% 35.10/24.88  Demodulation         : 6.98
% 35.10/24.88  BG Simplification    : 0.44
% 35.10/24.88  Subsumption          : 10.11
% 35.10/24.88  Abstraction          : 0.71
% 35.10/24.88  MUC search           : 0.00
% 35.10/24.88  Cooper               : 0.00
% 35.10/24.88  Total                : 24.15
% 35.10/24.88  Index Insertion      : 0.00
% 35.10/24.88  Index Deletion       : 0.00
% 35.10/24.88  Index Matching       : 0.00
% 35.10/24.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
