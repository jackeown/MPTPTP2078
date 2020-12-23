%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:13 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 497 expanded)
%              Number of leaves         :   41 ( 199 expanded)
%              Depth                    :   12
%              Number of atoms          :  581 (2586 expanded)
%              Number of equality atoms :  113 ( 546 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_383,plain,(
    ! [C_277,A_278,B_279] :
      ( v1_relat_1(C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_390,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_383])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_xboole_0(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [A_226,B_227] :
      ( k3_xboole_0(A_226,B_227) = k1_xboole_0
      | ~ r1_xboole_0(A_226,B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_397,plain,(
    ! [A_280,B_281] :
      ( k3_xboole_0(A_280,B_281) = k1_xboole_0
      | k4_xboole_0(A_280,B_281) != A_280 ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_401,plain,(
    ! [A_3] : k3_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_397])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_453,plain,(
    ! [A_291,B_292] :
      ( k7_relat_1(A_291,B_292) = k1_xboole_0
      | ~ r1_xboole_0(B_292,k1_relat_1(A_291))
      | ~ v1_relat_1(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1222,plain,(
    ! [A_387,A_388] :
      ( k7_relat_1(A_387,A_388) = k1_xboole_0
      | ~ v1_relat_1(A_387)
      | k3_xboole_0(A_388,k1_relat_1(A_387)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_453])).

tff(c_1238,plain,(
    ! [A_389] :
      ( k7_relat_1(A_389,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_1222])).

tff(c_1246,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_390,c_1238])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_473,plain,(
    ! [A_295,B_296] :
      ( r1_xboole_0(A_295,B_296)
      | ~ r1_subset_1(A_295,B_296)
      | v1_xboole_0(B_296)
      | v1_xboole_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = A_4
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2847,plain,(
    ! [A_665,B_666] :
      ( k4_xboole_0(A_665,B_666) = A_665
      | ~ r1_subset_1(A_665,B_666)
      | v1_xboole_0(B_666)
      | v1_xboole_0(A_665) ) ),
    inference(resolution,[status(thm)],[c_473,c_8])).

tff(c_2853,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2847])).

tff(c_2857,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_2853])).

tff(c_89,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = k1_xboole_0
      | k4_xboole_0(A_4,B_5) != A_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_2871,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2857,c_89])).

tff(c_492,plain,(
    ! [A_298,B_299,C_300] :
      ( k9_subset_1(A_298,B_299,C_300) = k3_xboole_0(B_299,C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(A_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_503,plain,(
    ! [B_299] : k9_subset_1('#skF_1',B_299,'#skF_4') = k3_xboole_0(B_299,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_492])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_391,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_383])).

tff(c_1245,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_391,c_1238])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_2947,plain,(
    ! [E_676,D_675,C_673,B_674,F_678,A_677] :
      ( v1_funct_1(k1_tmap_1(A_677,B_674,C_673,D_675,E_676,F_678))
      | ~ m1_subset_1(F_678,k1_zfmisc_1(k2_zfmisc_1(D_675,B_674)))
      | ~ v1_funct_2(F_678,D_675,B_674)
      | ~ v1_funct_1(F_678)
      | ~ m1_subset_1(E_676,k1_zfmisc_1(k2_zfmisc_1(C_673,B_674)))
      | ~ v1_funct_2(E_676,C_673,B_674)
      | ~ v1_funct_1(E_676)
      | ~ m1_subset_1(D_675,k1_zfmisc_1(A_677))
      | v1_xboole_0(D_675)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(A_677))
      | v1_xboole_0(C_673)
      | v1_xboole_0(B_674)
      | v1_xboole_0(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2949,plain,(
    ! [A_677,C_673,E_676] :
      ( v1_funct_1(k1_tmap_1(A_677,'#skF_2',C_673,'#skF_4',E_676,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_676,k1_zfmisc_1(k2_zfmisc_1(C_673,'#skF_2')))
      | ~ v1_funct_2(E_676,C_673,'#skF_2')
      | ~ v1_funct_1(E_676)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_677))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_673,k1_zfmisc_1(A_677))
      | v1_xboole_0(C_673)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_677) ) ),
    inference(resolution,[status(thm)],[c_52,c_2947])).

tff(c_2954,plain,(
    ! [A_677,C_673,E_676] :
      ( v1_funct_1(k1_tmap_1(A_677,'#skF_2',C_673,'#skF_4',E_676,'#skF_6'))
      | ~ m1_subset_1(E_676,k1_zfmisc_1(k2_zfmisc_1(C_673,'#skF_2')))
      | ~ v1_funct_2(E_676,C_673,'#skF_2')
      | ~ v1_funct_1(E_676)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_677))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_673,k1_zfmisc_1(A_677))
      | v1_xboole_0(C_673)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_677) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2949])).

tff(c_2960,plain,(
    ! [A_679,C_680,E_681] :
      ( v1_funct_1(k1_tmap_1(A_679,'#skF_2',C_680,'#skF_4',E_681,'#skF_6'))
      | ~ m1_subset_1(E_681,k1_zfmisc_1(k2_zfmisc_1(C_680,'#skF_2')))
      | ~ v1_funct_2(E_681,C_680,'#skF_2')
      | ~ v1_funct_1(E_681)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_679))
      | ~ m1_subset_1(C_680,k1_zfmisc_1(A_679))
      | v1_xboole_0(C_680)
      | v1_xboole_0(A_679) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2954])).

tff(c_2964,plain,(
    ! [A_679] :
      ( v1_funct_1(k1_tmap_1(A_679,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_679))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_679))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_679) ) ),
    inference(resolution,[status(thm)],[c_58,c_2960])).

tff(c_2971,plain,(
    ! [A_679] :
      ( v1_funct_1(k1_tmap_1(A_679,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_679))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_679))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_679) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2964])).

tff(c_2981,plain,(
    ! [A_689] :
      ( v1_funct_1(k1_tmap_1(A_689,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_689))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_689))
      | v1_xboole_0(A_689) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2971])).

tff(c_2984,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_2981])).

tff(c_2987,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2984])).

tff(c_2988,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2987])).

tff(c_1102,plain,(
    ! [A_371,B_372,C_373,D_374] :
      ( k2_partfun1(A_371,B_372,C_373,D_374) = k7_relat_1(C_373,D_374)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372)))
      | ~ v1_funct_1(C_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1106,plain,(
    ! [D_374] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_374) = k7_relat_1('#skF_5',D_374)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_1102])).

tff(c_1112,plain,(
    ! [D_374] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_374) = k7_relat_1('#skF_5',D_374) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1106])).

tff(c_1104,plain,(
    ! [D_374] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_374) = k7_relat_1('#skF_6',D_374)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_1102])).

tff(c_1109,plain,(
    ! [D_374] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_374) = k7_relat_1('#skF_6',D_374) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1104])).

tff(c_46,plain,(
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

tff(c_44,plain,(
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

tff(c_3144,plain,(
    ! [A_715,D_720,B_717,C_719,F_718,E_716] :
      ( k2_partfun1(k4_subset_1(A_715,C_719,D_720),B_717,k1_tmap_1(A_715,B_717,C_719,D_720,E_716,F_718),C_719) = E_716
      | ~ m1_subset_1(k1_tmap_1(A_715,B_717,C_719,D_720,E_716,F_718),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_715,C_719,D_720),B_717)))
      | ~ v1_funct_2(k1_tmap_1(A_715,B_717,C_719,D_720,E_716,F_718),k4_subset_1(A_715,C_719,D_720),B_717)
      | ~ v1_funct_1(k1_tmap_1(A_715,B_717,C_719,D_720,E_716,F_718))
      | k2_partfun1(D_720,B_717,F_718,k9_subset_1(A_715,C_719,D_720)) != k2_partfun1(C_719,B_717,E_716,k9_subset_1(A_715,C_719,D_720))
      | ~ m1_subset_1(F_718,k1_zfmisc_1(k2_zfmisc_1(D_720,B_717)))
      | ~ v1_funct_2(F_718,D_720,B_717)
      | ~ v1_funct_1(F_718)
      | ~ m1_subset_1(E_716,k1_zfmisc_1(k2_zfmisc_1(C_719,B_717)))
      | ~ v1_funct_2(E_716,C_719,B_717)
      | ~ v1_funct_1(E_716)
      | ~ m1_subset_1(D_720,k1_zfmisc_1(A_715))
      | v1_xboole_0(D_720)
      | ~ m1_subset_1(C_719,k1_zfmisc_1(A_715))
      | v1_xboole_0(C_719)
      | v1_xboole_0(B_717)
      | v1_xboole_0(A_715) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_3796,plain,(
    ! [B_840,E_842,A_843,C_839,D_841,F_844] :
      ( k2_partfun1(k4_subset_1(A_843,C_839,D_841),B_840,k1_tmap_1(A_843,B_840,C_839,D_841,E_842,F_844),C_839) = E_842
      | ~ v1_funct_2(k1_tmap_1(A_843,B_840,C_839,D_841,E_842,F_844),k4_subset_1(A_843,C_839,D_841),B_840)
      | ~ v1_funct_1(k1_tmap_1(A_843,B_840,C_839,D_841,E_842,F_844))
      | k2_partfun1(D_841,B_840,F_844,k9_subset_1(A_843,C_839,D_841)) != k2_partfun1(C_839,B_840,E_842,k9_subset_1(A_843,C_839,D_841))
      | ~ m1_subset_1(F_844,k1_zfmisc_1(k2_zfmisc_1(D_841,B_840)))
      | ~ v1_funct_2(F_844,D_841,B_840)
      | ~ v1_funct_1(F_844)
      | ~ m1_subset_1(E_842,k1_zfmisc_1(k2_zfmisc_1(C_839,B_840)))
      | ~ v1_funct_2(E_842,C_839,B_840)
      | ~ v1_funct_1(E_842)
      | ~ m1_subset_1(D_841,k1_zfmisc_1(A_843))
      | v1_xboole_0(D_841)
      | ~ m1_subset_1(C_839,k1_zfmisc_1(A_843))
      | v1_xboole_0(C_839)
      | v1_xboole_0(B_840)
      | v1_xboole_0(A_843) ) ),
    inference(resolution,[status(thm)],[c_44,c_3144])).

tff(c_3863,plain,(
    ! [D_869,F_872,B_868,C_867,E_870,A_871] :
      ( k2_partfun1(k4_subset_1(A_871,C_867,D_869),B_868,k1_tmap_1(A_871,B_868,C_867,D_869,E_870,F_872),C_867) = E_870
      | ~ v1_funct_1(k1_tmap_1(A_871,B_868,C_867,D_869,E_870,F_872))
      | k2_partfun1(D_869,B_868,F_872,k9_subset_1(A_871,C_867,D_869)) != k2_partfun1(C_867,B_868,E_870,k9_subset_1(A_871,C_867,D_869))
      | ~ m1_subset_1(F_872,k1_zfmisc_1(k2_zfmisc_1(D_869,B_868)))
      | ~ v1_funct_2(F_872,D_869,B_868)
      | ~ v1_funct_1(F_872)
      | ~ m1_subset_1(E_870,k1_zfmisc_1(k2_zfmisc_1(C_867,B_868)))
      | ~ v1_funct_2(E_870,C_867,B_868)
      | ~ v1_funct_1(E_870)
      | ~ m1_subset_1(D_869,k1_zfmisc_1(A_871))
      | v1_xboole_0(D_869)
      | ~ m1_subset_1(C_867,k1_zfmisc_1(A_871))
      | v1_xboole_0(C_867)
      | v1_xboole_0(B_868)
      | v1_xboole_0(A_871) ) ),
    inference(resolution,[status(thm)],[c_46,c_3796])).

tff(c_3867,plain,(
    ! [A_871,C_867,E_870] :
      ( k2_partfun1(k4_subset_1(A_871,C_867,'#skF_4'),'#skF_2',k1_tmap_1(A_871,'#skF_2',C_867,'#skF_4',E_870,'#skF_6'),C_867) = E_870
      | ~ v1_funct_1(k1_tmap_1(A_871,'#skF_2',C_867,'#skF_4',E_870,'#skF_6'))
      | k2_partfun1(C_867,'#skF_2',E_870,k9_subset_1(A_871,C_867,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_871,C_867,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_870,k1_zfmisc_1(k2_zfmisc_1(C_867,'#skF_2')))
      | ~ v1_funct_2(E_870,C_867,'#skF_2')
      | ~ v1_funct_1(E_870)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_871))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_867,k1_zfmisc_1(A_871))
      | v1_xboole_0(C_867)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_871) ) ),
    inference(resolution,[status(thm)],[c_52,c_3863])).

tff(c_3873,plain,(
    ! [A_871,C_867,E_870] :
      ( k2_partfun1(k4_subset_1(A_871,C_867,'#skF_4'),'#skF_2',k1_tmap_1(A_871,'#skF_2',C_867,'#skF_4',E_870,'#skF_6'),C_867) = E_870
      | ~ v1_funct_1(k1_tmap_1(A_871,'#skF_2',C_867,'#skF_4',E_870,'#skF_6'))
      | k2_partfun1(C_867,'#skF_2',E_870,k9_subset_1(A_871,C_867,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_871,C_867,'#skF_4'))
      | ~ m1_subset_1(E_870,k1_zfmisc_1(k2_zfmisc_1(C_867,'#skF_2')))
      | ~ v1_funct_2(E_870,C_867,'#skF_2')
      | ~ v1_funct_1(E_870)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_871))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_867,k1_zfmisc_1(A_871))
      | v1_xboole_0(C_867)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_871) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1109,c_3867])).

tff(c_3879,plain,(
    ! [A_873,C_874,E_875] :
      ( k2_partfun1(k4_subset_1(A_873,C_874,'#skF_4'),'#skF_2',k1_tmap_1(A_873,'#skF_2',C_874,'#skF_4',E_875,'#skF_6'),C_874) = E_875
      | ~ v1_funct_1(k1_tmap_1(A_873,'#skF_2',C_874,'#skF_4',E_875,'#skF_6'))
      | k2_partfun1(C_874,'#skF_2',E_875,k9_subset_1(A_873,C_874,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_873,C_874,'#skF_4'))
      | ~ m1_subset_1(E_875,k1_zfmisc_1(k2_zfmisc_1(C_874,'#skF_2')))
      | ~ v1_funct_2(E_875,C_874,'#skF_2')
      | ~ v1_funct_1(E_875)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_873))
      | ~ m1_subset_1(C_874,k1_zfmisc_1(A_873))
      | v1_xboole_0(C_874)
      | v1_xboole_0(A_873) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_3873])).

tff(c_3886,plain,(
    ! [A_873] :
      ( k2_partfun1(k4_subset_1(A_873,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_873,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_873,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_873,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_873,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_873))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_873))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_873) ) ),
    inference(resolution,[status(thm)],[c_58,c_3879])).

tff(c_3896,plain,(
    ! [A_873] :
      ( k2_partfun1(k4_subset_1(A_873,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_873,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_873,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_873,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_873,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_873))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_873))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_873) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1112,c_3886])).

tff(c_3976,plain,(
    ! [A_892] :
      ( k2_partfun1(k4_subset_1(A_892,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_892,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_892,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_892,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_892,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_892))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_892))
      | v1_xboole_0(A_892) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3896])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1338,plain,(
    ! [A_394,B_395] :
      ( k3_xboole_0(A_394,B_395) = k1_xboole_0
      | ~ r1_subset_1(A_394,B_395)
      | v1_xboole_0(B_395)
      | v1_xboole_0(A_394) ) ),
    inference(resolution,[status(thm)],[c_473,c_2])).

tff(c_1347,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1338])).

tff(c_1352,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_1347])).

tff(c_1394,plain,(
    ! [C_398,B_399,F_403,D_400,A_402,E_401] :
      ( v1_funct_1(k1_tmap_1(A_402,B_399,C_398,D_400,E_401,F_403))
      | ~ m1_subset_1(F_403,k1_zfmisc_1(k2_zfmisc_1(D_400,B_399)))
      | ~ v1_funct_2(F_403,D_400,B_399)
      | ~ v1_funct_1(F_403)
      | ~ m1_subset_1(E_401,k1_zfmisc_1(k2_zfmisc_1(C_398,B_399)))
      | ~ v1_funct_2(E_401,C_398,B_399)
      | ~ v1_funct_1(E_401)
      | ~ m1_subset_1(D_400,k1_zfmisc_1(A_402))
      | v1_xboole_0(D_400)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(A_402))
      | v1_xboole_0(C_398)
      | v1_xboole_0(B_399)
      | v1_xboole_0(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1396,plain,(
    ! [A_402,C_398,E_401] :
      ( v1_funct_1(k1_tmap_1(A_402,'#skF_2',C_398,'#skF_4',E_401,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_401,k1_zfmisc_1(k2_zfmisc_1(C_398,'#skF_2')))
      | ~ v1_funct_2(E_401,C_398,'#skF_2')
      | ~ v1_funct_1(E_401)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_402))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_398,k1_zfmisc_1(A_402))
      | v1_xboole_0(C_398)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_402) ) ),
    inference(resolution,[status(thm)],[c_52,c_1394])).

tff(c_1401,plain,(
    ! [A_402,C_398,E_401] :
      ( v1_funct_1(k1_tmap_1(A_402,'#skF_2',C_398,'#skF_4',E_401,'#skF_6'))
      | ~ m1_subset_1(E_401,k1_zfmisc_1(k2_zfmisc_1(C_398,'#skF_2')))
      | ~ v1_funct_2(E_401,C_398,'#skF_2')
      | ~ v1_funct_1(E_401)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_402))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_398,k1_zfmisc_1(A_402))
      | v1_xboole_0(C_398)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_402) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1396])).

tff(c_1459,plain,(
    ! [A_417,C_418,E_419] :
      ( v1_funct_1(k1_tmap_1(A_417,'#skF_2',C_418,'#skF_4',E_419,'#skF_6'))
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(C_418,'#skF_2')))
      | ~ v1_funct_2(E_419,C_418,'#skF_2')
      | ~ v1_funct_1(E_419)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_417))
      | ~ m1_subset_1(C_418,k1_zfmisc_1(A_417))
      | v1_xboole_0(C_418)
      | v1_xboole_0(A_417) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1401])).

tff(c_1463,plain,(
    ! [A_417] :
      ( v1_funct_1(k1_tmap_1(A_417,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_417))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_417))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_417) ) ),
    inference(resolution,[status(thm)],[c_58,c_1459])).

tff(c_1470,plain,(
    ! [A_417] :
      ( v1_funct_1(k1_tmap_1(A_417,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_417))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_417))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1463])).

tff(c_1479,plain,(
    ! [A_421] :
      ( v1_funct_1(k1_tmap_1(A_421,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_421))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_421))
      | v1_xboole_0(A_421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1470])).

tff(c_1482,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1479])).

tff(c_1485,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1482])).

tff(c_1486,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1485])).

tff(c_1629,plain,(
    ! [F_452,B_451,A_449,C_453,D_454,E_450] :
      ( k2_partfun1(k4_subset_1(A_449,C_453,D_454),B_451,k1_tmap_1(A_449,B_451,C_453,D_454,E_450,F_452),D_454) = F_452
      | ~ m1_subset_1(k1_tmap_1(A_449,B_451,C_453,D_454,E_450,F_452),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_449,C_453,D_454),B_451)))
      | ~ v1_funct_2(k1_tmap_1(A_449,B_451,C_453,D_454,E_450,F_452),k4_subset_1(A_449,C_453,D_454),B_451)
      | ~ v1_funct_1(k1_tmap_1(A_449,B_451,C_453,D_454,E_450,F_452))
      | k2_partfun1(D_454,B_451,F_452,k9_subset_1(A_449,C_453,D_454)) != k2_partfun1(C_453,B_451,E_450,k9_subset_1(A_449,C_453,D_454))
      | ~ m1_subset_1(F_452,k1_zfmisc_1(k2_zfmisc_1(D_454,B_451)))
      | ~ v1_funct_2(F_452,D_454,B_451)
      | ~ v1_funct_1(F_452)
      | ~ m1_subset_1(E_450,k1_zfmisc_1(k2_zfmisc_1(C_453,B_451)))
      | ~ v1_funct_2(E_450,C_453,B_451)
      | ~ v1_funct_1(E_450)
      | ~ m1_subset_1(D_454,k1_zfmisc_1(A_449))
      | v1_xboole_0(D_454)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(A_449))
      | v1_xboole_0(C_453)
      | v1_xboole_0(B_451)
      | v1_xboole_0(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2086,plain,(
    ! [E_569,F_571,C_566,D_568,A_570,B_567] :
      ( k2_partfun1(k4_subset_1(A_570,C_566,D_568),B_567,k1_tmap_1(A_570,B_567,C_566,D_568,E_569,F_571),D_568) = F_571
      | ~ v1_funct_2(k1_tmap_1(A_570,B_567,C_566,D_568,E_569,F_571),k4_subset_1(A_570,C_566,D_568),B_567)
      | ~ v1_funct_1(k1_tmap_1(A_570,B_567,C_566,D_568,E_569,F_571))
      | k2_partfun1(D_568,B_567,F_571,k9_subset_1(A_570,C_566,D_568)) != k2_partfun1(C_566,B_567,E_569,k9_subset_1(A_570,C_566,D_568))
      | ~ m1_subset_1(F_571,k1_zfmisc_1(k2_zfmisc_1(D_568,B_567)))
      | ~ v1_funct_2(F_571,D_568,B_567)
      | ~ v1_funct_1(F_571)
      | ~ m1_subset_1(E_569,k1_zfmisc_1(k2_zfmisc_1(C_566,B_567)))
      | ~ v1_funct_2(E_569,C_566,B_567)
      | ~ v1_funct_1(E_569)
      | ~ m1_subset_1(D_568,k1_zfmisc_1(A_570))
      | v1_xboole_0(D_568)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(A_570))
      | v1_xboole_0(C_566)
      | v1_xboole_0(B_567)
      | v1_xboole_0(A_570) ) ),
    inference(resolution,[status(thm)],[c_44,c_1629])).

tff(c_2341,plain,(
    ! [F_614,C_609,D_611,B_610,A_613,E_612] :
      ( k2_partfun1(k4_subset_1(A_613,C_609,D_611),B_610,k1_tmap_1(A_613,B_610,C_609,D_611,E_612,F_614),D_611) = F_614
      | ~ v1_funct_1(k1_tmap_1(A_613,B_610,C_609,D_611,E_612,F_614))
      | k2_partfun1(D_611,B_610,F_614,k9_subset_1(A_613,C_609,D_611)) != k2_partfun1(C_609,B_610,E_612,k9_subset_1(A_613,C_609,D_611))
      | ~ m1_subset_1(F_614,k1_zfmisc_1(k2_zfmisc_1(D_611,B_610)))
      | ~ v1_funct_2(F_614,D_611,B_610)
      | ~ v1_funct_1(F_614)
      | ~ m1_subset_1(E_612,k1_zfmisc_1(k2_zfmisc_1(C_609,B_610)))
      | ~ v1_funct_2(E_612,C_609,B_610)
      | ~ v1_funct_1(E_612)
      | ~ m1_subset_1(D_611,k1_zfmisc_1(A_613))
      | v1_xboole_0(D_611)
      | ~ m1_subset_1(C_609,k1_zfmisc_1(A_613))
      | v1_xboole_0(C_609)
      | v1_xboole_0(B_610)
      | v1_xboole_0(A_613) ) ),
    inference(resolution,[status(thm)],[c_46,c_2086])).

tff(c_2345,plain,(
    ! [A_613,C_609,E_612] :
      ( k2_partfun1(k4_subset_1(A_613,C_609,'#skF_4'),'#skF_2',k1_tmap_1(A_613,'#skF_2',C_609,'#skF_4',E_612,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_613,'#skF_2',C_609,'#skF_4',E_612,'#skF_6'))
      | k2_partfun1(C_609,'#skF_2',E_612,k9_subset_1(A_613,C_609,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_613,C_609,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_612,k1_zfmisc_1(k2_zfmisc_1(C_609,'#skF_2')))
      | ~ v1_funct_2(E_612,C_609,'#skF_2')
      | ~ v1_funct_1(E_612)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_613))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_609,k1_zfmisc_1(A_613))
      | v1_xboole_0(C_609)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_613) ) ),
    inference(resolution,[status(thm)],[c_52,c_2341])).

tff(c_2351,plain,(
    ! [A_613,C_609,E_612] :
      ( k2_partfun1(k4_subset_1(A_613,C_609,'#skF_4'),'#skF_2',k1_tmap_1(A_613,'#skF_2',C_609,'#skF_4',E_612,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_613,'#skF_2',C_609,'#skF_4',E_612,'#skF_6'))
      | k2_partfun1(C_609,'#skF_2',E_612,k9_subset_1(A_613,C_609,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_613,C_609,'#skF_4'))
      | ~ m1_subset_1(E_612,k1_zfmisc_1(k2_zfmisc_1(C_609,'#skF_2')))
      | ~ v1_funct_2(E_612,C_609,'#skF_2')
      | ~ v1_funct_1(E_612)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_613))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_609,k1_zfmisc_1(A_613))
      | v1_xboole_0(C_609)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1109,c_2345])).

tff(c_2716,plain,(
    ! [A_658,C_659,E_660] :
      ( k2_partfun1(k4_subset_1(A_658,C_659,'#skF_4'),'#skF_2',k1_tmap_1(A_658,'#skF_2',C_659,'#skF_4',E_660,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_658,'#skF_2',C_659,'#skF_4',E_660,'#skF_6'))
      | k2_partfun1(C_659,'#skF_2',E_660,k9_subset_1(A_658,C_659,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_658,C_659,'#skF_4'))
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(C_659,'#skF_2')))
      | ~ v1_funct_2(E_660,C_659,'#skF_2')
      | ~ v1_funct_1(E_660)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_658))
      | ~ m1_subset_1(C_659,k1_zfmisc_1(A_658))
      | v1_xboole_0(C_659)
      | v1_xboole_0(A_658) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2351])).

tff(c_2723,plain,(
    ! [A_658] :
      ( k2_partfun1(k4_subset_1(A_658,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_658,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_658,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_658,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_658,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_658))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_658))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_658) ) ),
    inference(resolution,[status(thm)],[c_58,c_2716])).

tff(c_2733,plain,(
    ! [A_658] :
      ( k2_partfun1(k4_subset_1(A_658,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_658,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_658,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_658,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_658,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_658))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_658))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1112,c_2723])).

tff(c_2751,plain,(
    ! [A_662] :
      ( k2_partfun1(k4_subset_1(A_662,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_662,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_662,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_662,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_662,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_662))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_662))
      | v1_xboole_0(A_662) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2733])).

tff(c_126,plain,(
    ! [C_234,A_235,B_236] :
      ( v1_relat_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_133,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_126])).

tff(c_144,plain,(
    ! [A_240,B_241] :
      ( k3_xboole_0(A_240,B_241) = k1_xboole_0
      | k4_xboole_0(A_240,B_241) != A_240 ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_148,plain,(
    ! [A_3] : k3_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_201,plain,(
    ! [A_251,B_252] :
      ( k7_relat_1(A_251,B_252) = k1_xboole_0
      | ~ r1_xboole_0(B_252,k1_relat_1(A_251))
      | ~ v1_relat_1(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_296,plain,(
    ! [A_266,A_267] :
      ( k7_relat_1(A_266,A_267) = k1_xboole_0
      | ~ v1_relat_1(A_266)
      | k3_xboole_0(A_267,k1_relat_1(A_266)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_201])).

tff(c_302,plain,(
    ! [A_268] :
      ( k7_relat_1(A_268,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_296])).

tff(c_310,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133,c_302])).

tff(c_134,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_126])).

tff(c_309,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_302])).

tff(c_212,plain,(
    ! [A_253,B_254] :
      ( r1_xboole_0(A_253,B_254)
      | ~ r1_subset_1(A_253,B_254)
      | v1_xboole_0(B_254)
      | v1_xboole_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_349,plain,(
    ! [A_275,B_276] :
      ( k4_xboole_0(A_275,B_276) = A_275
      | ~ r1_subset_1(A_275,B_276)
      | v1_xboole_0(B_276)
      | v1_xboole_0(A_275) ) ),
    inference(resolution,[status(thm)],[c_212,c_8])).

tff(c_355,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_349])).

tff(c_359,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_355])).

tff(c_373,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_89])).

tff(c_315,plain,(
    ! [A_269,B_270,C_271,D_272] :
      ( k2_partfun1(A_269,B_270,C_271,D_272) = k7_relat_1(C_271,D_272)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ v1_funct_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_317,plain,(
    ! [D_272] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_272) = k7_relat_1('#skF_6',D_272)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_315])).

tff(c_322,plain,(
    ! [D_272] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_272) = k7_relat_1('#skF_6',D_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_317])).

tff(c_319,plain,(
    ! [D_272] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_272) = k7_relat_1('#skF_5',D_272)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_315])).

tff(c_325,plain,(
    ! [D_272] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_272) = k7_relat_1('#skF_5',D_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_319])).

tff(c_230,plain,(
    ! [A_255,B_256,C_257] :
      ( k9_subset_1(A_255,B_256,C_257) = k3_xboole_0(B_256,C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(A_255)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_241,plain,(
    ! [B_256] : k9_subset_1('#skF_1',B_256,'#skF_4') = k3_xboole_0(B_256,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_230])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_123,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_243,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_241,c_123])).

tff(c_348,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_325,c_243])).

tff(c_376,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_373,c_348])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_309,c_376])).

tff(c_380,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1275,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_2762,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_1275])).

tff(c_2776,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1246,c_1352,c_503,c_1245,c_1352,c_503,c_1486,c_2762])).

tff(c_2778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2776])).

tff(c_2779,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_3985,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3976,c_2779])).

tff(c_3996,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1246,c_2871,c_503,c_1245,c_2871,c_503,c_2988,c_3985])).

tff(c_3998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:06:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.47  
% 7.51/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.51/2.47  
% 7.51/2.47  %Foreground sorts:
% 7.51/2.47  
% 7.51/2.47  
% 7.51/2.47  %Background operators:
% 7.51/2.47  
% 7.51/2.47  
% 7.51/2.47  %Foreground operators:
% 7.51/2.47  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.51/2.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.51/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.51/2.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.51/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.51/2.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.51/2.47  tff('#skF_5', type, '#skF_5': $i).
% 7.51/2.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.51/2.47  tff('#skF_6', type, '#skF_6': $i).
% 7.51/2.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.51/2.47  tff('#skF_2', type, '#skF_2': $i).
% 7.51/2.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.51/2.47  tff('#skF_3', type, '#skF_3': $i).
% 7.51/2.47  tff('#skF_1', type, '#skF_1': $i).
% 7.51/2.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.51/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.51/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.51/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.51/2.47  tff('#skF_4', type, '#skF_4': $i).
% 7.51/2.47  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.51/2.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.51/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.51/2.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.51/2.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.51/2.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.51/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.51/2.47  
% 7.51/2.50  tff(f_225, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.51/2.50  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.51/2.50  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 7.51/2.50  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.51/2.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.51/2.50  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 7.51/2.50  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.51/2.50  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.51/2.50  tff(f_183, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.51/2.50  tff(f_101, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.51/2.50  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.51/2.50  tff(c_76, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_383, plain, (![C_277, A_278, B_279]: (v1_relat_1(C_277) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.51/2.50  tff(c_390, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_383])).
% 7.51/2.50  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.51/2.50  tff(c_10, plain, (![A_4, B_5]: (r1_xboole_0(A_4, B_5) | k4_xboole_0(A_4, B_5)!=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.50  tff(c_85, plain, (![A_226, B_227]: (k3_xboole_0(A_226, B_227)=k1_xboole_0 | ~r1_xboole_0(A_226, B_227))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.51/2.50  tff(c_397, plain, (![A_280, B_281]: (k3_xboole_0(A_280, B_281)=k1_xboole_0 | k4_xboole_0(A_280, B_281)!=A_280)), inference(resolution, [status(thm)], [c_10, c_85])).
% 7.51/2.50  tff(c_401, plain, (![A_3]: (k3_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_397])).
% 7.51/2.50  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.51/2.50  tff(c_453, plain, (![A_291, B_292]: (k7_relat_1(A_291, B_292)=k1_xboole_0 | ~r1_xboole_0(B_292, k1_relat_1(A_291)) | ~v1_relat_1(A_291))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.51/2.50  tff(c_1222, plain, (![A_387, A_388]: (k7_relat_1(A_387, A_388)=k1_xboole_0 | ~v1_relat_1(A_387) | k3_xboole_0(A_388, k1_relat_1(A_387))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_453])).
% 7.51/2.50  tff(c_1238, plain, (![A_389]: (k7_relat_1(A_389, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_389))), inference(superposition, [status(thm), theory('equality')], [c_401, c_1222])).
% 7.51/2.50  tff(c_1246, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_390, c_1238])).
% 7.51/2.50  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_64, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_473, plain, (![A_295, B_296]: (r1_xboole_0(A_295, B_296) | ~r1_subset_1(A_295, B_296) | v1_xboole_0(B_296) | v1_xboole_0(A_295))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.51/2.50  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=A_4 | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.51/2.50  tff(c_2847, plain, (![A_665, B_666]: (k4_xboole_0(A_665, B_666)=A_665 | ~r1_subset_1(A_665, B_666) | v1_xboole_0(B_666) | v1_xboole_0(A_665))), inference(resolution, [status(thm)], [c_473, c_8])).
% 7.51/2.50  tff(c_2853, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2847])).
% 7.51/2.50  tff(c_2857, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_2853])).
% 7.51/2.50  tff(c_89, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=k1_xboole_0 | k4_xboole_0(A_4, B_5)!=A_4)), inference(resolution, [status(thm)], [c_10, c_85])).
% 7.51/2.50  tff(c_2871, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2857, c_89])).
% 7.51/2.50  tff(c_492, plain, (![A_298, B_299, C_300]: (k9_subset_1(A_298, B_299, C_300)=k3_xboole_0(B_299, C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(A_298)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.51/2.50  tff(c_503, plain, (![B_299]: (k9_subset_1('#skF_1', B_299, '#skF_4')=k3_xboole_0(B_299, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_492])).
% 7.51/2.50  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_391, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_383])).
% 7.51/2.50  tff(c_1245, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_391, c_1238])).
% 7.51/2.50  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_2947, plain, (![E_676, D_675, C_673, B_674, F_678, A_677]: (v1_funct_1(k1_tmap_1(A_677, B_674, C_673, D_675, E_676, F_678)) | ~m1_subset_1(F_678, k1_zfmisc_1(k2_zfmisc_1(D_675, B_674))) | ~v1_funct_2(F_678, D_675, B_674) | ~v1_funct_1(F_678) | ~m1_subset_1(E_676, k1_zfmisc_1(k2_zfmisc_1(C_673, B_674))) | ~v1_funct_2(E_676, C_673, B_674) | ~v1_funct_1(E_676) | ~m1_subset_1(D_675, k1_zfmisc_1(A_677)) | v1_xboole_0(D_675) | ~m1_subset_1(C_673, k1_zfmisc_1(A_677)) | v1_xboole_0(C_673) | v1_xboole_0(B_674) | v1_xboole_0(A_677))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.51/2.50  tff(c_2949, plain, (![A_677, C_673, E_676]: (v1_funct_1(k1_tmap_1(A_677, '#skF_2', C_673, '#skF_4', E_676, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_676, k1_zfmisc_1(k2_zfmisc_1(C_673, '#skF_2'))) | ~v1_funct_2(E_676, C_673, '#skF_2') | ~v1_funct_1(E_676) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_677)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_673, k1_zfmisc_1(A_677)) | v1_xboole_0(C_673) | v1_xboole_0('#skF_2') | v1_xboole_0(A_677))), inference(resolution, [status(thm)], [c_52, c_2947])).
% 7.51/2.50  tff(c_2954, plain, (![A_677, C_673, E_676]: (v1_funct_1(k1_tmap_1(A_677, '#skF_2', C_673, '#skF_4', E_676, '#skF_6')) | ~m1_subset_1(E_676, k1_zfmisc_1(k2_zfmisc_1(C_673, '#skF_2'))) | ~v1_funct_2(E_676, C_673, '#skF_2') | ~v1_funct_1(E_676) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_677)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_673, k1_zfmisc_1(A_677)) | v1_xboole_0(C_673) | v1_xboole_0('#skF_2') | v1_xboole_0(A_677))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2949])).
% 7.51/2.50  tff(c_2960, plain, (![A_679, C_680, E_681]: (v1_funct_1(k1_tmap_1(A_679, '#skF_2', C_680, '#skF_4', E_681, '#skF_6')) | ~m1_subset_1(E_681, k1_zfmisc_1(k2_zfmisc_1(C_680, '#skF_2'))) | ~v1_funct_2(E_681, C_680, '#skF_2') | ~v1_funct_1(E_681) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_679)) | ~m1_subset_1(C_680, k1_zfmisc_1(A_679)) | v1_xboole_0(C_680) | v1_xboole_0(A_679))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2954])).
% 7.51/2.50  tff(c_2964, plain, (![A_679]: (v1_funct_1(k1_tmap_1(A_679, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_679)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_679)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_679))), inference(resolution, [status(thm)], [c_58, c_2960])).
% 7.51/2.50  tff(c_2971, plain, (![A_679]: (v1_funct_1(k1_tmap_1(A_679, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_679)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_679)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_679))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2964])).
% 7.51/2.50  tff(c_2981, plain, (![A_689]: (v1_funct_1(k1_tmap_1(A_689, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_689)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_689)) | v1_xboole_0(A_689))), inference(negUnitSimplification, [status(thm)], [c_72, c_2971])).
% 7.51/2.50  tff(c_2984, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_2981])).
% 7.51/2.50  tff(c_2987, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2984])).
% 7.51/2.50  tff(c_2988, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_2987])).
% 7.51/2.50  tff(c_1102, plain, (![A_371, B_372, C_373, D_374]: (k2_partfun1(A_371, B_372, C_373, D_374)=k7_relat_1(C_373, D_374) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))) | ~v1_funct_1(C_373))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.51/2.50  tff(c_1106, plain, (![D_374]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_374)=k7_relat_1('#skF_5', D_374) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_1102])).
% 7.51/2.50  tff(c_1112, plain, (![D_374]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_374)=k7_relat_1('#skF_5', D_374))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1106])).
% 7.51/2.50  tff(c_1104, plain, (![D_374]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_374)=k7_relat_1('#skF_6', D_374) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_1102])).
% 7.51/2.50  tff(c_1109, plain, (![D_374]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_374)=k7_relat_1('#skF_6', D_374))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1104])).
% 7.51/2.50  tff(c_46, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.51/2.50  tff(c_44, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.51/2.50  tff(c_3144, plain, (![A_715, D_720, B_717, C_719, F_718, E_716]: (k2_partfun1(k4_subset_1(A_715, C_719, D_720), B_717, k1_tmap_1(A_715, B_717, C_719, D_720, E_716, F_718), C_719)=E_716 | ~m1_subset_1(k1_tmap_1(A_715, B_717, C_719, D_720, E_716, F_718), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_715, C_719, D_720), B_717))) | ~v1_funct_2(k1_tmap_1(A_715, B_717, C_719, D_720, E_716, F_718), k4_subset_1(A_715, C_719, D_720), B_717) | ~v1_funct_1(k1_tmap_1(A_715, B_717, C_719, D_720, E_716, F_718)) | k2_partfun1(D_720, B_717, F_718, k9_subset_1(A_715, C_719, D_720))!=k2_partfun1(C_719, B_717, E_716, k9_subset_1(A_715, C_719, D_720)) | ~m1_subset_1(F_718, k1_zfmisc_1(k2_zfmisc_1(D_720, B_717))) | ~v1_funct_2(F_718, D_720, B_717) | ~v1_funct_1(F_718) | ~m1_subset_1(E_716, k1_zfmisc_1(k2_zfmisc_1(C_719, B_717))) | ~v1_funct_2(E_716, C_719, B_717) | ~v1_funct_1(E_716) | ~m1_subset_1(D_720, k1_zfmisc_1(A_715)) | v1_xboole_0(D_720) | ~m1_subset_1(C_719, k1_zfmisc_1(A_715)) | v1_xboole_0(C_719) | v1_xboole_0(B_717) | v1_xboole_0(A_715))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.51/2.50  tff(c_3796, plain, (![B_840, E_842, A_843, C_839, D_841, F_844]: (k2_partfun1(k4_subset_1(A_843, C_839, D_841), B_840, k1_tmap_1(A_843, B_840, C_839, D_841, E_842, F_844), C_839)=E_842 | ~v1_funct_2(k1_tmap_1(A_843, B_840, C_839, D_841, E_842, F_844), k4_subset_1(A_843, C_839, D_841), B_840) | ~v1_funct_1(k1_tmap_1(A_843, B_840, C_839, D_841, E_842, F_844)) | k2_partfun1(D_841, B_840, F_844, k9_subset_1(A_843, C_839, D_841))!=k2_partfun1(C_839, B_840, E_842, k9_subset_1(A_843, C_839, D_841)) | ~m1_subset_1(F_844, k1_zfmisc_1(k2_zfmisc_1(D_841, B_840))) | ~v1_funct_2(F_844, D_841, B_840) | ~v1_funct_1(F_844) | ~m1_subset_1(E_842, k1_zfmisc_1(k2_zfmisc_1(C_839, B_840))) | ~v1_funct_2(E_842, C_839, B_840) | ~v1_funct_1(E_842) | ~m1_subset_1(D_841, k1_zfmisc_1(A_843)) | v1_xboole_0(D_841) | ~m1_subset_1(C_839, k1_zfmisc_1(A_843)) | v1_xboole_0(C_839) | v1_xboole_0(B_840) | v1_xboole_0(A_843))), inference(resolution, [status(thm)], [c_44, c_3144])).
% 7.51/2.50  tff(c_3863, plain, (![D_869, F_872, B_868, C_867, E_870, A_871]: (k2_partfun1(k4_subset_1(A_871, C_867, D_869), B_868, k1_tmap_1(A_871, B_868, C_867, D_869, E_870, F_872), C_867)=E_870 | ~v1_funct_1(k1_tmap_1(A_871, B_868, C_867, D_869, E_870, F_872)) | k2_partfun1(D_869, B_868, F_872, k9_subset_1(A_871, C_867, D_869))!=k2_partfun1(C_867, B_868, E_870, k9_subset_1(A_871, C_867, D_869)) | ~m1_subset_1(F_872, k1_zfmisc_1(k2_zfmisc_1(D_869, B_868))) | ~v1_funct_2(F_872, D_869, B_868) | ~v1_funct_1(F_872) | ~m1_subset_1(E_870, k1_zfmisc_1(k2_zfmisc_1(C_867, B_868))) | ~v1_funct_2(E_870, C_867, B_868) | ~v1_funct_1(E_870) | ~m1_subset_1(D_869, k1_zfmisc_1(A_871)) | v1_xboole_0(D_869) | ~m1_subset_1(C_867, k1_zfmisc_1(A_871)) | v1_xboole_0(C_867) | v1_xboole_0(B_868) | v1_xboole_0(A_871))), inference(resolution, [status(thm)], [c_46, c_3796])).
% 7.51/2.50  tff(c_3867, plain, (![A_871, C_867, E_870]: (k2_partfun1(k4_subset_1(A_871, C_867, '#skF_4'), '#skF_2', k1_tmap_1(A_871, '#skF_2', C_867, '#skF_4', E_870, '#skF_6'), C_867)=E_870 | ~v1_funct_1(k1_tmap_1(A_871, '#skF_2', C_867, '#skF_4', E_870, '#skF_6')) | k2_partfun1(C_867, '#skF_2', E_870, k9_subset_1(A_871, C_867, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_871, C_867, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_870, k1_zfmisc_1(k2_zfmisc_1(C_867, '#skF_2'))) | ~v1_funct_2(E_870, C_867, '#skF_2') | ~v1_funct_1(E_870) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_871)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_867, k1_zfmisc_1(A_871)) | v1_xboole_0(C_867) | v1_xboole_0('#skF_2') | v1_xboole_0(A_871))), inference(resolution, [status(thm)], [c_52, c_3863])).
% 7.51/2.50  tff(c_3873, plain, (![A_871, C_867, E_870]: (k2_partfun1(k4_subset_1(A_871, C_867, '#skF_4'), '#skF_2', k1_tmap_1(A_871, '#skF_2', C_867, '#skF_4', E_870, '#skF_6'), C_867)=E_870 | ~v1_funct_1(k1_tmap_1(A_871, '#skF_2', C_867, '#skF_4', E_870, '#skF_6')) | k2_partfun1(C_867, '#skF_2', E_870, k9_subset_1(A_871, C_867, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_871, C_867, '#skF_4')) | ~m1_subset_1(E_870, k1_zfmisc_1(k2_zfmisc_1(C_867, '#skF_2'))) | ~v1_funct_2(E_870, C_867, '#skF_2') | ~v1_funct_1(E_870) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_871)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_867, k1_zfmisc_1(A_871)) | v1_xboole_0(C_867) | v1_xboole_0('#skF_2') | v1_xboole_0(A_871))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1109, c_3867])).
% 7.51/2.50  tff(c_3879, plain, (![A_873, C_874, E_875]: (k2_partfun1(k4_subset_1(A_873, C_874, '#skF_4'), '#skF_2', k1_tmap_1(A_873, '#skF_2', C_874, '#skF_4', E_875, '#skF_6'), C_874)=E_875 | ~v1_funct_1(k1_tmap_1(A_873, '#skF_2', C_874, '#skF_4', E_875, '#skF_6')) | k2_partfun1(C_874, '#skF_2', E_875, k9_subset_1(A_873, C_874, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_873, C_874, '#skF_4')) | ~m1_subset_1(E_875, k1_zfmisc_1(k2_zfmisc_1(C_874, '#skF_2'))) | ~v1_funct_2(E_875, C_874, '#skF_2') | ~v1_funct_1(E_875) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_873)) | ~m1_subset_1(C_874, k1_zfmisc_1(A_873)) | v1_xboole_0(C_874) | v1_xboole_0(A_873))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_3873])).
% 7.51/2.50  tff(c_3886, plain, (![A_873]: (k2_partfun1(k4_subset_1(A_873, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_873, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_873, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_873, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_873, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_873)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_873)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_873))), inference(resolution, [status(thm)], [c_58, c_3879])).
% 7.51/2.50  tff(c_3896, plain, (![A_873]: (k2_partfun1(k4_subset_1(A_873, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_873, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_873, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_873, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_873, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_873)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_873)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_873))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1112, c_3886])).
% 7.51/2.50  tff(c_3976, plain, (![A_892]: (k2_partfun1(k4_subset_1(A_892, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_892, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_892, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_892, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_892, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_892)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_892)) | v1_xboole_0(A_892))), inference(negUnitSimplification, [status(thm)], [c_72, c_3896])).
% 7.51/2.50  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.51/2.50  tff(c_1338, plain, (![A_394, B_395]: (k3_xboole_0(A_394, B_395)=k1_xboole_0 | ~r1_subset_1(A_394, B_395) | v1_xboole_0(B_395) | v1_xboole_0(A_394))), inference(resolution, [status(thm)], [c_473, c_2])).
% 7.51/2.50  tff(c_1347, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1338])).
% 7.51/2.50  tff(c_1352, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_1347])).
% 7.51/2.50  tff(c_1394, plain, (![C_398, B_399, F_403, D_400, A_402, E_401]: (v1_funct_1(k1_tmap_1(A_402, B_399, C_398, D_400, E_401, F_403)) | ~m1_subset_1(F_403, k1_zfmisc_1(k2_zfmisc_1(D_400, B_399))) | ~v1_funct_2(F_403, D_400, B_399) | ~v1_funct_1(F_403) | ~m1_subset_1(E_401, k1_zfmisc_1(k2_zfmisc_1(C_398, B_399))) | ~v1_funct_2(E_401, C_398, B_399) | ~v1_funct_1(E_401) | ~m1_subset_1(D_400, k1_zfmisc_1(A_402)) | v1_xboole_0(D_400) | ~m1_subset_1(C_398, k1_zfmisc_1(A_402)) | v1_xboole_0(C_398) | v1_xboole_0(B_399) | v1_xboole_0(A_402))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.51/2.50  tff(c_1396, plain, (![A_402, C_398, E_401]: (v1_funct_1(k1_tmap_1(A_402, '#skF_2', C_398, '#skF_4', E_401, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_401, k1_zfmisc_1(k2_zfmisc_1(C_398, '#skF_2'))) | ~v1_funct_2(E_401, C_398, '#skF_2') | ~v1_funct_1(E_401) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_402)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_398, k1_zfmisc_1(A_402)) | v1_xboole_0(C_398) | v1_xboole_0('#skF_2') | v1_xboole_0(A_402))), inference(resolution, [status(thm)], [c_52, c_1394])).
% 7.51/2.50  tff(c_1401, plain, (![A_402, C_398, E_401]: (v1_funct_1(k1_tmap_1(A_402, '#skF_2', C_398, '#skF_4', E_401, '#skF_6')) | ~m1_subset_1(E_401, k1_zfmisc_1(k2_zfmisc_1(C_398, '#skF_2'))) | ~v1_funct_2(E_401, C_398, '#skF_2') | ~v1_funct_1(E_401) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_402)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_398, k1_zfmisc_1(A_402)) | v1_xboole_0(C_398) | v1_xboole_0('#skF_2') | v1_xboole_0(A_402))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1396])).
% 7.51/2.50  tff(c_1459, plain, (![A_417, C_418, E_419]: (v1_funct_1(k1_tmap_1(A_417, '#skF_2', C_418, '#skF_4', E_419, '#skF_6')) | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(C_418, '#skF_2'))) | ~v1_funct_2(E_419, C_418, '#skF_2') | ~v1_funct_1(E_419) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_417)) | ~m1_subset_1(C_418, k1_zfmisc_1(A_417)) | v1_xboole_0(C_418) | v1_xboole_0(A_417))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_1401])).
% 7.51/2.50  tff(c_1463, plain, (![A_417]: (v1_funct_1(k1_tmap_1(A_417, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_417)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_417)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_417))), inference(resolution, [status(thm)], [c_58, c_1459])).
% 7.51/2.50  tff(c_1470, plain, (![A_417]: (v1_funct_1(k1_tmap_1(A_417, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_417)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_417)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_417))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1463])).
% 7.51/2.50  tff(c_1479, plain, (![A_421]: (v1_funct_1(k1_tmap_1(A_421, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_421)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_421)) | v1_xboole_0(A_421))), inference(negUnitSimplification, [status(thm)], [c_72, c_1470])).
% 7.51/2.50  tff(c_1482, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_1479])).
% 7.51/2.50  tff(c_1485, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1482])).
% 7.51/2.50  tff(c_1486, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1485])).
% 7.51/2.50  tff(c_1629, plain, (![F_452, B_451, A_449, C_453, D_454, E_450]: (k2_partfun1(k4_subset_1(A_449, C_453, D_454), B_451, k1_tmap_1(A_449, B_451, C_453, D_454, E_450, F_452), D_454)=F_452 | ~m1_subset_1(k1_tmap_1(A_449, B_451, C_453, D_454, E_450, F_452), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_449, C_453, D_454), B_451))) | ~v1_funct_2(k1_tmap_1(A_449, B_451, C_453, D_454, E_450, F_452), k4_subset_1(A_449, C_453, D_454), B_451) | ~v1_funct_1(k1_tmap_1(A_449, B_451, C_453, D_454, E_450, F_452)) | k2_partfun1(D_454, B_451, F_452, k9_subset_1(A_449, C_453, D_454))!=k2_partfun1(C_453, B_451, E_450, k9_subset_1(A_449, C_453, D_454)) | ~m1_subset_1(F_452, k1_zfmisc_1(k2_zfmisc_1(D_454, B_451))) | ~v1_funct_2(F_452, D_454, B_451) | ~v1_funct_1(F_452) | ~m1_subset_1(E_450, k1_zfmisc_1(k2_zfmisc_1(C_453, B_451))) | ~v1_funct_2(E_450, C_453, B_451) | ~v1_funct_1(E_450) | ~m1_subset_1(D_454, k1_zfmisc_1(A_449)) | v1_xboole_0(D_454) | ~m1_subset_1(C_453, k1_zfmisc_1(A_449)) | v1_xboole_0(C_453) | v1_xboole_0(B_451) | v1_xboole_0(A_449))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.51/2.50  tff(c_2086, plain, (![E_569, F_571, C_566, D_568, A_570, B_567]: (k2_partfun1(k4_subset_1(A_570, C_566, D_568), B_567, k1_tmap_1(A_570, B_567, C_566, D_568, E_569, F_571), D_568)=F_571 | ~v1_funct_2(k1_tmap_1(A_570, B_567, C_566, D_568, E_569, F_571), k4_subset_1(A_570, C_566, D_568), B_567) | ~v1_funct_1(k1_tmap_1(A_570, B_567, C_566, D_568, E_569, F_571)) | k2_partfun1(D_568, B_567, F_571, k9_subset_1(A_570, C_566, D_568))!=k2_partfun1(C_566, B_567, E_569, k9_subset_1(A_570, C_566, D_568)) | ~m1_subset_1(F_571, k1_zfmisc_1(k2_zfmisc_1(D_568, B_567))) | ~v1_funct_2(F_571, D_568, B_567) | ~v1_funct_1(F_571) | ~m1_subset_1(E_569, k1_zfmisc_1(k2_zfmisc_1(C_566, B_567))) | ~v1_funct_2(E_569, C_566, B_567) | ~v1_funct_1(E_569) | ~m1_subset_1(D_568, k1_zfmisc_1(A_570)) | v1_xboole_0(D_568) | ~m1_subset_1(C_566, k1_zfmisc_1(A_570)) | v1_xboole_0(C_566) | v1_xboole_0(B_567) | v1_xboole_0(A_570))), inference(resolution, [status(thm)], [c_44, c_1629])).
% 7.51/2.50  tff(c_2341, plain, (![F_614, C_609, D_611, B_610, A_613, E_612]: (k2_partfun1(k4_subset_1(A_613, C_609, D_611), B_610, k1_tmap_1(A_613, B_610, C_609, D_611, E_612, F_614), D_611)=F_614 | ~v1_funct_1(k1_tmap_1(A_613, B_610, C_609, D_611, E_612, F_614)) | k2_partfun1(D_611, B_610, F_614, k9_subset_1(A_613, C_609, D_611))!=k2_partfun1(C_609, B_610, E_612, k9_subset_1(A_613, C_609, D_611)) | ~m1_subset_1(F_614, k1_zfmisc_1(k2_zfmisc_1(D_611, B_610))) | ~v1_funct_2(F_614, D_611, B_610) | ~v1_funct_1(F_614) | ~m1_subset_1(E_612, k1_zfmisc_1(k2_zfmisc_1(C_609, B_610))) | ~v1_funct_2(E_612, C_609, B_610) | ~v1_funct_1(E_612) | ~m1_subset_1(D_611, k1_zfmisc_1(A_613)) | v1_xboole_0(D_611) | ~m1_subset_1(C_609, k1_zfmisc_1(A_613)) | v1_xboole_0(C_609) | v1_xboole_0(B_610) | v1_xboole_0(A_613))), inference(resolution, [status(thm)], [c_46, c_2086])).
% 7.51/2.50  tff(c_2345, plain, (![A_613, C_609, E_612]: (k2_partfun1(k4_subset_1(A_613, C_609, '#skF_4'), '#skF_2', k1_tmap_1(A_613, '#skF_2', C_609, '#skF_4', E_612, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_613, '#skF_2', C_609, '#skF_4', E_612, '#skF_6')) | k2_partfun1(C_609, '#skF_2', E_612, k9_subset_1(A_613, C_609, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_613, C_609, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_612, k1_zfmisc_1(k2_zfmisc_1(C_609, '#skF_2'))) | ~v1_funct_2(E_612, C_609, '#skF_2') | ~v1_funct_1(E_612) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_613)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_609, k1_zfmisc_1(A_613)) | v1_xboole_0(C_609) | v1_xboole_0('#skF_2') | v1_xboole_0(A_613))), inference(resolution, [status(thm)], [c_52, c_2341])).
% 7.51/2.50  tff(c_2351, plain, (![A_613, C_609, E_612]: (k2_partfun1(k4_subset_1(A_613, C_609, '#skF_4'), '#skF_2', k1_tmap_1(A_613, '#skF_2', C_609, '#skF_4', E_612, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_613, '#skF_2', C_609, '#skF_4', E_612, '#skF_6')) | k2_partfun1(C_609, '#skF_2', E_612, k9_subset_1(A_613, C_609, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_613, C_609, '#skF_4')) | ~m1_subset_1(E_612, k1_zfmisc_1(k2_zfmisc_1(C_609, '#skF_2'))) | ~v1_funct_2(E_612, C_609, '#skF_2') | ~v1_funct_1(E_612) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_613)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_609, k1_zfmisc_1(A_613)) | v1_xboole_0(C_609) | v1_xboole_0('#skF_2') | v1_xboole_0(A_613))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1109, c_2345])).
% 7.51/2.50  tff(c_2716, plain, (![A_658, C_659, E_660]: (k2_partfun1(k4_subset_1(A_658, C_659, '#skF_4'), '#skF_2', k1_tmap_1(A_658, '#skF_2', C_659, '#skF_4', E_660, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_658, '#skF_2', C_659, '#skF_4', E_660, '#skF_6')) | k2_partfun1(C_659, '#skF_2', E_660, k9_subset_1(A_658, C_659, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_658, C_659, '#skF_4')) | ~m1_subset_1(E_660, k1_zfmisc_1(k2_zfmisc_1(C_659, '#skF_2'))) | ~v1_funct_2(E_660, C_659, '#skF_2') | ~v1_funct_1(E_660) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_658)) | ~m1_subset_1(C_659, k1_zfmisc_1(A_658)) | v1_xboole_0(C_659) | v1_xboole_0(A_658))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2351])).
% 7.51/2.50  tff(c_2723, plain, (![A_658]: (k2_partfun1(k4_subset_1(A_658, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_658, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_658, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_658, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_658, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_658)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_658)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_658))), inference(resolution, [status(thm)], [c_58, c_2716])).
% 7.51/2.50  tff(c_2733, plain, (![A_658]: (k2_partfun1(k4_subset_1(A_658, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_658, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_658, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_658, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_658, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_658)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_658)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_658))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1112, c_2723])).
% 7.51/2.50  tff(c_2751, plain, (![A_662]: (k2_partfun1(k4_subset_1(A_662, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_662, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_662, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_662, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_662, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_662)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_662)) | v1_xboole_0(A_662))), inference(negUnitSimplification, [status(thm)], [c_72, c_2733])).
% 7.51/2.50  tff(c_126, plain, (![C_234, A_235, B_236]: (v1_relat_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.51/2.50  tff(c_133, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_126])).
% 7.51/2.50  tff(c_144, plain, (![A_240, B_241]: (k3_xboole_0(A_240, B_241)=k1_xboole_0 | k4_xboole_0(A_240, B_241)!=A_240)), inference(resolution, [status(thm)], [c_10, c_85])).
% 7.51/2.50  tff(c_148, plain, (![A_3]: (k3_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_144])).
% 7.51/2.50  tff(c_201, plain, (![A_251, B_252]: (k7_relat_1(A_251, B_252)=k1_xboole_0 | ~r1_xboole_0(B_252, k1_relat_1(A_251)) | ~v1_relat_1(A_251))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.51/2.50  tff(c_296, plain, (![A_266, A_267]: (k7_relat_1(A_266, A_267)=k1_xboole_0 | ~v1_relat_1(A_266) | k3_xboole_0(A_267, k1_relat_1(A_266))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_201])).
% 7.51/2.50  tff(c_302, plain, (![A_268]: (k7_relat_1(A_268, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_268))), inference(superposition, [status(thm), theory('equality')], [c_148, c_296])).
% 7.51/2.50  tff(c_310, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_133, c_302])).
% 7.51/2.50  tff(c_134, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_126])).
% 7.51/2.50  tff(c_309, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_134, c_302])).
% 7.51/2.50  tff(c_212, plain, (![A_253, B_254]: (r1_xboole_0(A_253, B_254) | ~r1_subset_1(A_253, B_254) | v1_xboole_0(B_254) | v1_xboole_0(A_253))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.51/2.50  tff(c_349, plain, (![A_275, B_276]: (k4_xboole_0(A_275, B_276)=A_275 | ~r1_subset_1(A_275, B_276) | v1_xboole_0(B_276) | v1_xboole_0(A_275))), inference(resolution, [status(thm)], [c_212, c_8])).
% 7.51/2.50  tff(c_355, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_349])).
% 7.51/2.50  tff(c_359, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_355])).
% 7.51/2.50  tff(c_373, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_359, c_89])).
% 7.51/2.50  tff(c_315, plain, (![A_269, B_270, C_271, D_272]: (k2_partfun1(A_269, B_270, C_271, D_272)=k7_relat_1(C_271, D_272) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~v1_funct_1(C_271))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.51/2.50  tff(c_317, plain, (![D_272]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_272)=k7_relat_1('#skF_6', D_272) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_315])).
% 7.51/2.50  tff(c_322, plain, (![D_272]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_272)=k7_relat_1('#skF_6', D_272))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_317])).
% 7.51/2.50  tff(c_319, plain, (![D_272]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_272)=k7_relat_1('#skF_5', D_272) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_315])).
% 7.51/2.50  tff(c_325, plain, (![D_272]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_272)=k7_relat_1('#skF_5', D_272))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_319])).
% 7.51/2.50  tff(c_230, plain, (![A_255, B_256, C_257]: (k9_subset_1(A_255, B_256, C_257)=k3_xboole_0(B_256, C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(A_255)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.51/2.50  tff(c_241, plain, (![B_256]: (k9_subset_1('#skF_1', B_256, '#skF_4')=k3_xboole_0(B_256, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_230])).
% 7.51/2.50  tff(c_50, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.51/2.50  tff(c_123, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 7.51/2.50  tff(c_243, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_241, c_123])).
% 7.51/2.50  tff(c_348, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_325, c_243])).
% 7.51/2.50  tff(c_376, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_373, c_373, c_348])).
% 7.51/2.50  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_310, c_309, c_376])).
% 7.51/2.50  tff(c_380, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 7.51/2.50  tff(c_1275, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_380])).
% 7.51/2.50  tff(c_2762, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2751, c_1275])).
% 7.51/2.50  tff(c_2776, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1246, c_1352, c_503, c_1245, c_1352, c_503, c_1486, c_2762])).
% 7.51/2.50  tff(c_2778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2776])).
% 7.51/2.50  tff(c_2779, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_380])).
% 7.51/2.50  tff(c_3985, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3976, c_2779])).
% 7.51/2.50  tff(c_3996, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1246, c_2871, c_503, c_1245, c_2871, c_503, c_2988, c_3985])).
% 7.51/2.50  tff(c_3998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3996])).
% 7.51/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.50  
% 7.51/2.50  Inference rules
% 7.51/2.50  ----------------------
% 7.51/2.50  #Ref     : 0
% 7.51/2.50  #Sup     : 802
% 7.51/2.50  #Fact    : 0
% 7.51/2.50  #Define  : 0
% 7.51/2.50  #Split   : 35
% 7.51/2.50  #Chain   : 0
% 7.51/2.50  #Close   : 0
% 7.51/2.50  
% 7.51/2.50  Ordering : KBO
% 7.51/2.50  
% 7.51/2.50  Simplification rules
% 7.51/2.50  ----------------------
% 7.51/2.50  #Subsume      : 81
% 7.51/2.50  #Demod        : 598
% 7.51/2.50  #Tautology    : 374
% 7.51/2.50  #SimpNegUnit  : 178
% 7.51/2.50  #BackRed      : 7
% 7.51/2.50  
% 7.51/2.50  #Partial instantiations: 0
% 7.51/2.50  #Strategies tried      : 1
% 7.51/2.50  
% 7.51/2.50  Timing (in seconds)
% 7.51/2.50  ----------------------
% 7.82/2.50  Preprocessing        : 0.42
% 7.82/2.50  Parsing              : 0.21
% 7.82/2.50  CNF conversion       : 0.06
% 7.82/2.50  Main loop            : 1.31
% 7.82/2.50  Inferencing          : 0.47
% 7.82/2.50  Reduction            : 0.41
% 7.82/2.50  Demodulation         : 0.29
% 7.82/2.50  BG Simplification    : 0.05
% 7.82/2.51  Subsumption          : 0.30
% 7.82/2.51  Abstraction          : 0.06
% 7.82/2.51  MUC search           : 0.00
% 7.82/2.51  Cooper               : 0.00
% 7.82/2.51  Total                : 1.78
% 7.82/2.51  Index Insertion      : 0.00
% 7.82/2.51  Index Deletion       : 0.00
% 7.82/2.51  Index Matching       : 0.00
% 7.82/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
