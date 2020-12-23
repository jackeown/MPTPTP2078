%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:14 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 504 expanded)
%              Number of leaves         :   41 ( 200 expanded)
%              Depth                    :   12
%              Number of atoms          :  582 (2612 expanded)
%              Number of equality atoms :   96 ( 480 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_211,negated_conjecture,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_169,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_135,axiom,(
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

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_540,plain,(
    ! [C_298,A_299,B_300] :
      ( v1_relat_1(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_553,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_540])).

tff(c_10,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_14,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_1'(A_5),k1_zfmisc_1(A_5))
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_554,plain,(
    ! [C_301,A_302,B_303] :
      ( v1_xboole_0(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303)))
      | ~ v1_xboole_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_669,plain,(
    ! [A_323,B_324] :
      ( v1_xboole_0('#skF_1'(k2_zfmisc_1(A_323,B_324)))
      | ~ v1_xboole_0(A_323)
      | v1_xboole_0(k2_zfmisc_1(A_323,B_324)) ) ),
    inference(resolution,[status(thm)],[c_14,c_554])).

tff(c_12,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0('#skF_1'(A_5))
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_678,plain,(
    ! [A_325,B_326] :
      ( ~ v1_xboole_0(A_325)
      | v1_xboole_0(k2_zfmisc_1(A_325,B_326)) ) ),
    inference(resolution,[status(thm)],[c_669,c_12])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_691,plain,(
    ! [A_327,B_328] :
      ( k2_zfmisc_1(A_327,B_328) = k1_xboole_0
      | ~ v1_xboole_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_678,c_8])).

tff(c_698,plain,(
    ! [B_329] : k2_zfmisc_1(k1_xboole_0,B_329) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_691])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k3_xboole_0(B_14,k2_zfmisc_1(A_13,k2_relat_1(B_14))) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_707,plain,(
    ! [B_14] :
      ( k7_relat_1(B_14,k1_xboole_0) = k3_xboole_0(B_14,k1_xboole_0)
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_20])).

tff(c_726,plain,(
    ! [B_330] :
      ( k7_relat_1(B_330,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_707])).

tff(c_737,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_553,c_726])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_58,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_578,plain,(
    ! [A_308,B_309] :
      ( r1_xboole_0(A_308,B_309)
      | ~ r1_subset_1(A_308,B_309)
      | v1_xboole_0(B_309)
      | v1_xboole_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_658,plain,(
    ! [A_321,B_322] :
      ( k3_xboole_0(A_321,B_322) = k1_xboole_0
      | ~ r1_subset_1(A_321,B_322)
      | v1_xboole_0(B_322)
      | v1_xboole_0(A_321) ) ),
    inference(resolution,[status(thm)],[c_578,c_2])).

tff(c_661,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_658])).

tff(c_664,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_661])).

tff(c_587,plain,(
    ! [A_310,B_311,C_312] :
      ( k9_subset_1(A_310,B_311,C_312) = k3_xboole_0(B_311,C_312)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(A_310)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_602,plain,(
    ! [B_311] : k9_subset_1('#skF_2',B_311,'#skF_5') = k3_xboole_0(B_311,'#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_587])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_552,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_540])).

tff(c_738,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_552,c_726])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_48,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_2649,plain,(
    ! [A_634,E_632,C_636,B_633,F_637,D_635] :
      ( v1_funct_1(k1_tmap_1(A_634,B_633,C_636,D_635,E_632,F_637))
      | ~ m1_subset_1(F_637,k1_zfmisc_1(k2_zfmisc_1(D_635,B_633)))
      | ~ v1_funct_2(F_637,D_635,B_633)
      | ~ v1_funct_1(F_637)
      | ~ m1_subset_1(E_632,k1_zfmisc_1(k2_zfmisc_1(C_636,B_633)))
      | ~ v1_funct_2(E_632,C_636,B_633)
      | ~ v1_funct_1(E_632)
      | ~ m1_subset_1(D_635,k1_zfmisc_1(A_634))
      | v1_xboole_0(D_635)
      | ~ m1_subset_1(C_636,k1_zfmisc_1(A_634))
      | v1_xboole_0(C_636)
      | v1_xboole_0(B_633)
      | v1_xboole_0(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2658,plain,(
    ! [A_634,C_636,E_632] :
      ( v1_funct_1(k1_tmap_1(A_634,'#skF_3',C_636,'#skF_5',E_632,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_632,k1_zfmisc_1(k2_zfmisc_1(C_636,'#skF_3')))
      | ~ v1_funct_2(E_632,C_636,'#skF_3')
      | ~ v1_funct_1(E_632)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_634))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_636,k1_zfmisc_1(A_634))
      | v1_xboole_0(C_636)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_634) ) ),
    inference(resolution,[status(thm)],[c_46,c_2649])).

tff(c_2665,plain,(
    ! [A_634,C_636,E_632] :
      ( v1_funct_1(k1_tmap_1(A_634,'#skF_3',C_636,'#skF_5',E_632,'#skF_7'))
      | ~ m1_subset_1(E_632,k1_zfmisc_1(k2_zfmisc_1(C_636,'#skF_3')))
      | ~ v1_funct_2(E_632,C_636,'#skF_3')
      | ~ v1_funct_1(E_632)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_634))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_636,k1_zfmisc_1(A_634))
      | v1_xboole_0(C_636)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_634) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2658])).

tff(c_2672,plain,(
    ! [A_638,C_639,E_640] :
      ( v1_funct_1(k1_tmap_1(A_638,'#skF_3',C_639,'#skF_5',E_640,'#skF_7'))
      | ~ m1_subset_1(E_640,k1_zfmisc_1(k2_zfmisc_1(C_639,'#skF_3')))
      | ~ v1_funct_2(E_640,C_639,'#skF_3')
      | ~ v1_funct_1(E_640)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_638))
      | ~ m1_subset_1(C_639,k1_zfmisc_1(A_638))
      | v1_xboole_0(C_639)
      | v1_xboole_0(A_638) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2665])).

tff(c_2685,plain,(
    ! [A_638] :
      ( v1_funct_1(k1_tmap_1(A_638,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_638))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_638))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_638) ) ),
    inference(resolution,[status(thm)],[c_52,c_2672])).

tff(c_2694,plain,(
    ! [A_638] :
      ( v1_funct_1(k1_tmap_1(A_638,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_638))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_638))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2685])).

tff(c_2704,plain,(
    ! [A_648] :
      ( v1_funct_1(k1_tmap_1(A_648,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_648))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_648))
      | v1_xboole_0(A_648) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2694])).

tff(c_2707,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2704])).

tff(c_2710,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2707])).

tff(c_2711,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2710])).

tff(c_739,plain,(
    ! [A_331,B_332,C_333,D_334] :
      ( k2_partfun1(A_331,B_332,C_333,D_334) = k7_relat_1(C_333,D_334)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | ~ v1_funct_1(C_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_748,plain,(
    ! [D_334] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_334) = k7_relat_1('#skF_6',D_334)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_739])).

tff(c_755,plain,(
    ! [D_334] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_334) = k7_relat_1('#skF_6',D_334) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_748])).

tff(c_746,plain,(
    ! [D_334] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_334) = k7_relat_1('#skF_7',D_334)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_739])).

tff(c_752,plain,(
    ! [D_334] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_334) = k7_relat_1('#skF_7',D_334) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_746])).

tff(c_40,plain,(
    ! [A_155,D_158,E_159,B_156,F_160,C_157] :
      ( v1_funct_2(k1_tmap_1(A_155,B_156,C_157,D_158,E_159,F_160),k4_subset_1(A_155,C_157,D_158),B_156)
      | ~ m1_subset_1(F_160,k1_zfmisc_1(k2_zfmisc_1(D_158,B_156)))
      | ~ v1_funct_2(F_160,D_158,B_156)
      | ~ v1_funct_1(F_160)
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(C_157,B_156)))
      | ~ v1_funct_2(E_159,C_157,B_156)
      | ~ v1_funct_1(E_159)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(A_155))
      | v1_xboole_0(D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(A_155))
      | v1_xboole_0(C_157)
      | v1_xboole_0(B_156)
      | v1_xboole_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_38,plain,(
    ! [A_155,D_158,E_159,B_156,F_160,C_157] :
      ( m1_subset_1(k1_tmap_1(A_155,B_156,C_157,D_158,E_159,F_160),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_155,C_157,D_158),B_156)))
      | ~ m1_subset_1(F_160,k1_zfmisc_1(k2_zfmisc_1(D_158,B_156)))
      | ~ v1_funct_2(F_160,D_158,B_156)
      | ~ v1_funct_1(F_160)
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(C_157,B_156)))
      | ~ v1_funct_2(E_159,C_157,B_156)
      | ~ v1_funct_1(E_159)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(A_155))
      | v1_xboole_0(D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(A_155))
      | v1_xboole_0(C_157)
      | v1_xboole_0(B_156)
      | v1_xboole_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2921,plain,(
    ! [D_680,A_678,E_683,C_682,B_679,F_681] :
      ( k2_partfun1(k4_subset_1(A_678,C_682,D_680),B_679,k1_tmap_1(A_678,B_679,C_682,D_680,E_683,F_681),C_682) = E_683
      | ~ m1_subset_1(k1_tmap_1(A_678,B_679,C_682,D_680,E_683,F_681),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_678,C_682,D_680),B_679)))
      | ~ v1_funct_2(k1_tmap_1(A_678,B_679,C_682,D_680,E_683,F_681),k4_subset_1(A_678,C_682,D_680),B_679)
      | ~ v1_funct_1(k1_tmap_1(A_678,B_679,C_682,D_680,E_683,F_681))
      | k2_partfun1(D_680,B_679,F_681,k9_subset_1(A_678,C_682,D_680)) != k2_partfun1(C_682,B_679,E_683,k9_subset_1(A_678,C_682,D_680))
      | ~ m1_subset_1(F_681,k1_zfmisc_1(k2_zfmisc_1(D_680,B_679)))
      | ~ v1_funct_2(F_681,D_680,B_679)
      | ~ v1_funct_1(F_681)
      | ~ m1_subset_1(E_683,k1_zfmisc_1(k2_zfmisc_1(C_682,B_679)))
      | ~ v1_funct_2(E_683,C_682,B_679)
      | ~ v1_funct_1(E_683)
      | ~ m1_subset_1(D_680,k1_zfmisc_1(A_678))
      | v1_xboole_0(D_680)
      | ~ m1_subset_1(C_682,k1_zfmisc_1(A_678))
      | v1_xboole_0(C_682)
      | v1_xboole_0(B_679)
      | v1_xboole_0(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3882,plain,(
    ! [B_821,D_823,F_825,C_824,A_822,E_820] :
      ( k2_partfun1(k4_subset_1(A_822,C_824,D_823),B_821,k1_tmap_1(A_822,B_821,C_824,D_823,E_820,F_825),C_824) = E_820
      | ~ v1_funct_2(k1_tmap_1(A_822,B_821,C_824,D_823,E_820,F_825),k4_subset_1(A_822,C_824,D_823),B_821)
      | ~ v1_funct_1(k1_tmap_1(A_822,B_821,C_824,D_823,E_820,F_825))
      | k2_partfun1(D_823,B_821,F_825,k9_subset_1(A_822,C_824,D_823)) != k2_partfun1(C_824,B_821,E_820,k9_subset_1(A_822,C_824,D_823))
      | ~ m1_subset_1(F_825,k1_zfmisc_1(k2_zfmisc_1(D_823,B_821)))
      | ~ v1_funct_2(F_825,D_823,B_821)
      | ~ v1_funct_1(F_825)
      | ~ m1_subset_1(E_820,k1_zfmisc_1(k2_zfmisc_1(C_824,B_821)))
      | ~ v1_funct_2(E_820,C_824,B_821)
      | ~ v1_funct_1(E_820)
      | ~ m1_subset_1(D_823,k1_zfmisc_1(A_822))
      | v1_xboole_0(D_823)
      | ~ m1_subset_1(C_824,k1_zfmisc_1(A_822))
      | v1_xboole_0(C_824)
      | v1_xboole_0(B_821)
      | v1_xboole_0(A_822) ) ),
    inference(resolution,[status(thm)],[c_38,c_2921])).

tff(c_4145,plain,(
    ! [D_871,B_869,E_868,C_872,A_870,F_873] :
      ( k2_partfun1(k4_subset_1(A_870,C_872,D_871),B_869,k1_tmap_1(A_870,B_869,C_872,D_871,E_868,F_873),C_872) = E_868
      | ~ v1_funct_1(k1_tmap_1(A_870,B_869,C_872,D_871,E_868,F_873))
      | k2_partfun1(D_871,B_869,F_873,k9_subset_1(A_870,C_872,D_871)) != k2_partfun1(C_872,B_869,E_868,k9_subset_1(A_870,C_872,D_871))
      | ~ m1_subset_1(F_873,k1_zfmisc_1(k2_zfmisc_1(D_871,B_869)))
      | ~ v1_funct_2(F_873,D_871,B_869)
      | ~ v1_funct_1(F_873)
      | ~ m1_subset_1(E_868,k1_zfmisc_1(k2_zfmisc_1(C_872,B_869)))
      | ~ v1_funct_2(E_868,C_872,B_869)
      | ~ v1_funct_1(E_868)
      | ~ m1_subset_1(D_871,k1_zfmisc_1(A_870))
      | v1_xboole_0(D_871)
      | ~ m1_subset_1(C_872,k1_zfmisc_1(A_870))
      | v1_xboole_0(C_872)
      | v1_xboole_0(B_869)
      | v1_xboole_0(A_870) ) ),
    inference(resolution,[status(thm)],[c_40,c_3882])).

tff(c_4162,plain,(
    ! [A_870,C_872,E_868] :
      ( k2_partfun1(k4_subset_1(A_870,C_872,'#skF_5'),'#skF_3',k1_tmap_1(A_870,'#skF_3',C_872,'#skF_5',E_868,'#skF_7'),C_872) = E_868
      | ~ v1_funct_1(k1_tmap_1(A_870,'#skF_3',C_872,'#skF_5',E_868,'#skF_7'))
      | k2_partfun1(C_872,'#skF_3',E_868,k9_subset_1(A_870,C_872,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_870,C_872,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_868,k1_zfmisc_1(k2_zfmisc_1(C_872,'#skF_3')))
      | ~ v1_funct_2(E_868,C_872,'#skF_3')
      | ~ v1_funct_1(E_868)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_870))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_872,k1_zfmisc_1(A_870))
      | v1_xboole_0(C_872)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_870) ) ),
    inference(resolution,[status(thm)],[c_46,c_4145])).

tff(c_4170,plain,(
    ! [A_870,C_872,E_868] :
      ( k2_partfun1(k4_subset_1(A_870,C_872,'#skF_5'),'#skF_3',k1_tmap_1(A_870,'#skF_3',C_872,'#skF_5',E_868,'#skF_7'),C_872) = E_868
      | ~ v1_funct_1(k1_tmap_1(A_870,'#skF_3',C_872,'#skF_5',E_868,'#skF_7'))
      | k2_partfun1(C_872,'#skF_3',E_868,k9_subset_1(A_870,C_872,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_870,C_872,'#skF_5'))
      | ~ m1_subset_1(E_868,k1_zfmisc_1(k2_zfmisc_1(C_872,'#skF_3')))
      | ~ v1_funct_2(E_868,C_872,'#skF_3')
      | ~ v1_funct_1(E_868)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_870))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_872,k1_zfmisc_1(A_870))
      | v1_xboole_0(C_872)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_870) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_752,c_4162])).

tff(c_4176,plain,(
    ! [A_874,C_875,E_876] :
      ( k2_partfun1(k4_subset_1(A_874,C_875,'#skF_5'),'#skF_3',k1_tmap_1(A_874,'#skF_3',C_875,'#skF_5',E_876,'#skF_7'),C_875) = E_876
      | ~ v1_funct_1(k1_tmap_1(A_874,'#skF_3',C_875,'#skF_5',E_876,'#skF_7'))
      | k2_partfun1(C_875,'#skF_3',E_876,k9_subset_1(A_874,C_875,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_874,C_875,'#skF_5'))
      | ~ m1_subset_1(E_876,k1_zfmisc_1(k2_zfmisc_1(C_875,'#skF_3')))
      | ~ v1_funct_2(E_876,C_875,'#skF_3')
      | ~ v1_funct_1(E_876)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_874))
      | ~ m1_subset_1(C_875,k1_zfmisc_1(A_874))
      | v1_xboole_0(C_875)
      | v1_xboole_0(A_874) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_4170])).

tff(c_4201,plain,(
    ! [A_874] :
      ( k2_partfun1(k4_subset_1(A_874,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_874,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_874,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_874,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_874,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_874))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_874))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_874) ) ),
    inference(resolution,[status(thm)],[c_52,c_4176])).

tff(c_4213,plain,(
    ! [A_874] :
      ( k2_partfun1(k4_subset_1(A_874,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_874,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_874,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_874,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_874,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_874))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_874))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_874) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_755,c_4201])).

tff(c_4249,plain,(
    ! [A_888] :
      ( k2_partfun1(k4_subset_1(A_888,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_888,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_888,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_888,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_888,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_888))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_888))
      | v1_xboole_0(A_888) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4213])).

tff(c_899,plain,(
    ! [E_357,C_361,F_362,A_359,B_358,D_360] :
      ( v1_funct_1(k1_tmap_1(A_359,B_358,C_361,D_360,E_357,F_362))
      | ~ m1_subset_1(F_362,k1_zfmisc_1(k2_zfmisc_1(D_360,B_358)))
      | ~ v1_funct_2(F_362,D_360,B_358)
      | ~ v1_funct_1(F_362)
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(C_361,B_358)))
      | ~ v1_funct_2(E_357,C_361,B_358)
      | ~ v1_funct_1(E_357)
      | ~ m1_subset_1(D_360,k1_zfmisc_1(A_359))
      | v1_xboole_0(D_360)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(A_359))
      | v1_xboole_0(C_361)
      | v1_xboole_0(B_358)
      | v1_xboole_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_908,plain,(
    ! [A_359,C_361,E_357] :
      ( v1_funct_1(k1_tmap_1(A_359,'#skF_3',C_361,'#skF_5',E_357,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(C_361,'#skF_3')))
      | ~ v1_funct_2(E_357,C_361,'#skF_3')
      | ~ v1_funct_1(E_357)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_359))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_361,k1_zfmisc_1(A_359))
      | v1_xboole_0(C_361)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_46,c_899])).

tff(c_915,plain,(
    ! [A_359,C_361,E_357] :
      ( v1_funct_1(k1_tmap_1(A_359,'#skF_3',C_361,'#skF_5',E_357,'#skF_7'))
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(C_361,'#skF_3')))
      | ~ v1_funct_2(E_357,C_361,'#skF_3')
      | ~ v1_funct_1(E_357)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_359))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_361,k1_zfmisc_1(A_359))
      | v1_xboole_0(C_361)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_908])).

tff(c_928,plain,(
    ! [A_366,C_367,E_368] :
      ( v1_funct_1(k1_tmap_1(A_366,'#skF_3',C_367,'#skF_5',E_368,'#skF_7'))
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(C_367,'#skF_3')))
      | ~ v1_funct_2(E_368,C_367,'#skF_3')
      | ~ v1_funct_1(E_368)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_366))
      | ~ m1_subset_1(C_367,k1_zfmisc_1(A_366))
      | v1_xboole_0(C_367)
      | v1_xboole_0(A_366) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_915])).

tff(c_941,plain,(
    ! [A_366] :
      ( v1_funct_1(k1_tmap_1(A_366,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_366))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_366))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_52,c_928])).

tff(c_950,plain,(
    ! [A_366] :
      ( v1_funct_1(k1_tmap_1(A_366,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_366))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_366))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_941])).

tff(c_959,plain,(
    ! [A_370] :
      ( v1_funct_1(k1_tmap_1(A_370,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_370))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_370))
      | v1_xboole_0(A_370) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_950])).

tff(c_962,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_959])).

tff(c_965,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_962])).

tff(c_966,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_965])).

tff(c_1192,plain,(
    ! [F_416,B_414,D_415,C_417,E_418,A_413] :
      ( k2_partfun1(k4_subset_1(A_413,C_417,D_415),B_414,k1_tmap_1(A_413,B_414,C_417,D_415,E_418,F_416),D_415) = F_416
      | ~ m1_subset_1(k1_tmap_1(A_413,B_414,C_417,D_415,E_418,F_416),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_413,C_417,D_415),B_414)))
      | ~ v1_funct_2(k1_tmap_1(A_413,B_414,C_417,D_415,E_418,F_416),k4_subset_1(A_413,C_417,D_415),B_414)
      | ~ v1_funct_1(k1_tmap_1(A_413,B_414,C_417,D_415,E_418,F_416))
      | k2_partfun1(D_415,B_414,F_416,k9_subset_1(A_413,C_417,D_415)) != k2_partfun1(C_417,B_414,E_418,k9_subset_1(A_413,C_417,D_415))
      | ~ m1_subset_1(F_416,k1_zfmisc_1(k2_zfmisc_1(D_415,B_414)))
      | ~ v1_funct_2(F_416,D_415,B_414)
      | ~ v1_funct_1(F_416)
      | ~ m1_subset_1(E_418,k1_zfmisc_1(k2_zfmisc_1(C_417,B_414)))
      | ~ v1_funct_2(E_418,C_417,B_414)
      | ~ v1_funct_1(E_418)
      | ~ m1_subset_1(D_415,k1_zfmisc_1(A_413))
      | v1_xboole_0(D_415)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(A_413))
      | v1_xboole_0(C_417)
      | v1_xboole_0(B_414)
      | v1_xboole_0(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2192,plain,(
    ! [A_562,F_565,D_563,E_560,C_564,B_561] :
      ( k2_partfun1(k4_subset_1(A_562,C_564,D_563),B_561,k1_tmap_1(A_562,B_561,C_564,D_563,E_560,F_565),D_563) = F_565
      | ~ v1_funct_2(k1_tmap_1(A_562,B_561,C_564,D_563,E_560,F_565),k4_subset_1(A_562,C_564,D_563),B_561)
      | ~ v1_funct_1(k1_tmap_1(A_562,B_561,C_564,D_563,E_560,F_565))
      | k2_partfun1(D_563,B_561,F_565,k9_subset_1(A_562,C_564,D_563)) != k2_partfun1(C_564,B_561,E_560,k9_subset_1(A_562,C_564,D_563))
      | ~ m1_subset_1(F_565,k1_zfmisc_1(k2_zfmisc_1(D_563,B_561)))
      | ~ v1_funct_2(F_565,D_563,B_561)
      | ~ v1_funct_1(F_565)
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(C_564,B_561)))
      | ~ v1_funct_2(E_560,C_564,B_561)
      | ~ v1_funct_1(E_560)
      | ~ m1_subset_1(D_563,k1_zfmisc_1(A_562))
      | v1_xboole_0(D_563)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(A_562))
      | v1_xboole_0(C_564)
      | v1_xboole_0(B_561)
      | v1_xboole_0(A_562) ) ),
    inference(resolution,[status(thm)],[c_38,c_1192])).

tff(c_2375,plain,(
    ! [C_594,A_592,E_590,D_593,F_595,B_591] :
      ( k2_partfun1(k4_subset_1(A_592,C_594,D_593),B_591,k1_tmap_1(A_592,B_591,C_594,D_593,E_590,F_595),D_593) = F_595
      | ~ v1_funct_1(k1_tmap_1(A_592,B_591,C_594,D_593,E_590,F_595))
      | k2_partfun1(D_593,B_591,F_595,k9_subset_1(A_592,C_594,D_593)) != k2_partfun1(C_594,B_591,E_590,k9_subset_1(A_592,C_594,D_593))
      | ~ m1_subset_1(F_595,k1_zfmisc_1(k2_zfmisc_1(D_593,B_591)))
      | ~ v1_funct_2(F_595,D_593,B_591)
      | ~ v1_funct_1(F_595)
      | ~ m1_subset_1(E_590,k1_zfmisc_1(k2_zfmisc_1(C_594,B_591)))
      | ~ v1_funct_2(E_590,C_594,B_591)
      | ~ v1_funct_1(E_590)
      | ~ m1_subset_1(D_593,k1_zfmisc_1(A_592))
      | v1_xboole_0(D_593)
      | ~ m1_subset_1(C_594,k1_zfmisc_1(A_592))
      | v1_xboole_0(C_594)
      | v1_xboole_0(B_591)
      | v1_xboole_0(A_592) ) ),
    inference(resolution,[status(thm)],[c_40,c_2192])).

tff(c_2392,plain,(
    ! [A_592,C_594,E_590] :
      ( k2_partfun1(k4_subset_1(A_592,C_594,'#skF_5'),'#skF_3',k1_tmap_1(A_592,'#skF_3',C_594,'#skF_5',E_590,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_592,'#skF_3',C_594,'#skF_5',E_590,'#skF_7'))
      | k2_partfun1(C_594,'#skF_3',E_590,k9_subset_1(A_592,C_594,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_592,C_594,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_590,k1_zfmisc_1(k2_zfmisc_1(C_594,'#skF_3')))
      | ~ v1_funct_2(E_590,C_594,'#skF_3')
      | ~ v1_funct_1(E_590)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_592))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_594,k1_zfmisc_1(A_592))
      | v1_xboole_0(C_594)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_592) ) ),
    inference(resolution,[status(thm)],[c_46,c_2375])).

tff(c_2400,plain,(
    ! [A_592,C_594,E_590] :
      ( k2_partfun1(k4_subset_1(A_592,C_594,'#skF_5'),'#skF_3',k1_tmap_1(A_592,'#skF_3',C_594,'#skF_5',E_590,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_592,'#skF_3',C_594,'#skF_5',E_590,'#skF_7'))
      | k2_partfun1(C_594,'#skF_3',E_590,k9_subset_1(A_592,C_594,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_592,C_594,'#skF_5'))
      | ~ m1_subset_1(E_590,k1_zfmisc_1(k2_zfmisc_1(C_594,'#skF_3')))
      | ~ v1_funct_2(E_590,C_594,'#skF_3')
      | ~ v1_funct_1(E_590)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_592))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_594,k1_zfmisc_1(A_592))
      | v1_xboole_0(C_594)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_592) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_752,c_2392])).

tff(c_2410,plain,(
    ! [A_602,C_603,E_604] :
      ( k2_partfun1(k4_subset_1(A_602,C_603,'#skF_5'),'#skF_3',k1_tmap_1(A_602,'#skF_3',C_603,'#skF_5',E_604,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_602,'#skF_3',C_603,'#skF_5',E_604,'#skF_7'))
      | k2_partfun1(C_603,'#skF_3',E_604,k9_subset_1(A_602,C_603,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_602,C_603,'#skF_5'))
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(C_603,'#skF_3')))
      | ~ v1_funct_2(E_604,C_603,'#skF_3')
      | ~ v1_funct_1(E_604)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_602))
      | ~ m1_subset_1(C_603,k1_zfmisc_1(A_602))
      | v1_xboole_0(C_603)
      | v1_xboole_0(A_602) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2400])).

tff(c_2435,plain,(
    ! [A_602] :
      ( k2_partfun1(k4_subset_1(A_602,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_602,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_602,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_602,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_602,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_602))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_602))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_602) ) ),
    inference(resolution,[status(thm)],[c_52,c_2410])).

tff(c_2447,plain,(
    ! [A_602] :
      ( k2_partfun1(k4_subset_1(A_602,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_602,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_602,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_602,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_602,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_602))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_602))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_602) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_755,c_2435])).

tff(c_2482,plain,(
    ! [A_607] :
      ( k2_partfun1(k4_subset_1(A_607,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_607,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_607,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_607,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_607,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_607))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_607))
      | v1_xboole_0(A_607) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2447])).

tff(c_118,plain,(
    ! [C_228,A_229,B_230] :
      ( v1_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_131,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_138,plain,(
    ! [C_235,A_236,B_237] :
      ( v1_xboole_0(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ v1_xboole_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_223,plain,(
    ! [A_249,B_250] :
      ( v1_xboole_0('#skF_1'(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_xboole_0(A_249)
      | v1_xboole_0(k2_zfmisc_1(A_249,B_250)) ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_232,plain,(
    ! [A_251,B_252] :
      ( ~ v1_xboole_0(A_251)
      | v1_xboole_0(k2_zfmisc_1(A_251,B_252)) ) ),
    inference(resolution,[status(thm)],[c_223,c_12])).

tff(c_245,plain,(
    ! [A_253,B_254] :
      ( k2_zfmisc_1(A_253,B_254) = k1_xboole_0
      | ~ v1_xboole_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_232,c_8])).

tff(c_252,plain,(
    ! [B_255] : k2_zfmisc_1(k1_xboole_0,B_255) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_245])).

tff(c_261,plain,(
    ! [B_14] :
      ( k7_relat_1(B_14,k1_xboole_0) = k3_xboole_0(B_14,k1_xboole_0)
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_20])).

tff(c_280,plain,(
    ! [B_256] :
      ( k7_relat_1(B_256,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_261])).

tff(c_291,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_131,c_280])).

tff(c_152,plain,(
    ! [A_238,B_239] :
      ( r1_xboole_0(A_238,B_239)
      | ~ r1_subset_1(A_238,B_239)
      | v1_xboole_0(B_239)
      | v1_xboole_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_431,plain,(
    ! [A_279,B_280] :
      ( k3_xboole_0(A_279,B_280) = k1_xboole_0
      | ~ r1_subset_1(A_279,B_280)
      | v1_xboole_0(B_280)
      | v1_xboole_0(A_279) ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_437,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_431])).

tff(c_441,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_437])).

tff(c_130,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_118])).

tff(c_292,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_280])).

tff(c_293,plain,(
    ! [A_257,B_258,C_259,D_260] :
      ( k2_partfun1(A_257,B_258,C_259,D_260) = k7_relat_1(C_259,D_260)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ v1_funct_1(C_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_302,plain,(
    ! [D_260] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_260) = k7_relat_1('#skF_6',D_260)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_293])).

tff(c_309,plain,(
    ! [D_260] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_260) = k7_relat_1('#skF_6',D_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_302])).

tff(c_300,plain,(
    ! [D_260] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_260) = k7_relat_1('#skF_7',D_260)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_293])).

tff(c_306,plain,(
    ! [D_260] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_260) = k7_relat_1('#skF_7',D_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_300])).

tff(c_170,plain,(
    ! [A_242,B_243,C_244] :
      ( k9_subset_1(A_242,B_243,C_244) = k3_xboole_0(B_243,C_244)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_185,plain,(
    ! [B_243] : k9_subset_1('#skF_2',B_243,'#skF_5') = k3_xboole_0(B_243,'#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_170])).

tff(c_44,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_87,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_195,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_87])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_441,c_292,c_441,c_309,c_306,c_195])).

tff(c_508,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_771,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_508])).

tff(c_2493,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2482,c_771])).

tff(c_2507,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_738,c_737,c_664,c_664,c_602,c_602,c_966,c_2493])).

tff(c_2509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2507])).

tff(c_2510,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_508])).

tff(c_4258,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4249,c_2510])).

tff(c_4269,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_737,c_664,c_602,c_738,c_664,c_602,c_2711,c_4258])).

tff(c_4271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:58:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/3.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.87/3.23  
% 8.87/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.87/3.23  %$ v1_funct_2 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 8.87/3.23  
% 8.87/3.23  %Foreground sorts:
% 8.87/3.23  
% 8.87/3.23  
% 8.87/3.23  %Background operators:
% 8.87/3.23  
% 8.87/3.23  
% 8.87/3.23  %Foreground operators:
% 8.87/3.23  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.87/3.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.87/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.87/3.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.87/3.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.87/3.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.87/3.23  tff('#skF_7', type, '#skF_7': $i).
% 8.87/3.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.87/3.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.87/3.23  tff('#skF_5', type, '#skF_5': $i).
% 8.87/3.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.87/3.23  tff('#skF_6', type, '#skF_6': $i).
% 8.87/3.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.87/3.23  tff('#skF_2', type, '#skF_2': $i).
% 8.87/3.23  tff('#skF_3', type, '#skF_3': $i).
% 8.87/3.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.87/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.87/3.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.87/3.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.87/3.23  tff('#skF_4', type, '#skF_4': $i).
% 8.87/3.23  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.87/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.87/3.23  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.87/3.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.87/3.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.87/3.23  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.87/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.87/3.23  
% 8.87/3.26  tff(f_211, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.87/3.26  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.87/3.26  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.87/3.26  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.87/3.26  tff(f_45, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_subset_1)).
% 8.87/3.26  tff(f_81, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 8.87/3.26  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.87/3.26  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 8.87/3.26  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.87/3.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.87/3.26  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.87/3.26  tff(f_169, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.87/3.26  tff(f_87, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.87/3.26  tff(f_135, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.87/3.26  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_540, plain, (![C_298, A_299, B_300]: (v1_relat_1(C_298) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.87/3.26  tff(c_553, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_540])).
% 8.87/3.26  tff(c_10, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.87/3.26  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.87/3.26  tff(c_14, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), k1_zfmisc_1(A_5)) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.87/3.26  tff(c_554, plain, (![C_301, A_302, B_303]: (v1_xboole_0(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))) | ~v1_xboole_0(A_302))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.87/3.26  tff(c_669, plain, (![A_323, B_324]: (v1_xboole_0('#skF_1'(k2_zfmisc_1(A_323, B_324))) | ~v1_xboole_0(A_323) | v1_xboole_0(k2_zfmisc_1(A_323, B_324)))), inference(resolution, [status(thm)], [c_14, c_554])).
% 8.87/3.26  tff(c_12, plain, (![A_5]: (~v1_xboole_0('#skF_1'(A_5)) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.87/3.26  tff(c_678, plain, (![A_325, B_326]: (~v1_xboole_0(A_325) | v1_xboole_0(k2_zfmisc_1(A_325, B_326)))), inference(resolution, [status(thm)], [c_669, c_12])).
% 8.87/3.26  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.87/3.26  tff(c_691, plain, (![A_327, B_328]: (k2_zfmisc_1(A_327, B_328)=k1_xboole_0 | ~v1_xboole_0(A_327))), inference(resolution, [status(thm)], [c_678, c_8])).
% 8.87/3.26  tff(c_698, plain, (![B_329]: (k2_zfmisc_1(k1_xboole_0, B_329)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_691])).
% 8.87/3.26  tff(c_20, plain, (![B_14, A_13]: (k3_xboole_0(B_14, k2_zfmisc_1(A_13, k2_relat_1(B_14)))=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.87/3.26  tff(c_707, plain, (![B_14]: (k7_relat_1(B_14, k1_xboole_0)=k3_xboole_0(B_14, k1_xboole_0) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_698, c_20])).
% 8.87/3.26  tff(c_726, plain, (![B_330]: (k7_relat_1(B_330, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_330))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_707])).
% 8.87/3.26  tff(c_737, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_553, c_726])).
% 8.87/3.26  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_62, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_58, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_578, plain, (![A_308, B_309]: (r1_xboole_0(A_308, B_309) | ~r1_subset_1(A_308, B_309) | v1_xboole_0(B_309) | v1_xboole_0(A_308))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.87/3.26  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.87/3.26  tff(c_658, plain, (![A_321, B_322]: (k3_xboole_0(A_321, B_322)=k1_xboole_0 | ~r1_subset_1(A_321, B_322) | v1_xboole_0(B_322) | v1_xboole_0(A_321))), inference(resolution, [status(thm)], [c_578, c_2])).
% 8.87/3.26  tff(c_661, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_658])).
% 8.87/3.26  tff(c_664, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_661])).
% 8.87/3.26  tff(c_587, plain, (![A_310, B_311, C_312]: (k9_subset_1(A_310, B_311, C_312)=k3_xboole_0(B_311, C_312) | ~m1_subset_1(C_312, k1_zfmisc_1(A_310)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.87/3.26  tff(c_602, plain, (![B_311]: (k9_subset_1('#skF_2', B_311, '#skF_5')=k3_xboole_0(B_311, '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_587])).
% 8.87/3.26  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_552, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_540])).
% 8.87/3.26  tff(c_738, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_552, c_726])).
% 8.87/3.26  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_48, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_2649, plain, (![A_634, E_632, C_636, B_633, F_637, D_635]: (v1_funct_1(k1_tmap_1(A_634, B_633, C_636, D_635, E_632, F_637)) | ~m1_subset_1(F_637, k1_zfmisc_1(k2_zfmisc_1(D_635, B_633))) | ~v1_funct_2(F_637, D_635, B_633) | ~v1_funct_1(F_637) | ~m1_subset_1(E_632, k1_zfmisc_1(k2_zfmisc_1(C_636, B_633))) | ~v1_funct_2(E_632, C_636, B_633) | ~v1_funct_1(E_632) | ~m1_subset_1(D_635, k1_zfmisc_1(A_634)) | v1_xboole_0(D_635) | ~m1_subset_1(C_636, k1_zfmisc_1(A_634)) | v1_xboole_0(C_636) | v1_xboole_0(B_633) | v1_xboole_0(A_634))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.87/3.26  tff(c_2658, plain, (![A_634, C_636, E_632]: (v1_funct_1(k1_tmap_1(A_634, '#skF_3', C_636, '#skF_5', E_632, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_632, k1_zfmisc_1(k2_zfmisc_1(C_636, '#skF_3'))) | ~v1_funct_2(E_632, C_636, '#skF_3') | ~v1_funct_1(E_632) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_634)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_636, k1_zfmisc_1(A_634)) | v1_xboole_0(C_636) | v1_xboole_0('#skF_3') | v1_xboole_0(A_634))), inference(resolution, [status(thm)], [c_46, c_2649])).
% 8.87/3.26  tff(c_2665, plain, (![A_634, C_636, E_632]: (v1_funct_1(k1_tmap_1(A_634, '#skF_3', C_636, '#skF_5', E_632, '#skF_7')) | ~m1_subset_1(E_632, k1_zfmisc_1(k2_zfmisc_1(C_636, '#skF_3'))) | ~v1_funct_2(E_632, C_636, '#skF_3') | ~v1_funct_1(E_632) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_634)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_636, k1_zfmisc_1(A_634)) | v1_xboole_0(C_636) | v1_xboole_0('#skF_3') | v1_xboole_0(A_634))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2658])).
% 8.87/3.26  tff(c_2672, plain, (![A_638, C_639, E_640]: (v1_funct_1(k1_tmap_1(A_638, '#skF_3', C_639, '#skF_5', E_640, '#skF_7')) | ~m1_subset_1(E_640, k1_zfmisc_1(k2_zfmisc_1(C_639, '#skF_3'))) | ~v1_funct_2(E_640, C_639, '#skF_3') | ~v1_funct_1(E_640) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_638)) | ~m1_subset_1(C_639, k1_zfmisc_1(A_638)) | v1_xboole_0(C_639) | v1_xboole_0(A_638))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2665])).
% 8.87/3.26  tff(c_2685, plain, (![A_638]: (v1_funct_1(k1_tmap_1(A_638, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_638)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_638)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_638))), inference(resolution, [status(thm)], [c_52, c_2672])).
% 8.87/3.26  tff(c_2694, plain, (![A_638]: (v1_funct_1(k1_tmap_1(A_638, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_638)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_638)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_638))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2685])).
% 8.87/3.26  tff(c_2704, plain, (![A_648]: (v1_funct_1(k1_tmap_1(A_648, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_648)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_648)) | v1_xboole_0(A_648))), inference(negUnitSimplification, [status(thm)], [c_66, c_2694])).
% 8.87/3.26  tff(c_2707, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_2704])).
% 8.87/3.26  tff(c_2710, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2707])).
% 8.87/3.26  tff(c_2711, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_2710])).
% 8.87/3.26  tff(c_739, plain, (![A_331, B_332, C_333, D_334]: (k2_partfun1(A_331, B_332, C_333, D_334)=k7_relat_1(C_333, D_334) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | ~v1_funct_1(C_333))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/3.26  tff(c_748, plain, (![D_334]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_334)=k7_relat_1('#skF_6', D_334) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_739])).
% 8.87/3.26  tff(c_755, plain, (![D_334]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_334)=k7_relat_1('#skF_6', D_334))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_748])).
% 8.87/3.26  tff(c_746, plain, (![D_334]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_334)=k7_relat_1('#skF_7', D_334) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_46, c_739])).
% 8.87/3.26  tff(c_752, plain, (![D_334]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_334)=k7_relat_1('#skF_7', D_334))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_746])).
% 8.87/3.26  tff(c_40, plain, (![A_155, D_158, E_159, B_156, F_160, C_157]: (v1_funct_2(k1_tmap_1(A_155, B_156, C_157, D_158, E_159, F_160), k4_subset_1(A_155, C_157, D_158), B_156) | ~m1_subset_1(F_160, k1_zfmisc_1(k2_zfmisc_1(D_158, B_156))) | ~v1_funct_2(F_160, D_158, B_156) | ~v1_funct_1(F_160) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(C_157, B_156))) | ~v1_funct_2(E_159, C_157, B_156) | ~v1_funct_1(E_159) | ~m1_subset_1(D_158, k1_zfmisc_1(A_155)) | v1_xboole_0(D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(A_155)) | v1_xboole_0(C_157) | v1_xboole_0(B_156) | v1_xboole_0(A_155))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.87/3.26  tff(c_38, plain, (![A_155, D_158, E_159, B_156, F_160, C_157]: (m1_subset_1(k1_tmap_1(A_155, B_156, C_157, D_158, E_159, F_160), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_155, C_157, D_158), B_156))) | ~m1_subset_1(F_160, k1_zfmisc_1(k2_zfmisc_1(D_158, B_156))) | ~v1_funct_2(F_160, D_158, B_156) | ~v1_funct_1(F_160) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(C_157, B_156))) | ~v1_funct_2(E_159, C_157, B_156) | ~v1_funct_1(E_159) | ~m1_subset_1(D_158, k1_zfmisc_1(A_155)) | v1_xboole_0(D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(A_155)) | v1_xboole_0(C_157) | v1_xboole_0(B_156) | v1_xboole_0(A_155))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.87/3.26  tff(c_2921, plain, (![D_680, A_678, E_683, C_682, B_679, F_681]: (k2_partfun1(k4_subset_1(A_678, C_682, D_680), B_679, k1_tmap_1(A_678, B_679, C_682, D_680, E_683, F_681), C_682)=E_683 | ~m1_subset_1(k1_tmap_1(A_678, B_679, C_682, D_680, E_683, F_681), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_678, C_682, D_680), B_679))) | ~v1_funct_2(k1_tmap_1(A_678, B_679, C_682, D_680, E_683, F_681), k4_subset_1(A_678, C_682, D_680), B_679) | ~v1_funct_1(k1_tmap_1(A_678, B_679, C_682, D_680, E_683, F_681)) | k2_partfun1(D_680, B_679, F_681, k9_subset_1(A_678, C_682, D_680))!=k2_partfun1(C_682, B_679, E_683, k9_subset_1(A_678, C_682, D_680)) | ~m1_subset_1(F_681, k1_zfmisc_1(k2_zfmisc_1(D_680, B_679))) | ~v1_funct_2(F_681, D_680, B_679) | ~v1_funct_1(F_681) | ~m1_subset_1(E_683, k1_zfmisc_1(k2_zfmisc_1(C_682, B_679))) | ~v1_funct_2(E_683, C_682, B_679) | ~v1_funct_1(E_683) | ~m1_subset_1(D_680, k1_zfmisc_1(A_678)) | v1_xboole_0(D_680) | ~m1_subset_1(C_682, k1_zfmisc_1(A_678)) | v1_xboole_0(C_682) | v1_xboole_0(B_679) | v1_xboole_0(A_678))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.87/3.26  tff(c_3882, plain, (![B_821, D_823, F_825, C_824, A_822, E_820]: (k2_partfun1(k4_subset_1(A_822, C_824, D_823), B_821, k1_tmap_1(A_822, B_821, C_824, D_823, E_820, F_825), C_824)=E_820 | ~v1_funct_2(k1_tmap_1(A_822, B_821, C_824, D_823, E_820, F_825), k4_subset_1(A_822, C_824, D_823), B_821) | ~v1_funct_1(k1_tmap_1(A_822, B_821, C_824, D_823, E_820, F_825)) | k2_partfun1(D_823, B_821, F_825, k9_subset_1(A_822, C_824, D_823))!=k2_partfun1(C_824, B_821, E_820, k9_subset_1(A_822, C_824, D_823)) | ~m1_subset_1(F_825, k1_zfmisc_1(k2_zfmisc_1(D_823, B_821))) | ~v1_funct_2(F_825, D_823, B_821) | ~v1_funct_1(F_825) | ~m1_subset_1(E_820, k1_zfmisc_1(k2_zfmisc_1(C_824, B_821))) | ~v1_funct_2(E_820, C_824, B_821) | ~v1_funct_1(E_820) | ~m1_subset_1(D_823, k1_zfmisc_1(A_822)) | v1_xboole_0(D_823) | ~m1_subset_1(C_824, k1_zfmisc_1(A_822)) | v1_xboole_0(C_824) | v1_xboole_0(B_821) | v1_xboole_0(A_822))), inference(resolution, [status(thm)], [c_38, c_2921])).
% 8.87/3.26  tff(c_4145, plain, (![D_871, B_869, E_868, C_872, A_870, F_873]: (k2_partfun1(k4_subset_1(A_870, C_872, D_871), B_869, k1_tmap_1(A_870, B_869, C_872, D_871, E_868, F_873), C_872)=E_868 | ~v1_funct_1(k1_tmap_1(A_870, B_869, C_872, D_871, E_868, F_873)) | k2_partfun1(D_871, B_869, F_873, k9_subset_1(A_870, C_872, D_871))!=k2_partfun1(C_872, B_869, E_868, k9_subset_1(A_870, C_872, D_871)) | ~m1_subset_1(F_873, k1_zfmisc_1(k2_zfmisc_1(D_871, B_869))) | ~v1_funct_2(F_873, D_871, B_869) | ~v1_funct_1(F_873) | ~m1_subset_1(E_868, k1_zfmisc_1(k2_zfmisc_1(C_872, B_869))) | ~v1_funct_2(E_868, C_872, B_869) | ~v1_funct_1(E_868) | ~m1_subset_1(D_871, k1_zfmisc_1(A_870)) | v1_xboole_0(D_871) | ~m1_subset_1(C_872, k1_zfmisc_1(A_870)) | v1_xboole_0(C_872) | v1_xboole_0(B_869) | v1_xboole_0(A_870))), inference(resolution, [status(thm)], [c_40, c_3882])).
% 8.87/3.26  tff(c_4162, plain, (![A_870, C_872, E_868]: (k2_partfun1(k4_subset_1(A_870, C_872, '#skF_5'), '#skF_3', k1_tmap_1(A_870, '#skF_3', C_872, '#skF_5', E_868, '#skF_7'), C_872)=E_868 | ~v1_funct_1(k1_tmap_1(A_870, '#skF_3', C_872, '#skF_5', E_868, '#skF_7')) | k2_partfun1(C_872, '#skF_3', E_868, k9_subset_1(A_870, C_872, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_870, C_872, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_868, k1_zfmisc_1(k2_zfmisc_1(C_872, '#skF_3'))) | ~v1_funct_2(E_868, C_872, '#skF_3') | ~v1_funct_1(E_868) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_870)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_872, k1_zfmisc_1(A_870)) | v1_xboole_0(C_872) | v1_xboole_0('#skF_3') | v1_xboole_0(A_870))), inference(resolution, [status(thm)], [c_46, c_4145])).
% 8.87/3.26  tff(c_4170, plain, (![A_870, C_872, E_868]: (k2_partfun1(k4_subset_1(A_870, C_872, '#skF_5'), '#skF_3', k1_tmap_1(A_870, '#skF_3', C_872, '#skF_5', E_868, '#skF_7'), C_872)=E_868 | ~v1_funct_1(k1_tmap_1(A_870, '#skF_3', C_872, '#skF_5', E_868, '#skF_7')) | k2_partfun1(C_872, '#skF_3', E_868, k9_subset_1(A_870, C_872, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_870, C_872, '#skF_5')) | ~m1_subset_1(E_868, k1_zfmisc_1(k2_zfmisc_1(C_872, '#skF_3'))) | ~v1_funct_2(E_868, C_872, '#skF_3') | ~v1_funct_1(E_868) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_870)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_872, k1_zfmisc_1(A_870)) | v1_xboole_0(C_872) | v1_xboole_0('#skF_3') | v1_xboole_0(A_870))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_752, c_4162])).
% 8.87/3.26  tff(c_4176, plain, (![A_874, C_875, E_876]: (k2_partfun1(k4_subset_1(A_874, C_875, '#skF_5'), '#skF_3', k1_tmap_1(A_874, '#skF_3', C_875, '#skF_5', E_876, '#skF_7'), C_875)=E_876 | ~v1_funct_1(k1_tmap_1(A_874, '#skF_3', C_875, '#skF_5', E_876, '#skF_7')) | k2_partfun1(C_875, '#skF_3', E_876, k9_subset_1(A_874, C_875, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_874, C_875, '#skF_5')) | ~m1_subset_1(E_876, k1_zfmisc_1(k2_zfmisc_1(C_875, '#skF_3'))) | ~v1_funct_2(E_876, C_875, '#skF_3') | ~v1_funct_1(E_876) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_874)) | ~m1_subset_1(C_875, k1_zfmisc_1(A_874)) | v1_xboole_0(C_875) | v1_xboole_0(A_874))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_4170])).
% 8.87/3.26  tff(c_4201, plain, (![A_874]: (k2_partfun1(k4_subset_1(A_874, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_874, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_874, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_874, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_874, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_874)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_874)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_874))), inference(resolution, [status(thm)], [c_52, c_4176])).
% 8.87/3.26  tff(c_4213, plain, (![A_874]: (k2_partfun1(k4_subset_1(A_874, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_874, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_874, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_874, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_874, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_874)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_874)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_874))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_755, c_4201])).
% 8.87/3.26  tff(c_4249, plain, (![A_888]: (k2_partfun1(k4_subset_1(A_888, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_888, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_888, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_888, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_888, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_888)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_888)) | v1_xboole_0(A_888))), inference(negUnitSimplification, [status(thm)], [c_66, c_4213])).
% 8.87/3.26  tff(c_899, plain, (![E_357, C_361, F_362, A_359, B_358, D_360]: (v1_funct_1(k1_tmap_1(A_359, B_358, C_361, D_360, E_357, F_362)) | ~m1_subset_1(F_362, k1_zfmisc_1(k2_zfmisc_1(D_360, B_358))) | ~v1_funct_2(F_362, D_360, B_358) | ~v1_funct_1(F_362) | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(C_361, B_358))) | ~v1_funct_2(E_357, C_361, B_358) | ~v1_funct_1(E_357) | ~m1_subset_1(D_360, k1_zfmisc_1(A_359)) | v1_xboole_0(D_360) | ~m1_subset_1(C_361, k1_zfmisc_1(A_359)) | v1_xboole_0(C_361) | v1_xboole_0(B_358) | v1_xboole_0(A_359))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.87/3.26  tff(c_908, plain, (![A_359, C_361, E_357]: (v1_funct_1(k1_tmap_1(A_359, '#skF_3', C_361, '#skF_5', E_357, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(C_361, '#skF_3'))) | ~v1_funct_2(E_357, C_361, '#skF_3') | ~v1_funct_1(E_357) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_359)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_361, k1_zfmisc_1(A_359)) | v1_xboole_0(C_361) | v1_xboole_0('#skF_3') | v1_xboole_0(A_359))), inference(resolution, [status(thm)], [c_46, c_899])).
% 8.87/3.26  tff(c_915, plain, (![A_359, C_361, E_357]: (v1_funct_1(k1_tmap_1(A_359, '#skF_3', C_361, '#skF_5', E_357, '#skF_7')) | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(C_361, '#skF_3'))) | ~v1_funct_2(E_357, C_361, '#skF_3') | ~v1_funct_1(E_357) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_359)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_361, k1_zfmisc_1(A_359)) | v1_xboole_0(C_361) | v1_xboole_0('#skF_3') | v1_xboole_0(A_359))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_908])).
% 8.87/3.26  tff(c_928, plain, (![A_366, C_367, E_368]: (v1_funct_1(k1_tmap_1(A_366, '#skF_3', C_367, '#skF_5', E_368, '#skF_7')) | ~m1_subset_1(E_368, k1_zfmisc_1(k2_zfmisc_1(C_367, '#skF_3'))) | ~v1_funct_2(E_368, C_367, '#skF_3') | ~v1_funct_1(E_368) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_366)) | ~m1_subset_1(C_367, k1_zfmisc_1(A_366)) | v1_xboole_0(C_367) | v1_xboole_0(A_366))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_915])).
% 8.87/3.26  tff(c_941, plain, (![A_366]: (v1_funct_1(k1_tmap_1(A_366, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_366)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_366)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_366))), inference(resolution, [status(thm)], [c_52, c_928])).
% 8.87/3.26  tff(c_950, plain, (![A_366]: (v1_funct_1(k1_tmap_1(A_366, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_366)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_366)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_366))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_941])).
% 8.87/3.26  tff(c_959, plain, (![A_370]: (v1_funct_1(k1_tmap_1(A_370, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_370)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_370)) | v1_xboole_0(A_370))), inference(negUnitSimplification, [status(thm)], [c_66, c_950])).
% 8.87/3.26  tff(c_962, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_959])).
% 8.87/3.26  tff(c_965, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_962])).
% 8.87/3.26  tff(c_966, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_70, c_965])).
% 8.87/3.26  tff(c_1192, plain, (![F_416, B_414, D_415, C_417, E_418, A_413]: (k2_partfun1(k4_subset_1(A_413, C_417, D_415), B_414, k1_tmap_1(A_413, B_414, C_417, D_415, E_418, F_416), D_415)=F_416 | ~m1_subset_1(k1_tmap_1(A_413, B_414, C_417, D_415, E_418, F_416), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_413, C_417, D_415), B_414))) | ~v1_funct_2(k1_tmap_1(A_413, B_414, C_417, D_415, E_418, F_416), k4_subset_1(A_413, C_417, D_415), B_414) | ~v1_funct_1(k1_tmap_1(A_413, B_414, C_417, D_415, E_418, F_416)) | k2_partfun1(D_415, B_414, F_416, k9_subset_1(A_413, C_417, D_415))!=k2_partfun1(C_417, B_414, E_418, k9_subset_1(A_413, C_417, D_415)) | ~m1_subset_1(F_416, k1_zfmisc_1(k2_zfmisc_1(D_415, B_414))) | ~v1_funct_2(F_416, D_415, B_414) | ~v1_funct_1(F_416) | ~m1_subset_1(E_418, k1_zfmisc_1(k2_zfmisc_1(C_417, B_414))) | ~v1_funct_2(E_418, C_417, B_414) | ~v1_funct_1(E_418) | ~m1_subset_1(D_415, k1_zfmisc_1(A_413)) | v1_xboole_0(D_415) | ~m1_subset_1(C_417, k1_zfmisc_1(A_413)) | v1_xboole_0(C_417) | v1_xboole_0(B_414) | v1_xboole_0(A_413))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.87/3.26  tff(c_2192, plain, (![A_562, F_565, D_563, E_560, C_564, B_561]: (k2_partfun1(k4_subset_1(A_562, C_564, D_563), B_561, k1_tmap_1(A_562, B_561, C_564, D_563, E_560, F_565), D_563)=F_565 | ~v1_funct_2(k1_tmap_1(A_562, B_561, C_564, D_563, E_560, F_565), k4_subset_1(A_562, C_564, D_563), B_561) | ~v1_funct_1(k1_tmap_1(A_562, B_561, C_564, D_563, E_560, F_565)) | k2_partfun1(D_563, B_561, F_565, k9_subset_1(A_562, C_564, D_563))!=k2_partfun1(C_564, B_561, E_560, k9_subset_1(A_562, C_564, D_563)) | ~m1_subset_1(F_565, k1_zfmisc_1(k2_zfmisc_1(D_563, B_561))) | ~v1_funct_2(F_565, D_563, B_561) | ~v1_funct_1(F_565) | ~m1_subset_1(E_560, k1_zfmisc_1(k2_zfmisc_1(C_564, B_561))) | ~v1_funct_2(E_560, C_564, B_561) | ~v1_funct_1(E_560) | ~m1_subset_1(D_563, k1_zfmisc_1(A_562)) | v1_xboole_0(D_563) | ~m1_subset_1(C_564, k1_zfmisc_1(A_562)) | v1_xboole_0(C_564) | v1_xboole_0(B_561) | v1_xboole_0(A_562))), inference(resolution, [status(thm)], [c_38, c_1192])).
% 8.87/3.26  tff(c_2375, plain, (![C_594, A_592, E_590, D_593, F_595, B_591]: (k2_partfun1(k4_subset_1(A_592, C_594, D_593), B_591, k1_tmap_1(A_592, B_591, C_594, D_593, E_590, F_595), D_593)=F_595 | ~v1_funct_1(k1_tmap_1(A_592, B_591, C_594, D_593, E_590, F_595)) | k2_partfun1(D_593, B_591, F_595, k9_subset_1(A_592, C_594, D_593))!=k2_partfun1(C_594, B_591, E_590, k9_subset_1(A_592, C_594, D_593)) | ~m1_subset_1(F_595, k1_zfmisc_1(k2_zfmisc_1(D_593, B_591))) | ~v1_funct_2(F_595, D_593, B_591) | ~v1_funct_1(F_595) | ~m1_subset_1(E_590, k1_zfmisc_1(k2_zfmisc_1(C_594, B_591))) | ~v1_funct_2(E_590, C_594, B_591) | ~v1_funct_1(E_590) | ~m1_subset_1(D_593, k1_zfmisc_1(A_592)) | v1_xboole_0(D_593) | ~m1_subset_1(C_594, k1_zfmisc_1(A_592)) | v1_xboole_0(C_594) | v1_xboole_0(B_591) | v1_xboole_0(A_592))), inference(resolution, [status(thm)], [c_40, c_2192])).
% 8.87/3.26  tff(c_2392, plain, (![A_592, C_594, E_590]: (k2_partfun1(k4_subset_1(A_592, C_594, '#skF_5'), '#skF_3', k1_tmap_1(A_592, '#skF_3', C_594, '#skF_5', E_590, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_592, '#skF_3', C_594, '#skF_5', E_590, '#skF_7')) | k2_partfun1(C_594, '#skF_3', E_590, k9_subset_1(A_592, C_594, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_592, C_594, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_590, k1_zfmisc_1(k2_zfmisc_1(C_594, '#skF_3'))) | ~v1_funct_2(E_590, C_594, '#skF_3') | ~v1_funct_1(E_590) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_592)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_594, k1_zfmisc_1(A_592)) | v1_xboole_0(C_594) | v1_xboole_0('#skF_3') | v1_xboole_0(A_592))), inference(resolution, [status(thm)], [c_46, c_2375])).
% 8.87/3.26  tff(c_2400, plain, (![A_592, C_594, E_590]: (k2_partfun1(k4_subset_1(A_592, C_594, '#skF_5'), '#skF_3', k1_tmap_1(A_592, '#skF_3', C_594, '#skF_5', E_590, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_592, '#skF_3', C_594, '#skF_5', E_590, '#skF_7')) | k2_partfun1(C_594, '#skF_3', E_590, k9_subset_1(A_592, C_594, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_592, C_594, '#skF_5')) | ~m1_subset_1(E_590, k1_zfmisc_1(k2_zfmisc_1(C_594, '#skF_3'))) | ~v1_funct_2(E_590, C_594, '#skF_3') | ~v1_funct_1(E_590) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_592)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_594, k1_zfmisc_1(A_592)) | v1_xboole_0(C_594) | v1_xboole_0('#skF_3') | v1_xboole_0(A_592))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_752, c_2392])).
% 8.87/3.26  tff(c_2410, plain, (![A_602, C_603, E_604]: (k2_partfun1(k4_subset_1(A_602, C_603, '#skF_5'), '#skF_3', k1_tmap_1(A_602, '#skF_3', C_603, '#skF_5', E_604, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_602, '#skF_3', C_603, '#skF_5', E_604, '#skF_7')) | k2_partfun1(C_603, '#skF_3', E_604, k9_subset_1(A_602, C_603, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_602, C_603, '#skF_5')) | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(C_603, '#skF_3'))) | ~v1_funct_2(E_604, C_603, '#skF_3') | ~v1_funct_1(E_604) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_602)) | ~m1_subset_1(C_603, k1_zfmisc_1(A_602)) | v1_xboole_0(C_603) | v1_xboole_0(A_602))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2400])).
% 8.87/3.26  tff(c_2435, plain, (![A_602]: (k2_partfun1(k4_subset_1(A_602, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_602, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_602, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_602, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_602, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_602)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_602)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_602))), inference(resolution, [status(thm)], [c_52, c_2410])).
% 8.87/3.26  tff(c_2447, plain, (![A_602]: (k2_partfun1(k4_subset_1(A_602, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_602, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_602, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_602, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_602, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_602)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_602)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_602))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_755, c_2435])).
% 8.87/3.26  tff(c_2482, plain, (![A_607]: (k2_partfun1(k4_subset_1(A_607, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_607, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_607, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_607, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_607, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_607)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_607)) | v1_xboole_0(A_607))), inference(negUnitSimplification, [status(thm)], [c_66, c_2447])).
% 8.87/3.26  tff(c_118, plain, (![C_228, A_229, B_230]: (v1_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.87/3.26  tff(c_131, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_118])).
% 8.87/3.26  tff(c_138, plain, (![C_235, A_236, B_237]: (v1_xboole_0(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~v1_xboole_0(A_236))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.87/3.26  tff(c_223, plain, (![A_249, B_250]: (v1_xboole_0('#skF_1'(k2_zfmisc_1(A_249, B_250))) | ~v1_xboole_0(A_249) | v1_xboole_0(k2_zfmisc_1(A_249, B_250)))), inference(resolution, [status(thm)], [c_14, c_138])).
% 8.87/3.26  tff(c_232, plain, (![A_251, B_252]: (~v1_xboole_0(A_251) | v1_xboole_0(k2_zfmisc_1(A_251, B_252)))), inference(resolution, [status(thm)], [c_223, c_12])).
% 8.87/3.26  tff(c_245, plain, (![A_253, B_254]: (k2_zfmisc_1(A_253, B_254)=k1_xboole_0 | ~v1_xboole_0(A_253))), inference(resolution, [status(thm)], [c_232, c_8])).
% 8.87/3.26  tff(c_252, plain, (![B_255]: (k2_zfmisc_1(k1_xboole_0, B_255)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_245])).
% 8.87/3.26  tff(c_261, plain, (![B_14]: (k7_relat_1(B_14, k1_xboole_0)=k3_xboole_0(B_14, k1_xboole_0) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_252, c_20])).
% 8.87/3.26  tff(c_280, plain, (![B_256]: (k7_relat_1(B_256, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_256))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_261])).
% 8.87/3.26  tff(c_291, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_131, c_280])).
% 8.87/3.26  tff(c_152, plain, (![A_238, B_239]: (r1_xboole_0(A_238, B_239) | ~r1_subset_1(A_238, B_239) | v1_xboole_0(B_239) | v1_xboole_0(A_238))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.87/3.26  tff(c_431, plain, (![A_279, B_280]: (k3_xboole_0(A_279, B_280)=k1_xboole_0 | ~r1_subset_1(A_279, B_280) | v1_xboole_0(B_280) | v1_xboole_0(A_279))), inference(resolution, [status(thm)], [c_152, c_2])).
% 8.87/3.26  tff(c_437, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_431])).
% 8.87/3.26  tff(c_441, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_437])).
% 8.87/3.26  tff(c_130, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_118])).
% 8.87/3.26  tff(c_292, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_280])).
% 8.87/3.26  tff(c_293, plain, (![A_257, B_258, C_259, D_260]: (k2_partfun1(A_257, B_258, C_259, D_260)=k7_relat_1(C_259, D_260) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~v1_funct_1(C_259))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.87/3.26  tff(c_302, plain, (![D_260]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_260)=k7_relat_1('#skF_6', D_260) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_293])).
% 8.87/3.26  tff(c_309, plain, (![D_260]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_260)=k7_relat_1('#skF_6', D_260))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_302])).
% 8.87/3.26  tff(c_300, plain, (![D_260]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_260)=k7_relat_1('#skF_7', D_260) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_46, c_293])).
% 8.87/3.26  tff(c_306, plain, (![D_260]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_260)=k7_relat_1('#skF_7', D_260))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_300])).
% 8.87/3.26  tff(c_170, plain, (![A_242, B_243, C_244]: (k9_subset_1(A_242, B_243, C_244)=k3_xboole_0(B_243, C_244) | ~m1_subset_1(C_244, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.87/3.26  tff(c_185, plain, (![B_243]: (k9_subset_1('#skF_2', B_243, '#skF_5')=k3_xboole_0(B_243, '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_170])).
% 8.87/3.26  tff(c_44, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 8.87/3.26  tff(c_87, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_44])).
% 8.87/3.26  tff(c_195, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_87])).
% 8.87/3.26  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_441, c_292, c_441, c_309, c_306, c_195])).
% 8.87/3.26  tff(c_508, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 8.87/3.26  tff(c_771, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_508])).
% 8.87/3.26  tff(c_2493, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2482, c_771])).
% 8.87/3.26  tff(c_2507, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_738, c_737, c_664, c_664, c_602, c_602, c_966, c_2493])).
% 8.87/3.26  tff(c_2509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_2507])).
% 8.87/3.26  tff(c_2510, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_508])).
% 8.87/3.26  tff(c_4258, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4249, c_2510])).
% 8.87/3.26  tff(c_4269, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_737, c_664, c_602, c_738, c_664, c_602, c_2711, c_4258])).
% 8.87/3.26  tff(c_4271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_4269])).
% 8.87/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.87/3.26  
% 8.87/3.26  Inference rules
% 8.87/3.26  ----------------------
% 8.87/3.26  #Ref     : 0
% 8.87/3.26  #Sup     : 1029
% 8.87/3.26  #Fact    : 0
% 8.87/3.26  #Define  : 0
% 8.87/3.26  #Split   : 19
% 8.87/3.26  #Chain   : 0
% 8.87/3.26  #Close   : 0
% 8.87/3.26  
% 8.87/3.26  Ordering : KBO
% 8.87/3.26  
% 8.87/3.26  Simplification rules
% 8.87/3.26  ----------------------
% 8.87/3.26  #Subsume      : 451
% 8.87/3.26  #Demod        : 612
% 8.87/3.26  #Tautology    : 288
% 8.87/3.26  #SimpNegUnit  : 132
% 8.87/3.26  #BackRed      : 2
% 8.87/3.26  
% 8.87/3.26  #Partial instantiations: 0
% 8.87/3.26  #Strategies tried      : 1
% 8.87/3.26  
% 8.87/3.26  Timing (in seconds)
% 8.87/3.26  ----------------------
% 8.87/3.27  Preprocessing        : 0.69
% 8.87/3.27  Parsing              : 0.33
% 8.87/3.27  CNF conversion       : 0.10
% 8.87/3.27  Main loop            : 1.73
% 8.87/3.27  Inferencing          : 0.55
% 8.87/3.27  Reduction            : 0.59
% 8.87/3.27  Demodulation         : 0.43
% 8.87/3.27  BG Simplification    : 0.08
% 8.87/3.27  Subsumption          : 0.46
% 8.87/3.27  Abstraction          : 0.10
% 8.87/3.27  MUC search           : 0.00
% 8.87/3.27  Cooper               : 0.00
% 8.87/3.27  Total                : 2.47
% 8.87/3.27  Index Insertion      : 0.00
% 8.87/3.27  Index Deletion       : 0.00
% 8.87/3.27  Index Matching       : 0.00
% 8.87/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
