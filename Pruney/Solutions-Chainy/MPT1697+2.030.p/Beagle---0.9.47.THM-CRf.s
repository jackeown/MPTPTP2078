%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:13 EST 2020

% Result     : Theorem 23.29s
% Output     : CNFRefutation 23.90s
% Verified   : 
% Statistics : Number of formulae       :  427 (4084 expanded)
%              Number of leaves         :   52 (1382 expanded)
%              Depth                    :   24
%              Number of atoms          : 1223 (17862 expanded)
%              Number of equality atoms :  325 (3616 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_255,negated_conjecture,(
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

tff(f_213,axiom,(
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

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_131,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_179,axiom,(
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

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_60,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_101,plain,(
    ! [C_238,A_239,B_240] :
      ( v1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_112,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_101])).

tff(c_54880,plain,(
    ! [C_2954,A_2955,B_2956] :
      ( v4_relat_1(C_2954,A_2955)
      | ~ m1_subset_1(C_2954,k1_zfmisc_1(k2_zfmisc_1(A_2955,B_2956))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54891,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_54880])).

tff(c_56954,plain,(
    ! [B_3129,A_3130] :
      ( k1_relat_1(B_3129) = A_3130
      | ~ v1_partfun1(B_3129,A_3130)
      | ~ v4_relat_1(B_3129,A_3130)
      | ~ v1_relat_1(B_3129) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_56963,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54891,c_56954])).

tff(c_56972,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_56963])).

tff(c_57886,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56972])).

tff(c_58570,plain,(
    ! [C_3242,A_3243,B_3244] :
      ( v1_partfun1(C_3242,A_3243)
      | ~ v1_funct_2(C_3242,A_3243,B_3244)
      | ~ v1_funct_1(C_3242)
      | ~ m1_subset_1(C_3242,k1_zfmisc_1(k2_zfmisc_1(A_3243,B_3244)))
      | v1_xboole_0(B_3244) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58573,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_58570])).

tff(c_58583,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58573])).

tff(c_58585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_57886,c_58583])).

tff(c_58586,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56972])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( r1_xboole_0(k1_relat_1(B_26),A_25)
      | k7_relat_1(B_26,A_25) != k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58598,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58586,c_30])).

tff(c_58811,plain,(
    ! [A_3259] :
      ( r1_xboole_0('#skF_4',A_3259)
      | k7_relat_1('#skF_6',A_3259) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_58598])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k9_relat_1(B_16,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58604,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58586,c_14])).

tff(c_58622,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_6',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_58604])).

tff(c_59288,plain,(
    ! [A_3283] :
      ( k9_relat_1('#skF_6',A_3283) = k1_xboole_0
      | k7_relat_1('#skF_6',A_3283) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58811,c_58622])).

tff(c_4,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_101])).

tff(c_9436,plain,(
    ! [A_958] :
      ( k1_relat_1(A_958) = k1_xboole_0
      | k2_relat_1(A_958) != k1_xboole_0
      | ~ v1_relat_1(A_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9446,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_114,c_9436])).

tff(c_9449,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9446])).

tff(c_78,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | ~ r1_subset_1(A_27,B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10229,plain,(
    ! [C_1059,A_1060,B_1061] :
      ( v4_relat_1(C_1059,A_1060)
      | ~ m1_subset_1(C_1059,k1_zfmisc_1(k2_zfmisc_1(A_1060,B_1061))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10240,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_10229])).

tff(c_10442,plain,(
    ! [B_1103,A_1104] :
      ( k1_relat_1(B_1103) = A_1104
      | ~ v1_partfun1(B_1103,A_1104)
      | ~ v4_relat_1(B_1103,A_1104)
      | ~ v1_relat_1(B_1103) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10451,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10240,c_10442])).

tff(c_10460,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_10451])).

tff(c_10472,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10460])).

tff(c_10618,plain,(
    ! [C_1118,A_1119,B_1120] :
      ( v1_partfun1(C_1118,A_1119)
      | ~ v1_funct_2(C_1118,A_1119,B_1120)
      | ~ v1_funct_1(C_1118)
      | ~ m1_subset_1(C_1118,k1_zfmisc_1(k2_zfmisc_1(A_1119,B_1120)))
      | v1_xboole_0(B_1120) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10621,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_10618])).

tff(c_10631,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_10621])).

tff(c_10633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_10472,c_10631])).

tff(c_10634,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10460])).

tff(c_18,plain,(
    ! [A_17,B_19] :
      ( k7_relat_1(A_17,B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,k1_relat_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10640,plain,(
    ! [B_19] :
      ( k7_relat_1('#skF_6',B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10634,c_18])).

tff(c_10793,plain,(
    ! [B_1128] :
      ( k7_relat_1('#skF_6',B_1128) = k1_xboole_0
      | ~ r1_xboole_0(B_1128,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_10640])).

tff(c_10805,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_6',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_34,c_10793])).

tff(c_10860,plain,(
    ! [A_1131] :
      ( k7_relat_1('#skF_6',A_1131) = k1_xboole_0
      | ~ r1_subset_1(A_1131,'#skF_4')
      | v1_xboole_0(A_1131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_10805])).

tff(c_10863,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_10860])).

tff(c_10866,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_10863])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10873,plain,
    ( k9_relat_1('#skF_6','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10866,c_12])).

tff(c_10877,plain,(
    k9_relat_1('#skF_6','#skF_3') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_10873])).

tff(c_10282,plain,(
    ! [B_1080,A_1081] :
      ( k9_relat_1(B_1080,A_1081) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_1080),A_1081)
      | ~ v1_relat_1(B_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10405,plain,(
    ! [B_1098,A_1099] :
      ( k9_relat_1(B_1098,A_1099) = k1_xboole_0
      | k7_relat_1(B_1098,A_1099) != k1_xboole_0
      | ~ v1_relat_1(B_1098) ) ),
    inference(resolution,[status(thm)],[c_30,c_10282])).

tff(c_10414,plain,(
    ! [A_1099] :
      ( k9_relat_1('#skF_6',A_1099) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1099) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_112,c_10405])).

tff(c_10894,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10877,c_10414])).

tff(c_10901,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10866,c_10894])).

tff(c_10903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9449,c_10901])).

tff(c_10904,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9446])).

tff(c_56812,plain,(
    ! [B_3121,A_3122] :
      ( r1_xboole_0(k1_relat_1(B_3121),A_3122)
      | k7_relat_1(B_3121,A_3122) != k1_xboole_0
      | ~ v1_relat_1(B_3121) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56832,plain,(
    ! [A_3122] :
      ( r1_xboole_0(k1_xboole_0,A_3122)
      | k7_relat_1(k1_xboole_0,A_3122) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10904,c_56812])).

tff(c_56839,plain,(
    ! [A_3122] :
      ( r1_xboole_0(k1_xboole_0,A_3122)
      | k7_relat_1(k1_xboole_0,A_3122) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_56832])).

tff(c_58610,plain,(
    ! [B_19] :
      ( k7_relat_1('#skF_6',B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58586,c_18])).

tff(c_58647,plain,(
    ! [B_3246] :
      ( k7_relat_1('#skF_6',B_3246) = k1_xboole_0
      | ~ r1_xboole_0(B_3246,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_58610])).

tff(c_58673,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56839,c_58647])).

tff(c_59097,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58673])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( r1_xboole_0(k1_relat_1(B_16),A_15)
      | k9_relat_1(B_16,A_15) != k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58607,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58586,c_16])).

tff(c_58995,plain,(
    ! [A_3266] :
      ( r1_xboole_0('#skF_4',A_3266)
      | k9_relat_1('#skF_6',A_3266) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_58607])).

tff(c_54895,plain,(
    ! [A_2958,B_2959] :
      ( k7_relat_1(A_2958,B_2959) = k1_xboole_0
      | ~ r1_xboole_0(B_2959,k1_relat_1(A_2958))
      | ~ v1_relat_1(A_2958) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54898,plain,(
    ! [B_2959] :
      ( k7_relat_1(k1_xboole_0,B_2959) = k1_xboole_0
      | ~ r1_xboole_0(B_2959,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10904,c_54895])).

tff(c_54900,plain,(
    ! [B_2959] :
      ( k7_relat_1(k1_xboole_0,B_2959) = k1_xboole_0
      | ~ r1_xboole_0(B_2959,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_54898])).

tff(c_59028,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58995,c_54900])).

tff(c_59213,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_59097,c_59028])).

tff(c_59299,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59288,c_59213])).

tff(c_113,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_101])).

tff(c_54892,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_54880])).

tff(c_56960,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54892,c_56954])).

tff(c_56969,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_56960])).

tff(c_56983,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56969])).

tff(c_57824,plain,(
    ! [C_3194,A_3195,B_3196] :
      ( v1_partfun1(C_3194,A_3195)
      | ~ v1_funct_2(C_3194,A_3195,B_3196)
      | ~ v1_funct_1(C_3194)
      | ~ m1_subset_1(C_3194,k1_zfmisc_1(k2_zfmisc_1(A_3195,B_3196)))
      | v1_xboole_0(B_3196) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_57830,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_57824])).

tff(c_57841,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_57830])).

tff(c_57843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_56983,c_57841])).

tff(c_57844,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_56969])).

tff(c_28,plain,(
    ! [B_26,A_25] :
      ( k7_relat_1(B_26,A_25) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_57859,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57844,c_28])).

tff(c_58979,plain,(
    ! [A_3265] :
      ( k7_relat_1('#skF_5',A_3265) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_3265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_57859])).

tff(c_58989,plain,(
    ! [B_28] :
      ( k7_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_58979])).

tff(c_59132,plain,(
    ! [B_3277] :
      ( k7_relat_1('#skF_5',B_3277) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_3277)
      | v1_xboole_0(B_3277) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_58989])).

tff(c_59135,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_59132])).

tff(c_59138,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_59135])).

tff(c_57856,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57844,c_30])).

tff(c_57876,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_57856])).

tff(c_58672,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57876,c_58647])).

tff(c_59319,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59138,c_58672])).

tff(c_26,plain,(
    ! [B_24,A_23] :
      ( k3_xboole_0(k1_relat_1(B_24),A_23) = k1_relat_1(k7_relat_1(B_24,A_23))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58595,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_23)) = k3_xboole_0('#skF_4',A_23)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58586,c_26])).

tff(c_58616,plain,(
    ! [A_23] : k1_relat_1(k7_relat_1('#skF_6',A_23)) = k3_xboole_0('#skF_4',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_58595])).

tff(c_59323,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59319,c_58616])).

tff(c_59329,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10904,c_59323])).

tff(c_58891,plain,(
    ! [B_3262,A_3263] :
      ( k7_relat_1(B_3262,k3_xboole_0(k1_relat_1(B_3262),A_3263)) = k7_relat_1(B_3262,A_3263)
      | ~ v1_relat_1(B_3262) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58921,plain,(
    ! [A_3263] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_3263)) = k7_relat_1('#skF_6',A_3263)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58586,c_58891])).

tff(c_58943,plain,(
    ! [A_3263] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_3263)) = k7_relat_1('#skF_6',A_3263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_58921])).

tff(c_59336,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_59329,c_58943])).

tff(c_59339,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59319,c_59336])).

tff(c_59341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59299,c_59339])).

tff(c_59342,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58673])).

tff(c_58663,plain,(
    ! [A_27] :
      ( k7_relat_1('#skF_6',A_27) = k1_xboole_0
      | ~ r1_subset_1(A_27,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_34,c_58647])).

tff(c_59445,plain,(
    ! [A_3297] :
      ( k7_relat_1('#skF_6',A_3297) = k1_xboole_0
      | ~ r1_subset_1(A_3297,'#skF_4')
      | v1_xboole_0(A_3297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_58663])).

tff(c_59452,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_59445])).

tff(c_59458,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_59452])).

tff(c_58618,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_4',A_25)
      | k7_relat_1('#skF_6',A_25) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_58598])).

tff(c_57868,plain,(
    ! [B_19] :
      ( k7_relat_1('#skF_5',B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57844,c_18])).

tff(c_58853,plain,(
    ! [B_3261] :
      ( k7_relat_1('#skF_5',B_3261) = k1_xboole_0
      | ~ r1_xboole_0(B_3261,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_57868])).

tff(c_58882,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k7_relat_1('#skF_6','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58618,c_58853])).

tff(c_60000,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59458,c_58882])).

tff(c_57853,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_23)) = k3_xboole_0('#skF_3',A_23)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57844,c_26])).

tff(c_57874,plain,(
    ! [A_23] : k1_relat_1(k7_relat_1('#skF_5',A_23)) = k3_xboole_0('#skF_3',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_57853])).

tff(c_60004,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60000,c_57874])).

tff(c_60010,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10904,c_60004])).

tff(c_58696,plain,(
    ! [A_3249,B_3250,C_3251] :
      ( k9_subset_1(A_3249,B_3250,C_3251) = k3_xboole_0(B_3250,C_3251)
      | ~ m1_subset_1(C_3251,k1_zfmisc_1(A_3249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58711,plain,(
    ! [B_3250] : k9_subset_1('#skF_1',B_3250,'#skF_4') = k3_xboole_0(B_3250,'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_58696])).

tff(c_58924,plain,(
    ! [A_3263] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_3263)) = k7_relat_1('#skF_5',A_3263)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57844,c_58891])).

tff(c_58945,plain,(
    ! [A_3263] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_3263)) = k7_relat_1('#skF_5',A_3263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_58924])).

tff(c_59795,plain,(
    ! [D_3322,B_3320,E_3321,C_3325,F_3324,A_3323] :
      ( v1_funct_1(k1_tmap_1(A_3323,B_3320,C_3325,D_3322,E_3321,F_3324))
      | ~ m1_subset_1(F_3324,k1_zfmisc_1(k2_zfmisc_1(D_3322,B_3320)))
      | ~ v1_funct_2(F_3324,D_3322,B_3320)
      | ~ v1_funct_1(F_3324)
      | ~ m1_subset_1(E_3321,k1_zfmisc_1(k2_zfmisc_1(C_3325,B_3320)))
      | ~ v1_funct_2(E_3321,C_3325,B_3320)
      | ~ v1_funct_1(E_3321)
      | ~ m1_subset_1(D_3322,k1_zfmisc_1(A_3323))
      | v1_xboole_0(D_3322)
      | ~ m1_subset_1(C_3325,k1_zfmisc_1(A_3323))
      | v1_xboole_0(C_3325)
      | v1_xboole_0(B_3320)
      | v1_xboole_0(A_3323) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_59797,plain,(
    ! [A_3323,C_3325,E_3321] :
      ( v1_funct_1(k1_tmap_1(A_3323,'#skF_2',C_3325,'#skF_4',E_3321,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3321,k1_zfmisc_1(k2_zfmisc_1(C_3325,'#skF_2')))
      | ~ v1_funct_2(E_3321,C_3325,'#skF_2')
      | ~ v1_funct_1(E_3321)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3323))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3325,k1_zfmisc_1(A_3323))
      | v1_xboole_0(C_3325)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3323) ) ),
    inference(resolution,[status(thm)],[c_66,c_59795])).

tff(c_59805,plain,(
    ! [A_3323,C_3325,E_3321] :
      ( v1_funct_1(k1_tmap_1(A_3323,'#skF_2',C_3325,'#skF_4',E_3321,'#skF_6'))
      | ~ m1_subset_1(E_3321,k1_zfmisc_1(k2_zfmisc_1(C_3325,'#skF_2')))
      | ~ v1_funct_2(E_3321,C_3325,'#skF_2')
      | ~ v1_funct_1(E_3321)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3323))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3325,k1_zfmisc_1(A_3323))
      | v1_xboole_0(C_3325)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_59797])).

tff(c_61694,plain,(
    ! [A_3407,C_3408,E_3409] :
      ( v1_funct_1(k1_tmap_1(A_3407,'#skF_2',C_3408,'#skF_4',E_3409,'#skF_6'))
      | ~ m1_subset_1(E_3409,k1_zfmisc_1(k2_zfmisc_1(C_3408,'#skF_2')))
      | ~ v1_funct_2(E_3409,C_3408,'#skF_2')
      | ~ v1_funct_1(E_3409)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3407))
      | ~ m1_subset_1(C_3408,k1_zfmisc_1(A_3407))
      | v1_xboole_0(C_3408)
      | v1_xboole_0(A_3407) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_59805])).

tff(c_61701,plain,(
    ! [A_3407] :
      ( v1_funct_1(k1_tmap_1(A_3407,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3407))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3407))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3407) ) ),
    inference(resolution,[status(thm)],[c_72,c_61694])).

tff(c_61714,plain,(
    ! [A_3407] :
      ( v1_funct_1(k1_tmap_1(A_3407,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3407))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3407))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_61701])).

tff(c_62620,plain,(
    ! [A_3426] :
      ( v1_funct_1(k1_tmap_1(A_3426,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3426))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3426))
      | v1_xboole_0(A_3426) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_61714])).

tff(c_62623,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_62620])).

tff(c_62626,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_62623])).

tff(c_62627,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_62626])).

tff(c_59391,plain,(
    ! [A_3291,B_3292,C_3293,D_3294] :
      ( k2_partfun1(A_3291,B_3292,C_3293,D_3294) = k7_relat_1(C_3293,D_3294)
      | ~ m1_subset_1(C_3293,k1_zfmisc_1(k2_zfmisc_1(A_3291,B_3292)))
      | ~ v1_funct_1(C_3293) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_59395,plain,(
    ! [D_3294] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_3294) = k7_relat_1('#skF_5',D_3294)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_59391])).

tff(c_59404,plain,(
    ! [D_3294] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_3294) = k7_relat_1('#skF_5',D_3294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_59395])).

tff(c_59393,plain,(
    ! [D_3294] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_3294) = k7_relat_1('#skF_6',D_3294)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_59391])).

tff(c_59401,plain,(
    ! [D_3294] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_3294) = k7_relat_1('#skF_6',D_3294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_59393])).

tff(c_58,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_60084,plain,(
    ! [A_3346,C_3348,B_3349,E_3347,F_3350,D_3345] :
      ( k2_partfun1(k4_subset_1(A_3346,C_3348,D_3345),B_3349,k1_tmap_1(A_3346,B_3349,C_3348,D_3345,E_3347,F_3350),D_3345) = F_3350
      | ~ m1_subset_1(k1_tmap_1(A_3346,B_3349,C_3348,D_3345,E_3347,F_3350),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3346,C_3348,D_3345),B_3349)))
      | ~ v1_funct_2(k1_tmap_1(A_3346,B_3349,C_3348,D_3345,E_3347,F_3350),k4_subset_1(A_3346,C_3348,D_3345),B_3349)
      | ~ v1_funct_1(k1_tmap_1(A_3346,B_3349,C_3348,D_3345,E_3347,F_3350))
      | k2_partfun1(D_3345,B_3349,F_3350,k9_subset_1(A_3346,C_3348,D_3345)) != k2_partfun1(C_3348,B_3349,E_3347,k9_subset_1(A_3346,C_3348,D_3345))
      | ~ m1_subset_1(F_3350,k1_zfmisc_1(k2_zfmisc_1(D_3345,B_3349)))
      | ~ v1_funct_2(F_3350,D_3345,B_3349)
      | ~ v1_funct_1(F_3350)
      | ~ m1_subset_1(E_3347,k1_zfmisc_1(k2_zfmisc_1(C_3348,B_3349)))
      | ~ v1_funct_2(E_3347,C_3348,B_3349)
      | ~ v1_funct_1(E_3347)
      | ~ m1_subset_1(D_3345,k1_zfmisc_1(A_3346))
      | v1_xboole_0(D_3345)
      | ~ m1_subset_1(C_3348,k1_zfmisc_1(A_3346))
      | v1_xboole_0(C_3348)
      | v1_xboole_0(B_3349)
      | v1_xboole_0(A_3346) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66690,plain,(
    ! [D_3618,F_3620,A_3619,C_3621,E_3617,B_3616] :
      ( k2_partfun1(k4_subset_1(A_3619,C_3621,D_3618),B_3616,k1_tmap_1(A_3619,B_3616,C_3621,D_3618,E_3617,F_3620),D_3618) = F_3620
      | ~ v1_funct_2(k1_tmap_1(A_3619,B_3616,C_3621,D_3618,E_3617,F_3620),k4_subset_1(A_3619,C_3621,D_3618),B_3616)
      | ~ v1_funct_1(k1_tmap_1(A_3619,B_3616,C_3621,D_3618,E_3617,F_3620))
      | k2_partfun1(D_3618,B_3616,F_3620,k9_subset_1(A_3619,C_3621,D_3618)) != k2_partfun1(C_3621,B_3616,E_3617,k9_subset_1(A_3619,C_3621,D_3618))
      | ~ m1_subset_1(F_3620,k1_zfmisc_1(k2_zfmisc_1(D_3618,B_3616)))
      | ~ v1_funct_2(F_3620,D_3618,B_3616)
      | ~ v1_funct_1(F_3620)
      | ~ m1_subset_1(E_3617,k1_zfmisc_1(k2_zfmisc_1(C_3621,B_3616)))
      | ~ v1_funct_2(E_3617,C_3621,B_3616)
      | ~ v1_funct_1(E_3617)
      | ~ m1_subset_1(D_3618,k1_zfmisc_1(A_3619))
      | v1_xboole_0(D_3618)
      | ~ m1_subset_1(C_3621,k1_zfmisc_1(A_3619))
      | v1_xboole_0(C_3621)
      | v1_xboole_0(B_3616)
      | v1_xboole_0(A_3619) ) ),
    inference(resolution,[status(thm)],[c_58,c_60084])).

tff(c_69864,plain,(
    ! [D_3723,A_3724,C_3726,E_3722,F_3725,B_3721] :
      ( k2_partfun1(k4_subset_1(A_3724,C_3726,D_3723),B_3721,k1_tmap_1(A_3724,B_3721,C_3726,D_3723,E_3722,F_3725),D_3723) = F_3725
      | ~ v1_funct_1(k1_tmap_1(A_3724,B_3721,C_3726,D_3723,E_3722,F_3725))
      | k2_partfun1(D_3723,B_3721,F_3725,k9_subset_1(A_3724,C_3726,D_3723)) != k2_partfun1(C_3726,B_3721,E_3722,k9_subset_1(A_3724,C_3726,D_3723))
      | ~ m1_subset_1(F_3725,k1_zfmisc_1(k2_zfmisc_1(D_3723,B_3721)))
      | ~ v1_funct_2(F_3725,D_3723,B_3721)
      | ~ v1_funct_1(F_3725)
      | ~ m1_subset_1(E_3722,k1_zfmisc_1(k2_zfmisc_1(C_3726,B_3721)))
      | ~ v1_funct_2(E_3722,C_3726,B_3721)
      | ~ v1_funct_1(E_3722)
      | ~ m1_subset_1(D_3723,k1_zfmisc_1(A_3724))
      | v1_xboole_0(D_3723)
      | ~ m1_subset_1(C_3726,k1_zfmisc_1(A_3724))
      | v1_xboole_0(C_3726)
      | v1_xboole_0(B_3721)
      | v1_xboole_0(A_3724) ) ),
    inference(resolution,[status(thm)],[c_60,c_66690])).

tff(c_69868,plain,(
    ! [A_3724,C_3726,E_3722] :
      ( k2_partfun1(k4_subset_1(A_3724,C_3726,'#skF_4'),'#skF_2',k1_tmap_1(A_3724,'#skF_2',C_3726,'#skF_4',E_3722,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3724,'#skF_2',C_3726,'#skF_4',E_3722,'#skF_6'))
      | k2_partfun1(C_3726,'#skF_2',E_3722,k9_subset_1(A_3724,C_3726,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_3724,C_3726,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3722,k1_zfmisc_1(k2_zfmisc_1(C_3726,'#skF_2')))
      | ~ v1_funct_2(E_3722,C_3726,'#skF_2')
      | ~ v1_funct_1(E_3722)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3724))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3726,k1_zfmisc_1(A_3724))
      | v1_xboole_0(C_3726)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3724) ) ),
    inference(resolution,[status(thm)],[c_66,c_69864])).

tff(c_69877,plain,(
    ! [A_3724,C_3726,E_3722] :
      ( k2_partfun1(k4_subset_1(A_3724,C_3726,'#skF_4'),'#skF_2',k1_tmap_1(A_3724,'#skF_2',C_3726,'#skF_4',E_3722,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3724,'#skF_2',C_3726,'#skF_4',E_3722,'#skF_6'))
      | k2_partfun1(C_3726,'#skF_2',E_3722,k9_subset_1(A_3724,C_3726,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3724,C_3726,'#skF_4'))
      | ~ m1_subset_1(E_3722,k1_zfmisc_1(k2_zfmisc_1(C_3726,'#skF_2')))
      | ~ v1_funct_2(E_3722,C_3726,'#skF_2')
      | ~ v1_funct_1(E_3722)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3724))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3726,k1_zfmisc_1(A_3724))
      | v1_xboole_0(C_3726)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3724) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_59401,c_69868])).

tff(c_71756,plain,(
    ! [A_3767,C_3768,E_3769] :
      ( k2_partfun1(k4_subset_1(A_3767,C_3768,'#skF_4'),'#skF_2',k1_tmap_1(A_3767,'#skF_2',C_3768,'#skF_4',E_3769,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3767,'#skF_2',C_3768,'#skF_4',E_3769,'#skF_6'))
      | k2_partfun1(C_3768,'#skF_2',E_3769,k9_subset_1(A_3767,C_3768,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3767,C_3768,'#skF_4'))
      | ~ m1_subset_1(E_3769,k1_zfmisc_1(k2_zfmisc_1(C_3768,'#skF_2')))
      | ~ v1_funct_2(E_3769,C_3768,'#skF_2')
      | ~ v1_funct_1(E_3769)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3767))
      | ~ m1_subset_1(C_3768,k1_zfmisc_1(A_3767))
      | v1_xboole_0(C_3768)
      | v1_xboole_0(A_3767) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_69877])).

tff(c_71763,plain,(
    ! [A_3767] :
      ( k2_partfun1(k4_subset_1(A_3767,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3767,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3767,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_3767,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3767,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3767))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3767))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3767) ) ),
    inference(resolution,[status(thm)],[c_72,c_71756])).

tff(c_71776,plain,(
    ! [A_3767] :
      ( k2_partfun1(k4_subset_1(A_3767,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3767,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3767,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_3767,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3767,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3767))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3767))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_59404,c_71763])).

tff(c_75676,plain,(
    ! [A_3807] :
      ( k2_partfun1(k4_subset_1(A_3807,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_3807,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3807,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_3807,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3807,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3807))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3807))
      | v1_xboole_0(A_3807) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_71776])).

tff(c_4372,plain,(
    ! [C_656,A_657,B_658] :
      ( v4_relat_1(C_656,A_657)
      | ~ m1_subset_1(C_656,k1_zfmisc_1(k2_zfmisc_1(A_657,B_658))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4384,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4372])).

tff(c_4669,plain,(
    ! [B_700,A_701] :
      ( k1_relat_1(B_700) = A_701
      | ~ v1_partfun1(B_700,A_701)
      | ~ v4_relat_1(B_700,A_701)
      | ~ v1_relat_1(B_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4675,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4384,c_4669])).

tff(c_4684,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_4675])).

tff(c_4694,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4684])).

tff(c_5387,plain,(
    ! [C_761,A_762,B_763] :
      ( v1_partfun1(C_761,A_762)
      | ~ v1_funct_2(C_761,A_762,B_763)
      | ~ v1_funct_1(C_761)
      | ~ m1_subset_1(C_761,k1_zfmisc_1(k2_zfmisc_1(A_762,B_763)))
      | v1_xboole_0(B_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5393,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_5387])).

tff(c_5404,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_5393])).

tff(c_5406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4694,c_5404])).

tff(c_5407,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4684])).

tff(c_5419,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5407,c_28])).

tff(c_6539,plain,(
    ! [A_830] :
      ( k7_relat_1('#skF_5',A_830) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_830) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_5419])).

tff(c_6549,plain,(
    ! [B_28] :
      ( k7_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_6539])).

tff(c_6808,plain,(
    ! [B_848] :
      ( k7_relat_1('#skF_5',B_848) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_848)
      | v1_xboole_0(B_848) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6549])).

tff(c_6811,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_6808])).

tff(c_6814,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6811])).

tff(c_116,plain,(
    ! [A_241] :
      ( k1_relat_1(A_241) = k1_xboole_0
      | k2_relat_1(A_241) != k1_xboole_0
      | ~ v1_relat_1(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_126,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_114,c_116])).

tff(c_129,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_998,plain,(
    ! [C_344,A_345,B_346] :
      ( v4_relat_1(C_344,A_345)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1010,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_998])).

tff(c_1250,plain,(
    ! [B_396,A_397] :
      ( k1_relat_1(B_396) = A_397
      | ~ v1_partfun1(B_396,A_397)
      | ~ v4_relat_1(B_396,A_397)
      | ~ v1_relat_1(B_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1256,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1010,c_1250])).

tff(c_1265,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1256])).

tff(c_1275,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1265])).

tff(c_1803,plain,(
    ! [C_435,A_436,B_437] :
      ( v1_partfun1(C_435,A_436)
      | ~ v1_funct_2(C_435,A_436,B_437)
      | ~ v1_funct_1(C_435)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1(A_436,B_437)))
      | v1_xboole_0(B_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1809,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1803])).

tff(c_1820,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1809])).

tff(c_1822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1275,c_1820])).

tff(c_1823,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1265])).

tff(c_1835,plain,(
    ! [A_15] :
      ( k9_relat_1('#skF_5',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1823,c_14])).

tff(c_1962,plain,(
    ! [A_443] :
      ( k9_relat_1('#skF_5',A_443) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1835])).

tff(c_1969,plain,(
    ! [B_28] :
      ( k9_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_1962])).

tff(c_1995,plain,(
    ! [B_445] :
      ( k9_relat_1('#skF_5',B_445) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_445)
      | v1_xboole_0(B_445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1969])).

tff(c_1998,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1995])).

tff(c_2001,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1998])).

tff(c_1099,plain,(
    ! [B_376,A_377] :
      ( r1_xboole_0(k1_relat_1(B_376),A_377)
      | k9_relat_1(B_376,A_377) != k1_xboole_0
      | ~ v1_relat_1(B_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1115,plain,(
    ! [B_376,A_377] :
      ( k7_relat_1(B_376,A_377) = k1_xboole_0
      | k9_relat_1(B_376,A_377) != k1_xboole_0
      | ~ v1_relat_1(B_376) ) ),
    inference(resolution,[status(thm)],[c_1099,c_28])).

tff(c_2007,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2001,c_1115])).

tff(c_2016,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2007])).

tff(c_2025,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2016,c_12])).

tff(c_2029,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2001,c_2025])).

tff(c_2031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_2029])).

tff(c_2032,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_5428,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_23)) = k3_xboole_0('#skF_3',A_23)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5407,c_26])).

tff(c_5445,plain,(
    ! [A_23] : k1_relat_1(k7_relat_1('#skF_5',A_23)) = k3_xboole_0('#skF_3',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_5428])).

tff(c_6818,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6814,c_5445])).

tff(c_6824,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2032,c_6818])).

tff(c_6482,plain,(
    ! [B_828,A_829] :
      ( k7_relat_1(B_828,k3_xboole_0(k1_relat_1(B_828),A_829)) = k7_relat_1(B_828,A_829)
      | ~ v1_relat_1(B_828) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6515,plain,(
    ! [A_829] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_829)) = k7_relat_1('#skF_5',A_829)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5407,c_6482])).

tff(c_6536,plain,(
    ! [A_829] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_829)) = k7_relat_1('#skF_5',A_829) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_6515])).

tff(c_6831,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6824,c_6536])).

tff(c_6834,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6814,c_6831])).

tff(c_6768,plain,(
    ! [A_844,B_845,C_846,D_847] :
      ( k2_partfun1(A_844,B_845,C_846,D_847) = k7_relat_1(C_846,D_847)
      | ~ m1_subset_1(C_846,k1_zfmisc_1(k2_zfmisc_1(A_844,B_845)))
      | ~ v1_funct_1(C_846) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6772,plain,(
    ! [D_847] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_847) = k7_relat_1('#skF_5',D_847)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_6768])).

tff(c_6781,plain,(
    ! [D_847] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_847) = k7_relat_1('#skF_5',D_847) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6772])).

tff(c_5416,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k9_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5407,c_16])).

tff(c_6370,plain,(
    ! [A_823] :
      ( r1_xboole_0('#skF_3',A_823)
      | k9_relat_1('#skF_5',A_823) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_5416])).

tff(c_4383,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4372])).

tff(c_4678,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4383,c_4669])).

tff(c_4687,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_4678])).

tff(c_5449,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4687])).

tff(c_6159,plain,(
    ! [C_808,A_809,B_810] :
      ( v1_partfun1(C_808,A_809)
      | ~ v1_funct_2(C_808,A_809,B_810)
      | ~ v1_funct_1(C_808)
      | ~ m1_subset_1(C_808,k1_zfmisc_1(k2_zfmisc_1(A_809,B_810)))
      | v1_xboole_0(B_810) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6162,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_6159])).

tff(c_6172,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_6162])).

tff(c_6174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5449,c_6172])).

tff(c_6175,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4687])).

tff(c_6190,plain,(
    ! [B_19] :
      ( k7_relat_1('#skF_6',B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6175,c_18])).

tff(c_6209,plain,(
    ! [B_19] :
      ( k7_relat_1('#skF_6',B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_6190])).

tff(c_6386,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6370,c_6209])).

tff(c_6682,plain,(
    k9_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6386])).

tff(c_2033,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_6716,plain,(
    ! [B_843] :
      ( k7_relat_1('#skF_5',B_843) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_843)
      | v1_xboole_0(B_843) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6549])).

tff(c_6719,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_6716])).

tff(c_6722,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_6719])).

tff(c_6729,plain,
    ( k9_relat_1('#skF_5','#skF_4') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6722,c_12])).

tff(c_6734,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2033,c_6729])).

tff(c_6736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6682,c_6734])).

tff(c_6737,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6386])).

tff(c_6196,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_23)) = k3_xboole_0('#skF_4',A_23)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6175,c_26])).

tff(c_6213,plain,(
    ! [A_23] : k1_relat_1(k7_relat_1('#skF_6',A_23)) = k3_xboole_0('#skF_4',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_6196])).

tff(c_6742,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6737,c_6213])).

tff(c_6748,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2032,c_6742])).

tff(c_6512,plain,(
    ! [A_829] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_829)) = k7_relat_1('#skF_6',A_829)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6175,c_6482])).

tff(c_6534,plain,(
    ! [A_829] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_829)) = k7_relat_1('#skF_6',A_829) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_6512])).

tff(c_6759,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6748,c_6534])).

tff(c_6762,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6737,c_6759])).

tff(c_6770,plain,(
    ! [D_847] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_847) = k7_relat_1('#skF_6',D_847)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_6768])).

tff(c_6778,plain,(
    ! [D_847] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_847) = k7_relat_1('#skF_6',D_847) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6770])).

tff(c_6317,plain,(
    ! [A_815,B_816,C_817] :
      ( k9_subset_1(A_815,B_816,C_817) = k3_xboole_0(B_816,C_817)
      | ~ m1_subset_1(C_817,k1_zfmisc_1(A_815)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6332,plain,(
    ! [B_816] : k9_subset_1('#skF_1',B_816,'#skF_4') = k3_xboole_0(B_816,'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_6317])).

tff(c_64,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_115,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_6351,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6332,c_6332,c_115])).

tff(c_9433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6834,c_6781,c_6762,c_6778,c_6824,c_6824,c_6351])).

tff(c_9434,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_54878,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9434])).

tff(c_75687,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75676,c_54878])).

tff(c_75701,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_59342,c_60010,c_60000,c_58711,c_58945,c_58711,c_62627,c_75687])).

tff(c_75703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_75701])).

tff(c_75704,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9434])).

tff(c_75707,plain,(
    ! [C_3809,A_3810,B_3811] :
      ( v4_relat_1(C_3809,A_3810)
      | ~ m1_subset_1(C_3809,k1_zfmisc_1(k2_zfmisc_1(A_3810,B_3811))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_75718,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_75707])).

tff(c_77855,plain,(
    ! [B_3983,A_3984] :
      ( k1_relat_1(B_3983) = A_3984
      | ~ v1_partfun1(B_3983,A_3984)
      | ~ v4_relat_1(B_3983,A_3984)
      | ~ v1_relat_1(B_3983) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_77864,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_75718,c_77855])).

tff(c_77873,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_77864])).

tff(c_78429,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_77873])).

tff(c_78628,plain,(
    ! [C_4037,A_4038,B_4039] :
      ( v1_partfun1(C_4037,A_4038)
      | ~ v1_funct_2(C_4037,A_4038,B_4039)
      | ~ v1_funct_1(C_4037)
      | ~ m1_subset_1(C_4037,k1_zfmisc_1(k2_zfmisc_1(A_4038,B_4039)))
      | v1_xboole_0(B_4039) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_78631,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_78628])).

tff(c_78641,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_78631])).

tff(c_78643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_78429,c_78641])).

tff(c_78644,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_77873])).

tff(c_78665,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_4',A_15)
      | k9_relat_1('#skF_6',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78644,c_16])).

tff(c_78843,plain,(
    ! [A_4050] :
      ( r1_xboole_0('#skF_4',A_4050)
      | k9_relat_1('#skF_6',A_4050) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78665])).

tff(c_75776,plain,(
    ! [A_3831,B_3832] :
      ( k7_relat_1(A_3831,B_3832) = k1_xboole_0
      | ~ r1_xboole_0(B_3832,k1_relat_1(A_3831))
      | ~ v1_relat_1(A_3831) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_75799,plain,(
    ! [B_3832] :
      ( k7_relat_1(k1_xboole_0,B_3832) = k1_xboole_0
      | ~ r1_xboole_0(B_3832,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10904,c_75776])).

tff(c_75806,plain,(
    ! [B_3832] :
      ( k7_relat_1(k1_xboole_0,B_3832) = k1_xboole_0
      | ~ r1_xboole_0(B_3832,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_75799])).

tff(c_78871,plain,
    ( k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78843,c_75806])).

tff(c_79186,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_78871])).

tff(c_10905,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9446])).

tff(c_75719,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_75707])).

tff(c_77861,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_75719,c_77855])).

tff(c_77870,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_77861])).

tff(c_77880,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_77870])).

tff(c_78357,plain,(
    ! [C_4020,A_4021,B_4022] :
      ( v1_partfun1(C_4020,A_4021)
      | ~ v1_funct_2(C_4020,A_4021,B_4022)
      | ~ v1_funct_1(C_4020)
      | ~ m1_subset_1(C_4020,k1_zfmisc_1(k2_zfmisc_1(A_4021,B_4022)))
      | v1_xboole_0(B_4022) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_78363,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_78357])).

tff(c_78374,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_78363])).

tff(c_78376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_77880,c_78374])).

tff(c_78377,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_77870])).

tff(c_78389,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_5',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_25)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78377,c_28])).

tff(c_78886,plain,(
    ! [A_4053] :
      ( k7_relat_1('#skF_5',A_4053) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_4053) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_78389])).

tff(c_78893,plain,(
    ! [B_28] :
      ( k7_relat_1('#skF_5',B_28) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_78886])).

tff(c_79091,plain,(
    ! [B_4064] :
      ( k7_relat_1('#skF_5',B_4064) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_4064)
      | v1_xboole_0(B_4064) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_78893])).

tff(c_79094,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_79091])).

tff(c_79097,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_79094])).

tff(c_78404,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | k7_relat_1('#skF_5',A_25) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78377,c_30])).

tff(c_78821,plain,(
    ! [A_4049] :
      ( r1_xboole_0('#skF_3',A_4049)
      | k7_relat_1('#skF_5',A_4049) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_78404])).

tff(c_78662,plain,(
    ! [B_19] :
      ( k7_relat_1('#skF_6',B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78644,c_18])).

tff(c_78683,plain,(
    ! [B_19] :
      ( k7_relat_1('#skF_6',B_19) = k1_xboole_0
      | ~ r1_xboole_0(B_19,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78662])).

tff(c_78837,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78821,c_78683])).

tff(c_79189,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79097,c_78837])).

tff(c_78653,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_23)) = k3_xboole_0('#skF_4',A_23)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78644,c_26])).

tff(c_78677,plain,(
    ! [A_23] : k1_relat_1(k7_relat_1('#skF_6',A_23)) = k3_xboole_0('#skF_4',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78653])).

tff(c_79193,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_79189,c_78677])).

tff(c_79199,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10904,c_79193])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,k3_xboole_0(k1_relat_1(B_21),A_20)) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78650,plain,(
    ! [A_20] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_20)) = k7_relat_1('#skF_6',A_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78644,c_20])).

tff(c_78675,plain,(
    ! [A_20] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_20)) = k7_relat_1('#skF_6',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78650])).

tff(c_79209,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_79199,c_78675])).

tff(c_79213,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79189,c_79209])).

tff(c_79238,plain,
    ( k9_relat_1('#skF_6',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_79213,c_12])).

tff(c_79243,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_10905,c_79238])).

tff(c_79245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79186,c_79243])).

tff(c_79247,plain,(
    k9_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78871])).

tff(c_78656,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_6',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_25)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78644,c_28])).

tff(c_78679,plain,(
    ! [A_25] :
      ( k7_relat_1('#skF_6',A_25) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78656])).

tff(c_79299,plain,(
    ! [A_4080] :
      ( k7_relat_1('#skF_6',A_4080) = k1_xboole_0
      | k9_relat_1('#skF_6',A_4080) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_78843,c_78679])).

tff(c_79303,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79247,c_79299])).

tff(c_78386,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_23)) = k3_xboole_0('#skF_3',A_23)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78377,c_26])).

tff(c_78410,plain,(
    ! [A_23] : k1_relat_1(k7_relat_1('#skF_5',A_23)) = k3_xboole_0('#skF_3',A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_78386])).

tff(c_79101,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_79097,c_78410])).

tff(c_79107,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10904,c_79101])).

tff(c_77793,plain,(
    ! [A_3974,B_3975,C_3976] :
      ( k9_subset_1(A_3974,B_3975,C_3976) = k3_xboole_0(B_3975,C_3976)
      | ~ m1_subset_1(C_3976,k1_zfmisc_1(A_3974)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77808,plain,(
    ! [B_3975] : k9_subset_1('#skF_1',B_3975,'#skF_4') = k3_xboole_0(B_3975,'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_77793])).

tff(c_78383,plain,(
    ! [A_20] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_20)) = k7_relat_1('#skF_5',A_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78377,c_20])).

tff(c_78408,plain,(
    ! [A_20] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_20)) = k7_relat_1('#skF_5',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_78383])).

tff(c_79114,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_79107,c_78408])).

tff(c_79117,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79097,c_79114])).

tff(c_78806,plain,(
    ! [A_4045,B_4046,C_4047,D_4048] :
      ( k2_partfun1(A_4045,B_4046,C_4047,D_4048) = k7_relat_1(C_4047,D_4048)
      | ~ m1_subset_1(C_4047,k1_zfmisc_1(k2_zfmisc_1(A_4045,B_4046)))
      | ~ v1_funct_1(C_4047) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_78808,plain,(
    ! [D_4048] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_4048) = k7_relat_1('#skF_6',D_4048)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_78806])).

tff(c_78816,plain,(
    ! [D_4048] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_4048) = k7_relat_1('#skF_6',D_4048) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_78808])).

tff(c_78810,plain,(
    ! [D_4048] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_4048) = k7_relat_1('#skF_5',D_4048)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_78806])).

tff(c_78819,plain,(
    ! [D_4048] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_4048) = k7_relat_1('#skF_5',D_4048) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78810])).

tff(c_79144,plain,(
    ! [E_4066,F_4069,A_4068,D_4067,C_4070,B_4065] :
      ( v1_funct_1(k1_tmap_1(A_4068,B_4065,C_4070,D_4067,E_4066,F_4069))
      | ~ m1_subset_1(F_4069,k1_zfmisc_1(k2_zfmisc_1(D_4067,B_4065)))
      | ~ v1_funct_2(F_4069,D_4067,B_4065)
      | ~ v1_funct_1(F_4069)
      | ~ m1_subset_1(E_4066,k1_zfmisc_1(k2_zfmisc_1(C_4070,B_4065)))
      | ~ v1_funct_2(E_4066,C_4070,B_4065)
      | ~ v1_funct_1(E_4066)
      | ~ m1_subset_1(D_4067,k1_zfmisc_1(A_4068))
      | v1_xboole_0(D_4067)
      | ~ m1_subset_1(C_4070,k1_zfmisc_1(A_4068))
      | v1_xboole_0(C_4070)
      | v1_xboole_0(B_4065)
      | v1_xboole_0(A_4068) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_79146,plain,(
    ! [A_4068,C_4070,E_4066] :
      ( v1_funct_1(k1_tmap_1(A_4068,'#skF_2',C_4070,'#skF_4',E_4066,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_4066,k1_zfmisc_1(k2_zfmisc_1(C_4070,'#skF_2')))
      | ~ v1_funct_2(E_4066,C_4070,'#skF_2')
      | ~ v1_funct_1(E_4066)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4068))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_4070,k1_zfmisc_1(A_4068))
      | v1_xboole_0(C_4070)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_4068) ) ),
    inference(resolution,[status(thm)],[c_66,c_79144])).

tff(c_79154,plain,(
    ! [A_4068,C_4070,E_4066] :
      ( v1_funct_1(k1_tmap_1(A_4068,'#skF_2',C_4070,'#skF_4',E_4066,'#skF_6'))
      | ~ m1_subset_1(E_4066,k1_zfmisc_1(k2_zfmisc_1(C_4070,'#skF_2')))
      | ~ v1_funct_2(E_4066,C_4070,'#skF_2')
      | ~ v1_funct_1(E_4066)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4068))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_4070,k1_zfmisc_1(A_4068))
      | v1_xboole_0(C_4070)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_4068) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_79146])).

tff(c_80870,plain,(
    ! [A_4151,C_4152,E_4153] :
      ( v1_funct_1(k1_tmap_1(A_4151,'#skF_2',C_4152,'#skF_4',E_4153,'#skF_6'))
      | ~ m1_subset_1(E_4153,k1_zfmisc_1(k2_zfmisc_1(C_4152,'#skF_2')))
      | ~ v1_funct_2(E_4153,C_4152,'#skF_2')
      | ~ v1_funct_1(E_4153)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4151))
      | ~ m1_subset_1(C_4152,k1_zfmisc_1(A_4151))
      | v1_xboole_0(C_4152)
      | v1_xboole_0(A_4151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_79154])).

tff(c_80877,plain,(
    ! [A_4151] :
      ( v1_funct_1(k1_tmap_1(A_4151,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4151))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4151))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4151) ) ),
    inference(resolution,[status(thm)],[c_72,c_80870])).

tff(c_80890,plain,(
    ! [A_4151] :
      ( v1_funct_1(k1_tmap_1(A_4151,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4151))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4151))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_80877])).

tff(c_81694,plain,(
    ! [A_4171] :
      ( v1_funct_1(k1_tmap_1(A_4171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4171))
      | v1_xboole_0(A_4171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80890])).

tff(c_81697,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_81694])).

tff(c_81700,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_81697])).

tff(c_81701,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_81700])).

tff(c_79614,plain,(
    ! [D_4105,A_4106,E_4107,C_4108,F_4110,B_4109] :
      ( k2_partfun1(k4_subset_1(A_4106,C_4108,D_4105),B_4109,k1_tmap_1(A_4106,B_4109,C_4108,D_4105,E_4107,F_4110),C_4108) = E_4107
      | ~ m1_subset_1(k1_tmap_1(A_4106,B_4109,C_4108,D_4105,E_4107,F_4110),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_4106,C_4108,D_4105),B_4109)))
      | ~ v1_funct_2(k1_tmap_1(A_4106,B_4109,C_4108,D_4105,E_4107,F_4110),k4_subset_1(A_4106,C_4108,D_4105),B_4109)
      | ~ v1_funct_1(k1_tmap_1(A_4106,B_4109,C_4108,D_4105,E_4107,F_4110))
      | k2_partfun1(D_4105,B_4109,F_4110,k9_subset_1(A_4106,C_4108,D_4105)) != k2_partfun1(C_4108,B_4109,E_4107,k9_subset_1(A_4106,C_4108,D_4105))
      | ~ m1_subset_1(F_4110,k1_zfmisc_1(k2_zfmisc_1(D_4105,B_4109)))
      | ~ v1_funct_2(F_4110,D_4105,B_4109)
      | ~ v1_funct_1(F_4110)
      | ~ m1_subset_1(E_4107,k1_zfmisc_1(k2_zfmisc_1(C_4108,B_4109)))
      | ~ v1_funct_2(E_4107,C_4108,B_4109)
      | ~ v1_funct_1(E_4107)
      | ~ m1_subset_1(D_4105,k1_zfmisc_1(A_4106))
      | v1_xboole_0(D_4105)
      | ~ m1_subset_1(C_4108,k1_zfmisc_1(A_4106))
      | v1_xboole_0(C_4108)
      | v1_xboole_0(B_4109)
      | v1_xboole_0(A_4106) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_86030,plain,(
    ! [F_4358,E_4355,A_4357,B_4354,D_4356,C_4359] :
      ( k2_partfun1(k4_subset_1(A_4357,C_4359,D_4356),B_4354,k1_tmap_1(A_4357,B_4354,C_4359,D_4356,E_4355,F_4358),C_4359) = E_4355
      | ~ v1_funct_2(k1_tmap_1(A_4357,B_4354,C_4359,D_4356,E_4355,F_4358),k4_subset_1(A_4357,C_4359,D_4356),B_4354)
      | ~ v1_funct_1(k1_tmap_1(A_4357,B_4354,C_4359,D_4356,E_4355,F_4358))
      | k2_partfun1(D_4356,B_4354,F_4358,k9_subset_1(A_4357,C_4359,D_4356)) != k2_partfun1(C_4359,B_4354,E_4355,k9_subset_1(A_4357,C_4359,D_4356))
      | ~ m1_subset_1(F_4358,k1_zfmisc_1(k2_zfmisc_1(D_4356,B_4354)))
      | ~ v1_funct_2(F_4358,D_4356,B_4354)
      | ~ v1_funct_1(F_4358)
      | ~ m1_subset_1(E_4355,k1_zfmisc_1(k2_zfmisc_1(C_4359,B_4354)))
      | ~ v1_funct_2(E_4355,C_4359,B_4354)
      | ~ v1_funct_1(E_4355)
      | ~ m1_subset_1(D_4356,k1_zfmisc_1(A_4357))
      | v1_xboole_0(D_4356)
      | ~ m1_subset_1(C_4359,k1_zfmisc_1(A_4357))
      | v1_xboole_0(C_4359)
      | v1_xboole_0(B_4354)
      | v1_xboole_0(A_4357) ) ),
    inference(resolution,[status(thm)],[c_58,c_79614])).

tff(c_88799,plain,(
    ! [F_4456,E_4453,D_4454,A_4455,B_4452,C_4457] :
      ( k2_partfun1(k4_subset_1(A_4455,C_4457,D_4454),B_4452,k1_tmap_1(A_4455,B_4452,C_4457,D_4454,E_4453,F_4456),C_4457) = E_4453
      | ~ v1_funct_1(k1_tmap_1(A_4455,B_4452,C_4457,D_4454,E_4453,F_4456))
      | k2_partfun1(D_4454,B_4452,F_4456,k9_subset_1(A_4455,C_4457,D_4454)) != k2_partfun1(C_4457,B_4452,E_4453,k9_subset_1(A_4455,C_4457,D_4454))
      | ~ m1_subset_1(F_4456,k1_zfmisc_1(k2_zfmisc_1(D_4454,B_4452)))
      | ~ v1_funct_2(F_4456,D_4454,B_4452)
      | ~ v1_funct_1(F_4456)
      | ~ m1_subset_1(E_4453,k1_zfmisc_1(k2_zfmisc_1(C_4457,B_4452)))
      | ~ v1_funct_2(E_4453,C_4457,B_4452)
      | ~ v1_funct_1(E_4453)
      | ~ m1_subset_1(D_4454,k1_zfmisc_1(A_4455))
      | v1_xboole_0(D_4454)
      | ~ m1_subset_1(C_4457,k1_zfmisc_1(A_4455))
      | v1_xboole_0(C_4457)
      | v1_xboole_0(B_4452)
      | v1_xboole_0(A_4455) ) ),
    inference(resolution,[status(thm)],[c_60,c_86030])).

tff(c_88803,plain,(
    ! [A_4455,C_4457,E_4453] :
      ( k2_partfun1(k4_subset_1(A_4455,C_4457,'#skF_4'),'#skF_2',k1_tmap_1(A_4455,'#skF_2',C_4457,'#skF_4',E_4453,'#skF_6'),C_4457) = E_4453
      | ~ v1_funct_1(k1_tmap_1(A_4455,'#skF_2',C_4457,'#skF_4',E_4453,'#skF_6'))
      | k2_partfun1(C_4457,'#skF_2',E_4453,k9_subset_1(A_4455,C_4457,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_4455,C_4457,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_4453,k1_zfmisc_1(k2_zfmisc_1(C_4457,'#skF_2')))
      | ~ v1_funct_2(E_4453,C_4457,'#skF_2')
      | ~ v1_funct_1(E_4453)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4455))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_4457,k1_zfmisc_1(A_4455))
      | v1_xboole_0(C_4457)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_4455) ) ),
    inference(resolution,[status(thm)],[c_66,c_88799])).

tff(c_88812,plain,(
    ! [A_4455,C_4457,E_4453] :
      ( k2_partfun1(k4_subset_1(A_4455,C_4457,'#skF_4'),'#skF_2',k1_tmap_1(A_4455,'#skF_2',C_4457,'#skF_4',E_4453,'#skF_6'),C_4457) = E_4453
      | ~ v1_funct_1(k1_tmap_1(A_4455,'#skF_2',C_4457,'#skF_4',E_4453,'#skF_6'))
      | k2_partfun1(C_4457,'#skF_2',E_4453,k9_subset_1(A_4455,C_4457,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4455,C_4457,'#skF_4'))
      | ~ m1_subset_1(E_4453,k1_zfmisc_1(k2_zfmisc_1(C_4457,'#skF_2')))
      | ~ v1_funct_2(E_4453,C_4457,'#skF_2')
      | ~ v1_funct_1(E_4453)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4455))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_4457,k1_zfmisc_1(A_4455))
      | v1_xboole_0(C_4457)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_4455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_78816,c_88803])).

tff(c_93830,plain,(
    ! [A_4545,C_4546,E_4547] :
      ( k2_partfun1(k4_subset_1(A_4545,C_4546,'#skF_4'),'#skF_2',k1_tmap_1(A_4545,'#skF_2',C_4546,'#skF_4',E_4547,'#skF_6'),C_4546) = E_4547
      | ~ v1_funct_1(k1_tmap_1(A_4545,'#skF_2',C_4546,'#skF_4',E_4547,'#skF_6'))
      | k2_partfun1(C_4546,'#skF_2',E_4547,k9_subset_1(A_4545,C_4546,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4545,C_4546,'#skF_4'))
      | ~ m1_subset_1(E_4547,k1_zfmisc_1(k2_zfmisc_1(C_4546,'#skF_2')))
      | ~ v1_funct_2(E_4547,C_4546,'#skF_2')
      | ~ v1_funct_1(E_4547)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4545))
      | ~ m1_subset_1(C_4546,k1_zfmisc_1(A_4545))
      | v1_xboole_0(C_4546)
      | v1_xboole_0(A_4545) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_88812])).

tff(c_93837,plain,(
    ! [A_4545] :
      ( k2_partfun1(k4_subset_1(A_4545,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4545,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4545,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_4545,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4545,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4545))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4545))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4545) ) ),
    inference(resolution,[status(thm)],[c_72,c_93830])).

tff(c_93850,plain,(
    ! [A_4545] :
      ( k2_partfun1(k4_subset_1(A_4545,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4545,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4545,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4545,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4545,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4545))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4545))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4545) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_78819,c_93837])).

tff(c_95468,plain,(
    ! [A_4571] :
      ( k2_partfun1(k4_subset_1(A_4571,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4571,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_4571,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4571,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4571,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4571))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4571))
      | v1_xboole_0(A_4571) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_93850])).

tff(c_75705,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9434])).

tff(c_79805,plain,(
    ! [A_4121,G_4119,C_4122,D_4120,B_4123] :
      ( k1_tmap_1(A_4121,B_4123,C_4122,D_4120,k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,C_4122),k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,D_4120)) = G_4119
      | ~ m1_subset_1(G_4119,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_4121,C_4122,D_4120),B_4123)))
      | ~ v1_funct_2(G_4119,k4_subset_1(A_4121,C_4122,D_4120),B_4123)
      | ~ v1_funct_1(G_4119)
      | k2_partfun1(D_4120,B_4123,k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,D_4120),k9_subset_1(A_4121,C_4122,D_4120)) != k2_partfun1(C_4122,B_4123,k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,C_4122),k9_subset_1(A_4121,C_4122,D_4120))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,D_4120),k1_zfmisc_1(k2_zfmisc_1(D_4120,B_4123)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,D_4120),D_4120,B_4123)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,D_4120))
      | ~ m1_subset_1(k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,C_4122),k1_zfmisc_1(k2_zfmisc_1(C_4122,B_4123)))
      | ~ v1_funct_2(k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,C_4122),C_4122,B_4123)
      | ~ v1_funct_1(k2_partfun1(k4_subset_1(A_4121,C_4122,D_4120),B_4123,G_4119,C_4122))
      | ~ m1_subset_1(D_4120,k1_zfmisc_1(A_4121))
      | v1_xboole_0(D_4120)
      | ~ m1_subset_1(C_4122,k1_zfmisc_1(A_4121))
      | v1_xboole_0(C_4122)
      | v1_xboole_0(B_4123)
      | v1_xboole_0(A_4121) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_79807,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4')) = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4'))
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75705,c_79805])).

tff(c_79809,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'))
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_70,c_75705,c_68,c_75705,c_66,c_79303,c_78816,c_75705,c_79107,c_77808,c_79107,c_77808,c_75705,c_79807])).

tff(c_79810,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_82,c_79809])).

tff(c_82688,plain,
    ( k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81701,c_79810])).

tff(c_82689,plain,(
    ~ v1_funct_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_82688])).

tff(c_95477,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_95468,c_82689])).

tff(c_95490,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_79303,c_79107,c_77808,c_79117,c_79107,c_77808,c_81701,c_76,c_95477])).

tff(c_95492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_95490])).

tff(c_95493,plain,
    ( ~ v1_funct_2(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | k2_partfun1('#skF_3','#skF_2',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')))
    | k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3'),'#skF_6') = k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_82688])).

tff(c_96326,plain,(
    ~ m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_95493])).

tff(c_97802,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_96326])).

tff(c_97805,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_76,c_74,c_72,c_70,c_68,c_66,c_97802])).

tff(c_97807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_82,c_97805])).

tff(c_97809,plain,(
    m1_subset_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_95493])).

tff(c_56,plain,(
    ! [E_165,D_157,A_45,C_141,B_109,F_169] :
      ( k2_partfun1(k4_subset_1(A_45,C_141,D_157),B_109,k1_tmap_1(A_45,B_109,C_141,D_157,E_165,F_169),C_141) = E_165
      | ~ m1_subset_1(k1_tmap_1(A_45,B_109,C_141,D_157,E_165,F_169),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_45,C_141,D_157),B_109)))
      | ~ v1_funct_2(k1_tmap_1(A_45,B_109,C_141,D_157,E_165,F_169),k4_subset_1(A_45,C_141,D_157),B_109)
      | ~ v1_funct_1(k1_tmap_1(A_45,B_109,C_141,D_157,E_165,F_169))
      | k2_partfun1(D_157,B_109,F_169,k9_subset_1(A_45,C_141,D_157)) != k2_partfun1(C_141,B_109,E_165,k9_subset_1(A_45,C_141,D_157))
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(D_157,B_109)))
      | ~ v1_funct_2(F_169,D_157,B_109)
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(C_141,B_109)))
      | ~ v1_funct_2(E_165,C_141,B_109)
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(A_45))
      | v1_xboole_0(D_157)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(A_45))
      | v1_xboole_0(C_141)
      | v1_xboole_0(B_109)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_97866,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_97809,c_56])).

tff(c_97900,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
    | ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_76,c_74,c_72,c_70,c_68,c_66,c_79303,c_79107,c_77808,c_79117,c_79107,c_77808,c_78816,c_78819,c_81701,c_97866])).

tff(c_97901,plain,(
    ~ v1_funct_2(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_82,c_75704,c_97900])).

tff(c_97942,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_97901])).

tff(c_97945,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_76,c_74,c_72,c_70,c_68,c_66,c_97942])).

tff(c_97947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_82,c_97945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.29/13.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.58/13.90  
% 23.58/13.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.58/13.90  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 23.58/13.90  
% 23.58/13.90  %Foreground sorts:
% 23.58/13.90  
% 23.58/13.90  
% 23.58/13.90  %Background operators:
% 23.58/13.90  
% 23.58/13.90  
% 23.58/13.90  %Foreground operators:
% 23.58/13.90  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 23.58/13.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.58/13.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.58/13.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.58/13.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 23.58/13.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.58/13.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.58/13.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.58/13.90  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 23.58/13.90  tff('#skF_5', type, '#skF_5': $i).
% 23.58/13.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.58/13.90  tff('#skF_6', type, '#skF_6': $i).
% 23.58/13.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 23.58/13.90  tff('#skF_2', type, '#skF_2': $i).
% 23.58/13.90  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 23.58/13.90  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 23.58/13.90  tff('#skF_3', type, '#skF_3': $i).
% 23.58/13.90  tff('#skF_1', type, '#skF_1': $i).
% 23.58/13.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 23.58/13.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.58/13.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.58/13.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.58/13.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.58/13.90  tff('#skF_4', type, '#skF_4': $i).
% 23.58/13.90  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.58/13.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.58/13.90  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 23.58/13.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 23.58/13.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.58/13.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.58/13.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.58/13.90  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 23.58/13.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.58/13.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 23.58/13.90  
% 23.90/13.95  tff(f_255, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 23.90/13.95  tff(f_213, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 23.90/13.95  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.90/13.95  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.90/13.95  tff(f_125, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 23.90/13.95  tff(f_117, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 23.90/13.95  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 23.90/13.95  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 23.90/13.95  tff(f_31, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 23.90/13.95  tff(f_73, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 23.90/13.95  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 23.90/13.95  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 23.90/13.95  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 23.90/13.95  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 23.90/13.95  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 23.90/13.95  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 23.90/13.95  tff(f_131, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 23.90/13.95  tff(f_179, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 23.90/13.95  tff(c_90, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_88, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_86, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_82, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_60, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (v1_funct_2(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k4_subset_1(A_172, C_174, D_175), B_173) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_213])).
% 23.90/13.95  tff(c_101, plain, (![C_238, A_239, B_240]: (v1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 23.90/13.95  tff(c_112, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_101])).
% 23.90/13.95  tff(c_54880, plain, (![C_2954, A_2955, B_2956]: (v4_relat_1(C_2954, A_2955) | ~m1_subset_1(C_2954, k1_zfmisc_1(k2_zfmisc_1(A_2955, B_2956))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.90/13.95  tff(c_54891, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_54880])).
% 23.90/13.95  tff(c_56954, plain, (![B_3129, A_3130]: (k1_relat_1(B_3129)=A_3130 | ~v1_partfun1(B_3129, A_3130) | ~v4_relat_1(B_3129, A_3130) | ~v1_relat_1(B_3129))), inference(cnfTransformation, [status(thm)], [f_125])).
% 23.90/13.95  tff(c_56963, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54891, c_56954])).
% 23.90/13.95  tff(c_56972, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_56963])).
% 23.90/13.95  tff(c_57886, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_56972])).
% 23.90/13.95  tff(c_58570, plain, (![C_3242, A_3243, B_3244]: (v1_partfun1(C_3242, A_3243) | ~v1_funct_2(C_3242, A_3243, B_3244) | ~v1_funct_1(C_3242) | ~m1_subset_1(C_3242, k1_zfmisc_1(k2_zfmisc_1(A_3243, B_3244))) | v1_xboole_0(B_3244))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.90/13.95  tff(c_58573, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_58570])).
% 23.90/13.95  tff(c_58583, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58573])).
% 23.90/13.95  tff(c_58585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_57886, c_58583])).
% 23.90/13.95  tff(c_58586, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_56972])).
% 23.90/13.95  tff(c_30, plain, (![B_26, A_25]: (r1_xboole_0(k1_relat_1(B_26), A_25) | k7_relat_1(B_26, A_25)!=k1_xboole_0 | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.90/13.95  tff(c_58598, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58586, c_30])).
% 23.90/13.95  tff(c_58811, plain, (![A_3259]: (r1_xboole_0('#skF_4', A_3259) | k7_relat_1('#skF_6', A_3259)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_58598])).
% 23.90/13.95  tff(c_14, plain, (![B_16, A_15]: (k9_relat_1(B_16, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 23.90/13.95  tff(c_58604, plain, (![A_15]: (k9_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58586, c_14])).
% 23.90/13.95  tff(c_58622, plain, (![A_15]: (k9_relat_1('#skF_6', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_58604])).
% 23.90/13.95  tff(c_59288, plain, (![A_3283]: (k9_relat_1('#skF_6', A_3283)=k1_xboole_0 | k7_relat_1('#skF_6', A_3283)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_58811, c_58622])).
% 23.90/13.95  tff(c_4, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.90/13.95  tff(c_114, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_101])).
% 23.90/13.95  tff(c_9436, plain, (![A_958]: (k1_relat_1(A_958)=k1_xboole_0 | k2_relat_1(A_958)!=k1_xboole_0 | ~v1_relat_1(A_958))), inference(cnfTransformation, [status(thm)], [f_73])).
% 23.90/13.95  tff(c_9446, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_114, c_9436])).
% 23.90/13.95  tff(c_9449, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9446])).
% 23.90/13.95  tff(c_78, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_34, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | ~r1_subset_1(A_27, B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.90/13.95  tff(c_10229, plain, (![C_1059, A_1060, B_1061]: (v4_relat_1(C_1059, A_1060) | ~m1_subset_1(C_1059, k1_zfmisc_1(k2_zfmisc_1(A_1060, B_1061))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.90/13.95  tff(c_10240, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_10229])).
% 23.90/13.95  tff(c_10442, plain, (![B_1103, A_1104]: (k1_relat_1(B_1103)=A_1104 | ~v1_partfun1(B_1103, A_1104) | ~v4_relat_1(B_1103, A_1104) | ~v1_relat_1(B_1103))), inference(cnfTransformation, [status(thm)], [f_125])).
% 23.90/13.95  tff(c_10451, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10240, c_10442])).
% 23.90/13.95  tff(c_10460, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_10451])).
% 23.90/13.95  tff(c_10472, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_10460])).
% 23.90/13.95  tff(c_10618, plain, (![C_1118, A_1119, B_1120]: (v1_partfun1(C_1118, A_1119) | ~v1_funct_2(C_1118, A_1119, B_1120) | ~v1_funct_1(C_1118) | ~m1_subset_1(C_1118, k1_zfmisc_1(k2_zfmisc_1(A_1119, B_1120))) | v1_xboole_0(B_1120))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.90/13.95  tff(c_10621, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_10618])).
% 23.90/13.95  tff(c_10631, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_10621])).
% 23.90/13.95  tff(c_10633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_10472, c_10631])).
% 23.90/13.95  tff(c_10634, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_10460])).
% 23.90/13.95  tff(c_18, plain, (![A_17, B_19]: (k7_relat_1(A_17, B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, k1_relat_1(A_17)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.90/13.95  tff(c_10640, plain, (![B_19]: (k7_relat_1('#skF_6', B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10634, c_18])).
% 23.90/13.95  tff(c_10793, plain, (![B_1128]: (k7_relat_1('#skF_6', B_1128)=k1_xboole_0 | ~r1_xboole_0(B_1128, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_10640])).
% 23.90/13.95  tff(c_10805, plain, (![A_27]: (k7_relat_1('#skF_6', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_34, c_10793])).
% 23.90/13.95  tff(c_10860, plain, (![A_1131]: (k7_relat_1('#skF_6', A_1131)=k1_xboole_0 | ~r1_subset_1(A_1131, '#skF_4') | v1_xboole_0(A_1131))), inference(negUnitSimplification, [status(thm)], [c_82, c_10805])).
% 23.90/13.95  tff(c_10863, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_10860])).
% 23.90/13.95  tff(c_10866, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_10863])).
% 23.90/13.95  tff(c_12, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 23.90/13.95  tff(c_10873, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10866, c_12])).
% 23.90/13.95  tff(c_10877, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_10873])).
% 23.90/13.95  tff(c_10282, plain, (![B_1080, A_1081]: (k9_relat_1(B_1080, A_1081)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_1080), A_1081) | ~v1_relat_1(B_1080))), inference(cnfTransformation, [status(thm)], [f_56])).
% 23.90/13.95  tff(c_10405, plain, (![B_1098, A_1099]: (k9_relat_1(B_1098, A_1099)=k1_xboole_0 | k7_relat_1(B_1098, A_1099)!=k1_xboole_0 | ~v1_relat_1(B_1098))), inference(resolution, [status(thm)], [c_30, c_10282])).
% 23.90/13.95  tff(c_10414, plain, (![A_1099]: (k9_relat_1('#skF_6', A_1099)=k1_xboole_0 | k7_relat_1('#skF_6', A_1099)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_112, c_10405])).
% 23.90/13.95  tff(c_10894, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10877, c_10414])).
% 23.90/13.95  tff(c_10901, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10866, c_10894])).
% 23.90/13.95  tff(c_10903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9449, c_10901])).
% 23.90/13.95  tff(c_10904, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_9446])).
% 23.90/13.95  tff(c_56812, plain, (![B_3121, A_3122]: (r1_xboole_0(k1_relat_1(B_3121), A_3122) | k7_relat_1(B_3121, A_3122)!=k1_xboole_0 | ~v1_relat_1(B_3121))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.90/13.95  tff(c_56832, plain, (![A_3122]: (r1_xboole_0(k1_xboole_0, A_3122) | k7_relat_1(k1_xboole_0, A_3122)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10904, c_56812])).
% 23.90/13.95  tff(c_56839, plain, (![A_3122]: (r1_xboole_0(k1_xboole_0, A_3122) | k7_relat_1(k1_xboole_0, A_3122)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_56832])).
% 23.90/13.95  tff(c_58610, plain, (![B_19]: (k7_relat_1('#skF_6', B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58586, c_18])).
% 23.90/13.95  tff(c_58647, plain, (![B_3246]: (k7_relat_1('#skF_6', B_3246)=k1_xboole_0 | ~r1_xboole_0(B_3246, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_58610])).
% 23.90/13.95  tff(c_58673, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_56839, c_58647])).
% 23.90/13.95  tff(c_59097, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58673])).
% 23.90/13.95  tff(c_16, plain, (![B_16, A_15]: (r1_xboole_0(k1_relat_1(B_16), A_15) | k9_relat_1(B_16, A_15)!=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 23.90/13.95  tff(c_58607, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58586, c_16])).
% 23.90/13.95  tff(c_58995, plain, (![A_3266]: (r1_xboole_0('#skF_4', A_3266) | k9_relat_1('#skF_6', A_3266)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_58607])).
% 23.90/13.95  tff(c_54895, plain, (![A_2958, B_2959]: (k7_relat_1(A_2958, B_2959)=k1_xboole_0 | ~r1_xboole_0(B_2959, k1_relat_1(A_2958)) | ~v1_relat_1(A_2958))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.90/13.95  tff(c_54898, plain, (![B_2959]: (k7_relat_1(k1_xboole_0, B_2959)=k1_xboole_0 | ~r1_xboole_0(B_2959, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10904, c_54895])).
% 23.90/13.95  tff(c_54900, plain, (![B_2959]: (k7_relat_1(k1_xboole_0, B_2959)=k1_xboole_0 | ~r1_xboole_0(B_2959, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_54898])).
% 23.90/13.95  tff(c_59028, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_58995, c_54900])).
% 23.90/13.95  tff(c_59213, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_59097, c_59028])).
% 23.90/13.95  tff(c_59299, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_59288, c_59213])).
% 23.90/13.95  tff(c_113, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_101])).
% 23.90/13.95  tff(c_54892, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_54880])).
% 23.90/13.95  tff(c_56960, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54892, c_56954])).
% 23.90/13.95  tff(c_56969, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_56960])).
% 23.90/13.95  tff(c_56983, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_56969])).
% 23.90/13.95  tff(c_57824, plain, (![C_3194, A_3195, B_3196]: (v1_partfun1(C_3194, A_3195) | ~v1_funct_2(C_3194, A_3195, B_3196) | ~v1_funct_1(C_3194) | ~m1_subset_1(C_3194, k1_zfmisc_1(k2_zfmisc_1(A_3195, B_3196))) | v1_xboole_0(B_3196))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.90/13.95  tff(c_57830, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_57824])).
% 23.90/13.95  tff(c_57841, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_57830])).
% 23.90/13.95  tff(c_57843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_56983, c_57841])).
% 23.90/13.95  tff(c_57844, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_56969])).
% 23.90/13.95  tff(c_28, plain, (![B_26, A_25]: (k7_relat_1(B_26, A_25)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 23.90/13.95  tff(c_57859, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57844, c_28])).
% 23.90/13.95  tff(c_58979, plain, (![A_3265]: (k7_relat_1('#skF_5', A_3265)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_3265))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_57859])).
% 23.90/13.95  tff(c_58989, plain, (![B_28]: (k7_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_58979])).
% 23.90/13.95  tff(c_59132, plain, (![B_3277]: (k7_relat_1('#skF_5', B_3277)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_3277) | v1_xboole_0(B_3277))), inference(negUnitSimplification, [status(thm)], [c_86, c_58989])).
% 23.90/13.95  tff(c_59135, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_59132])).
% 23.90/13.95  tff(c_59138, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_59135])).
% 23.90/13.95  tff(c_57856, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57844, c_30])).
% 23.90/13.95  tff(c_57876, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_57856])).
% 23.90/13.95  tff(c_58672, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_57876, c_58647])).
% 23.90/13.95  tff(c_59319, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_59138, c_58672])).
% 23.90/13.95  tff(c_26, plain, (![B_24, A_23]: (k3_xboole_0(k1_relat_1(B_24), A_23)=k1_relat_1(k7_relat_1(B_24, A_23)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.90/13.95  tff(c_58595, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_6', A_23))=k3_xboole_0('#skF_4', A_23) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58586, c_26])).
% 23.90/13.95  tff(c_58616, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_6', A_23))=k3_xboole_0('#skF_4', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_58595])).
% 23.90/13.95  tff(c_59323, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59319, c_58616])).
% 23.90/13.95  tff(c_59329, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10904, c_59323])).
% 23.90/13.95  tff(c_58891, plain, (![B_3262, A_3263]: (k7_relat_1(B_3262, k3_xboole_0(k1_relat_1(B_3262), A_3263))=k7_relat_1(B_3262, A_3263) | ~v1_relat_1(B_3262))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.90/13.95  tff(c_58921, plain, (![A_3263]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_3263))=k7_relat_1('#skF_6', A_3263) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58586, c_58891])).
% 23.90/13.95  tff(c_58943, plain, (![A_3263]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_3263))=k7_relat_1('#skF_6', A_3263))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_58921])).
% 23.90/13.95  tff(c_59336, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59329, c_58943])).
% 23.90/13.95  tff(c_59339, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_59319, c_59336])).
% 23.90/13.95  tff(c_59341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59299, c_59339])).
% 23.90/13.95  tff(c_59342, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_58673])).
% 23.90/13.95  tff(c_58663, plain, (![A_27]: (k7_relat_1('#skF_6', A_27)=k1_xboole_0 | ~r1_subset_1(A_27, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_34, c_58647])).
% 23.90/13.95  tff(c_59445, plain, (![A_3297]: (k7_relat_1('#skF_6', A_3297)=k1_xboole_0 | ~r1_subset_1(A_3297, '#skF_4') | v1_xboole_0(A_3297))), inference(negUnitSimplification, [status(thm)], [c_82, c_58663])).
% 23.90/13.95  tff(c_59452, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_59445])).
% 23.90/13.95  tff(c_59458, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_59452])).
% 23.90/13.95  tff(c_58618, plain, (![A_25]: (r1_xboole_0('#skF_4', A_25) | k7_relat_1('#skF_6', A_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_58598])).
% 23.90/13.95  tff(c_57868, plain, (![B_19]: (k7_relat_1('#skF_5', B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57844, c_18])).
% 23.90/13.95  tff(c_58853, plain, (![B_3261]: (k7_relat_1('#skF_5', B_3261)=k1_xboole_0 | ~r1_xboole_0(B_3261, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_57868])).
% 23.90/13.95  tff(c_58882, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k7_relat_1('#skF_6', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_58618, c_58853])).
% 23.90/13.95  tff(c_60000, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_59458, c_58882])).
% 23.90/13.95  tff(c_57853, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_5', A_23))=k3_xboole_0('#skF_3', A_23) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57844, c_26])).
% 23.90/13.95  tff(c_57874, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_5', A_23))=k3_xboole_0('#skF_3', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_57853])).
% 23.90/13.95  tff(c_60004, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60000, c_57874])).
% 23.90/13.95  tff(c_60010, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10904, c_60004])).
% 23.90/13.95  tff(c_58696, plain, (![A_3249, B_3250, C_3251]: (k9_subset_1(A_3249, B_3250, C_3251)=k3_xboole_0(B_3250, C_3251) | ~m1_subset_1(C_3251, k1_zfmisc_1(A_3249)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.90/13.95  tff(c_58711, plain, (![B_3250]: (k9_subset_1('#skF_1', B_3250, '#skF_4')=k3_xboole_0(B_3250, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_58696])).
% 23.90/13.95  tff(c_58924, plain, (![A_3263]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_3263))=k7_relat_1('#skF_5', A_3263) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57844, c_58891])).
% 23.90/13.95  tff(c_58945, plain, (![A_3263]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_3263))=k7_relat_1('#skF_5', A_3263))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_58924])).
% 23.90/13.95  tff(c_59795, plain, (![D_3322, B_3320, E_3321, C_3325, F_3324, A_3323]: (v1_funct_1(k1_tmap_1(A_3323, B_3320, C_3325, D_3322, E_3321, F_3324)) | ~m1_subset_1(F_3324, k1_zfmisc_1(k2_zfmisc_1(D_3322, B_3320))) | ~v1_funct_2(F_3324, D_3322, B_3320) | ~v1_funct_1(F_3324) | ~m1_subset_1(E_3321, k1_zfmisc_1(k2_zfmisc_1(C_3325, B_3320))) | ~v1_funct_2(E_3321, C_3325, B_3320) | ~v1_funct_1(E_3321) | ~m1_subset_1(D_3322, k1_zfmisc_1(A_3323)) | v1_xboole_0(D_3322) | ~m1_subset_1(C_3325, k1_zfmisc_1(A_3323)) | v1_xboole_0(C_3325) | v1_xboole_0(B_3320) | v1_xboole_0(A_3323))), inference(cnfTransformation, [status(thm)], [f_213])).
% 23.90/13.95  tff(c_59797, plain, (![A_3323, C_3325, E_3321]: (v1_funct_1(k1_tmap_1(A_3323, '#skF_2', C_3325, '#skF_4', E_3321, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3321, k1_zfmisc_1(k2_zfmisc_1(C_3325, '#skF_2'))) | ~v1_funct_2(E_3321, C_3325, '#skF_2') | ~v1_funct_1(E_3321) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3323)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3325, k1_zfmisc_1(A_3323)) | v1_xboole_0(C_3325) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3323))), inference(resolution, [status(thm)], [c_66, c_59795])).
% 23.90/13.95  tff(c_59805, plain, (![A_3323, C_3325, E_3321]: (v1_funct_1(k1_tmap_1(A_3323, '#skF_2', C_3325, '#skF_4', E_3321, '#skF_6')) | ~m1_subset_1(E_3321, k1_zfmisc_1(k2_zfmisc_1(C_3325, '#skF_2'))) | ~v1_funct_2(E_3321, C_3325, '#skF_2') | ~v1_funct_1(E_3321) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3323)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3325, k1_zfmisc_1(A_3323)) | v1_xboole_0(C_3325) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3323))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_59797])).
% 23.90/13.95  tff(c_61694, plain, (![A_3407, C_3408, E_3409]: (v1_funct_1(k1_tmap_1(A_3407, '#skF_2', C_3408, '#skF_4', E_3409, '#skF_6')) | ~m1_subset_1(E_3409, k1_zfmisc_1(k2_zfmisc_1(C_3408, '#skF_2'))) | ~v1_funct_2(E_3409, C_3408, '#skF_2') | ~v1_funct_1(E_3409) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3407)) | ~m1_subset_1(C_3408, k1_zfmisc_1(A_3407)) | v1_xboole_0(C_3408) | v1_xboole_0(A_3407))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_59805])).
% 23.90/13.95  tff(c_61701, plain, (![A_3407]: (v1_funct_1(k1_tmap_1(A_3407, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3407)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3407)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3407))), inference(resolution, [status(thm)], [c_72, c_61694])).
% 23.90/13.95  tff(c_61714, plain, (![A_3407]: (v1_funct_1(k1_tmap_1(A_3407, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3407)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3407)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3407))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_61701])).
% 23.90/13.95  tff(c_62620, plain, (![A_3426]: (v1_funct_1(k1_tmap_1(A_3426, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3426)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3426)) | v1_xboole_0(A_3426))), inference(negUnitSimplification, [status(thm)], [c_86, c_61714])).
% 23.90/13.95  tff(c_62623, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_62620])).
% 23.90/13.95  tff(c_62626, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_62623])).
% 23.90/13.95  tff(c_62627, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_90, c_62626])).
% 23.90/13.95  tff(c_59391, plain, (![A_3291, B_3292, C_3293, D_3294]: (k2_partfun1(A_3291, B_3292, C_3293, D_3294)=k7_relat_1(C_3293, D_3294) | ~m1_subset_1(C_3293, k1_zfmisc_1(k2_zfmisc_1(A_3291, B_3292))) | ~v1_funct_1(C_3293))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.90/13.95  tff(c_59395, plain, (![D_3294]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_3294)=k7_relat_1('#skF_5', D_3294) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_59391])).
% 23.90/13.95  tff(c_59404, plain, (![D_3294]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_3294)=k7_relat_1('#skF_5', D_3294))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_59395])).
% 23.90/13.95  tff(c_59393, plain, (![D_3294]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_3294)=k7_relat_1('#skF_6', D_3294) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_59391])).
% 23.90/13.95  tff(c_59401, plain, (![D_3294]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_3294)=k7_relat_1('#skF_6', D_3294))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_59393])).
% 23.90/13.95  tff(c_58, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (m1_subset_1(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172, C_174, D_175), B_173))) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_213])).
% 23.90/13.95  tff(c_60084, plain, (![A_3346, C_3348, B_3349, E_3347, F_3350, D_3345]: (k2_partfun1(k4_subset_1(A_3346, C_3348, D_3345), B_3349, k1_tmap_1(A_3346, B_3349, C_3348, D_3345, E_3347, F_3350), D_3345)=F_3350 | ~m1_subset_1(k1_tmap_1(A_3346, B_3349, C_3348, D_3345, E_3347, F_3350), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3346, C_3348, D_3345), B_3349))) | ~v1_funct_2(k1_tmap_1(A_3346, B_3349, C_3348, D_3345, E_3347, F_3350), k4_subset_1(A_3346, C_3348, D_3345), B_3349) | ~v1_funct_1(k1_tmap_1(A_3346, B_3349, C_3348, D_3345, E_3347, F_3350)) | k2_partfun1(D_3345, B_3349, F_3350, k9_subset_1(A_3346, C_3348, D_3345))!=k2_partfun1(C_3348, B_3349, E_3347, k9_subset_1(A_3346, C_3348, D_3345)) | ~m1_subset_1(F_3350, k1_zfmisc_1(k2_zfmisc_1(D_3345, B_3349))) | ~v1_funct_2(F_3350, D_3345, B_3349) | ~v1_funct_1(F_3350) | ~m1_subset_1(E_3347, k1_zfmisc_1(k2_zfmisc_1(C_3348, B_3349))) | ~v1_funct_2(E_3347, C_3348, B_3349) | ~v1_funct_1(E_3347) | ~m1_subset_1(D_3345, k1_zfmisc_1(A_3346)) | v1_xboole_0(D_3345) | ~m1_subset_1(C_3348, k1_zfmisc_1(A_3346)) | v1_xboole_0(C_3348) | v1_xboole_0(B_3349) | v1_xboole_0(A_3346))), inference(cnfTransformation, [status(thm)], [f_179])).
% 23.90/13.95  tff(c_66690, plain, (![D_3618, F_3620, A_3619, C_3621, E_3617, B_3616]: (k2_partfun1(k4_subset_1(A_3619, C_3621, D_3618), B_3616, k1_tmap_1(A_3619, B_3616, C_3621, D_3618, E_3617, F_3620), D_3618)=F_3620 | ~v1_funct_2(k1_tmap_1(A_3619, B_3616, C_3621, D_3618, E_3617, F_3620), k4_subset_1(A_3619, C_3621, D_3618), B_3616) | ~v1_funct_1(k1_tmap_1(A_3619, B_3616, C_3621, D_3618, E_3617, F_3620)) | k2_partfun1(D_3618, B_3616, F_3620, k9_subset_1(A_3619, C_3621, D_3618))!=k2_partfun1(C_3621, B_3616, E_3617, k9_subset_1(A_3619, C_3621, D_3618)) | ~m1_subset_1(F_3620, k1_zfmisc_1(k2_zfmisc_1(D_3618, B_3616))) | ~v1_funct_2(F_3620, D_3618, B_3616) | ~v1_funct_1(F_3620) | ~m1_subset_1(E_3617, k1_zfmisc_1(k2_zfmisc_1(C_3621, B_3616))) | ~v1_funct_2(E_3617, C_3621, B_3616) | ~v1_funct_1(E_3617) | ~m1_subset_1(D_3618, k1_zfmisc_1(A_3619)) | v1_xboole_0(D_3618) | ~m1_subset_1(C_3621, k1_zfmisc_1(A_3619)) | v1_xboole_0(C_3621) | v1_xboole_0(B_3616) | v1_xboole_0(A_3619))), inference(resolution, [status(thm)], [c_58, c_60084])).
% 23.90/13.95  tff(c_69864, plain, (![D_3723, A_3724, C_3726, E_3722, F_3725, B_3721]: (k2_partfun1(k4_subset_1(A_3724, C_3726, D_3723), B_3721, k1_tmap_1(A_3724, B_3721, C_3726, D_3723, E_3722, F_3725), D_3723)=F_3725 | ~v1_funct_1(k1_tmap_1(A_3724, B_3721, C_3726, D_3723, E_3722, F_3725)) | k2_partfun1(D_3723, B_3721, F_3725, k9_subset_1(A_3724, C_3726, D_3723))!=k2_partfun1(C_3726, B_3721, E_3722, k9_subset_1(A_3724, C_3726, D_3723)) | ~m1_subset_1(F_3725, k1_zfmisc_1(k2_zfmisc_1(D_3723, B_3721))) | ~v1_funct_2(F_3725, D_3723, B_3721) | ~v1_funct_1(F_3725) | ~m1_subset_1(E_3722, k1_zfmisc_1(k2_zfmisc_1(C_3726, B_3721))) | ~v1_funct_2(E_3722, C_3726, B_3721) | ~v1_funct_1(E_3722) | ~m1_subset_1(D_3723, k1_zfmisc_1(A_3724)) | v1_xboole_0(D_3723) | ~m1_subset_1(C_3726, k1_zfmisc_1(A_3724)) | v1_xboole_0(C_3726) | v1_xboole_0(B_3721) | v1_xboole_0(A_3724))), inference(resolution, [status(thm)], [c_60, c_66690])).
% 23.90/13.95  tff(c_69868, plain, (![A_3724, C_3726, E_3722]: (k2_partfun1(k4_subset_1(A_3724, C_3726, '#skF_4'), '#skF_2', k1_tmap_1(A_3724, '#skF_2', C_3726, '#skF_4', E_3722, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3724, '#skF_2', C_3726, '#skF_4', E_3722, '#skF_6')) | k2_partfun1(C_3726, '#skF_2', E_3722, k9_subset_1(A_3724, C_3726, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_3724, C_3726, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3722, k1_zfmisc_1(k2_zfmisc_1(C_3726, '#skF_2'))) | ~v1_funct_2(E_3722, C_3726, '#skF_2') | ~v1_funct_1(E_3722) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3724)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3726, k1_zfmisc_1(A_3724)) | v1_xboole_0(C_3726) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3724))), inference(resolution, [status(thm)], [c_66, c_69864])).
% 23.90/13.95  tff(c_69877, plain, (![A_3724, C_3726, E_3722]: (k2_partfun1(k4_subset_1(A_3724, C_3726, '#skF_4'), '#skF_2', k1_tmap_1(A_3724, '#skF_2', C_3726, '#skF_4', E_3722, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3724, '#skF_2', C_3726, '#skF_4', E_3722, '#skF_6')) | k2_partfun1(C_3726, '#skF_2', E_3722, k9_subset_1(A_3724, C_3726, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3724, C_3726, '#skF_4')) | ~m1_subset_1(E_3722, k1_zfmisc_1(k2_zfmisc_1(C_3726, '#skF_2'))) | ~v1_funct_2(E_3722, C_3726, '#skF_2') | ~v1_funct_1(E_3722) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3724)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3726, k1_zfmisc_1(A_3724)) | v1_xboole_0(C_3726) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3724))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_59401, c_69868])).
% 23.90/13.95  tff(c_71756, plain, (![A_3767, C_3768, E_3769]: (k2_partfun1(k4_subset_1(A_3767, C_3768, '#skF_4'), '#skF_2', k1_tmap_1(A_3767, '#skF_2', C_3768, '#skF_4', E_3769, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3767, '#skF_2', C_3768, '#skF_4', E_3769, '#skF_6')) | k2_partfun1(C_3768, '#skF_2', E_3769, k9_subset_1(A_3767, C_3768, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3767, C_3768, '#skF_4')) | ~m1_subset_1(E_3769, k1_zfmisc_1(k2_zfmisc_1(C_3768, '#skF_2'))) | ~v1_funct_2(E_3769, C_3768, '#skF_2') | ~v1_funct_1(E_3769) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3767)) | ~m1_subset_1(C_3768, k1_zfmisc_1(A_3767)) | v1_xboole_0(C_3768) | v1_xboole_0(A_3767))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_69877])).
% 23.90/13.95  tff(c_71763, plain, (![A_3767]: (k2_partfun1(k4_subset_1(A_3767, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3767, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3767, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_3767, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3767, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3767)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3767)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3767))), inference(resolution, [status(thm)], [c_72, c_71756])).
% 23.90/13.95  tff(c_71776, plain, (![A_3767]: (k2_partfun1(k4_subset_1(A_3767, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3767, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3767, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_3767, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3767, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3767)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3767)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3767))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_59404, c_71763])).
% 23.90/13.95  tff(c_75676, plain, (![A_3807]: (k2_partfun1(k4_subset_1(A_3807, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_3807, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3807, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_3807, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3807, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3807)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3807)) | v1_xboole_0(A_3807))), inference(negUnitSimplification, [status(thm)], [c_86, c_71776])).
% 23.90/13.95  tff(c_4372, plain, (![C_656, A_657, B_658]: (v4_relat_1(C_656, A_657) | ~m1_subset_1(C_656, k1_zfmisc_1(k2_zfmisc_1(A_657, B_658))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.90/13.95  tff(c_4384, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_4372])).
% 23.90/13.95  tff(c_4669, plain, (![B_700, A_701]: (k1_relat_1(B_700)=A_701 | ~v1_partfun1(B_700, A_701) | ~v4_relat_1(B_700, A_701) | ~v1_relat_1(B_700))), inference(cnfTransformation, [status(thm)], [f_125])).
% 23.90/13.95  tff(c_4675, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4384, c_4669])).
% 23.90/13.95  tff(c_4684, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_4675])).
% 23.90/13.95  tff(c_4694, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_4684])).
% 23.90/13.95  tff(c_5387, plain, (![C_761, A_762, B_763]: (v1_partfun1(C_761, A_762) | ~v1_funct_2(C_761, A_762, B_763) | ~v1_funct_1(C_761) | ~m1_subset_1(C_761, k1_zfmisc_1(k2_zfmisc_1(A_762, B_763))) | v1_xboole_0(B_763))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.90/13.95  tff(c_5393, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_5387])).
% 23.90/13.95  tff(c_5404, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_5393])).
% 23.90/13.95  tff(c_5406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_4694, c_5404])).
% 23.90/13.95  tff(c_5407, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_4684])).
% 23.90/13.95  tff(c_5419, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5407, c_28])).
% 23.90/13.95  tff(c_6539, plain, (![A_830]: (k7_relat_1('#skF_5', A_830)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_830))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_5419])).
% 23.90/13.95  tff(c_6549, plain, (![B_28]: (k7_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_6539])).
% 23.90/13.95  tff(c_6808, plain, (![B_848]: (k7_relat_1('#skF_5', B_848)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_848) | v1_xboole_0(B_848))), inference(negUnitSimplification, [status(thm)], [c_86, c_6549])).
% 23.90/13.95  tff(c_6811, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_6808])).
% 23.90/13.95  tff(c_6814, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_6811])).
% 23.90/13.95  tff(c_116, plain, (![A_241]: (k1_relat_1(A_241)=k1_xboole_0 | k2_relat_1(A_241)!=k1_xboole_0 | ~v1_relat_1(A_241))), inference(cnfTransformation, [status(thm)], [f_73])).
% 23.90/13.95  tff(c_126, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_114, c_116])).
% 23.90/13.95  tff(c_129, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126])).
% 23.90/13.95  tff(c_998, plain, (![C_344, A_345, B_346]: (v4_relat_1(C_344, A_345) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.90/13.95  tff(c_1010, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_998])).
% 23.90/13.95  tff(c_1250, plain, (![B_396, A_397]: (k1_relat_1(B_396)=A_397 | ~v1_partfun1(B_396, A_397) | ~v4_relat_1(B_396, A_397) | ~v1_relat_1(B_396))), inference(cnfTransformation, [status(thm)], [f_125])).
% 23.90/13.95  tff(c_1256, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1010, c_1250])).
% 23.90/13.95  tff(c_1265, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1256])).
% 23.90/13.95  tff(c_1275, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1265])).
% 23.90/13.95  tff(c_1803, plain, (![C_435, A_436, B_437]: (v1_partfun1(C_435, A_436) | ~v1_funct_2(C_435, A_436, B_437) | ~v1_funct_1(C_435) | ~m1_subset_1(C_435, k1_zfmisc_1(k2_zfmisc_1(A_436, B_437))) | v1_xboole_0(B_437))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.90/13.95  tff(c_1809, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_1803])).
% 23.90/13.95  tff(c_1820, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1809])).
% 23.90/13.95  tff(c_1822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1275, c_1820])).
% 23.90/13.95  tff(c_1823, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1265])).
% 23.90/13.95  tff(c_1835, plain, (![A_15]: (k9_relat_1('#skF_5', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1823, c_14])).
% 23.90/13.95  tff(c_1962, plain, (![A_443]: (k9_relat_1('#skF_5', A_443)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_443))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1835])).
% 23.90/13.95  tff(c_1969, plain, (![B_28]: (k9_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_1962])).
% 23.90/13.95  tff(c_1995, plain, (![B_445]: (k9_relat_1('#skF_5', B_445)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_445) | v1_xboole_0(B_445))), inference(negUnitSimplification, [status(thm)], [c_86, c_1969])).
% 23.90/13.95  tff(c_1998, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1995])).
% 23.90/13.95  tff(c_2001, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_1998])).
% 23.90/13.95  tff(c_1099, plain, (![B_376, A_377]: (r1_xboole_0(k1_relat_1(B_376), A_377) | k9_relat_1(B_376, A_377)!=k1_xboole_0 | ~v1_relat_1(B_376))), inference(cnfTransformation, [status(thm)], [f_56])).
% 23.90/13.95  tff(c_1115, plain, (![B_376, A_377]: (k7_relat_1(B_376, A_377)=k1_xboole_0 | k9_relat_1(B_376, A_377)!=k1_xboole_0 | ~v1_relat_1(B_376))), inference(resolution, [status(thm)], [c_1099, c_28])).
% 23.90/13.95  tff(c_2007, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2001, c_1115])).
% 23.90/13.95  tff(c_2016, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2007])).
% 23.90/13.95  tff(c_2025, plain, (k9_relat_1('#skF_5', '#skF_4')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2016, c_12])).
% 23.90/13.95  tff(c_2029, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2001, c_2025])).
% 23.90/13.95  tff(c_2031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_2029])).
% 23.90/13.95  tff(c_2032, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 23.90/13.95  tff(c_5428, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_5', A_23))=k3_xboole_0('#skF_3', A_23) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5407, c_26])).
% 23.90/13.95  tff(c_5445, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_5', A_23))=k3_xboole_0('#skF_3', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_5428])).
% 23.90/13.95  tff(c_6818, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6814, c_5445])).
% 23.90/13.95  tff(c_6824, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2032, c_6818])).
% 23.90/13.95  tff(c_6482, plain, (![B_828, A_829]: (k7_relat_1(B_828, k3_xboole_0(k1_relat_1(B_828), A_829))=k7_relat_1(B_828, A_829) | ~v1_relat_1(B_828))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.90/13.95  tff(c_6515, plain, (![A_829]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_829))=k7_relat_1('#skF_5', A_829) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5407, c_6482])).
% 23.90/13.95  tff(c_6536, plain, (![A_829]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_829))=k7_relat_1('#skF_5', A_829))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_6515])).
% 23.90/13.95  tff(c_6831, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6824, c_6536])).
% 23.90/13.95  tff(c_6834, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6814, c_6831])).
% 23.90/13.95  tff(c_6768, plain, (![A_844, B_845, C_846, D_847]: (k2_partfun1(A_844, B_845, C_846, D_847)=k7_relat_1(C_846, D_847) | ~m1_subset_1(C_846, k1_zfmisc_1(k2_zfmisc_1(A_844, B_845))) | ~v1_funct_1(C_846))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.90/13.95  tff(c_6772, plain, (![D_847]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_847)=k7_relat_1('#skF_5', D_847) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_6768])).
% 23.90/13.95  tff(c_6781, plain, (![D_847]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_847)=k7_relat_1('#skF_5', D_847))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6772])).
% 23.90/13.95  tff(c_5416, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k9_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5407, c_16])).
% 23.90/13.95  tff(c_6370, plain, (![A_823]: (r1_xboole_0('#skF_3', A_823) | k9_relat_1('#skF_5', A_823)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_5416])).
% 23.90/13.95  tff(c_4383, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_4372])).
% 23.90/13.95  tff(c_4678, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4383, c_4669])).
% 23.90/13.95  tff(c_4687, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_4678])).
% 23.90/13.95  tff(c_5449, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_4687])).
% 23.90/13.95  tff(c_6159, plain, (![C_808, A_809, B_810]: (v1_partfun1(C_808, A_809) | ~v1_funct_2(C_808, A_809, B_810) | ~v1_funct_1(C_808) | ~m1_subset_1(C_808, k1_zfmisc_1(k2_zfmisc_1(A_809, B_810))) | v1_xboole_0(B_810))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.90/13.95  tff(c_6162, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_6159])).
% 23.90/13.95  tff(c_6172, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_6162])).
% 23.90/13.95  tff(c_6174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_5449, c_6172])).
% 23.90/13.95  tff(c_6175, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_4687])).
% 23.90/13.95  tff(c_6190, plain, (![B_19]: (k7_relat_1('#skF_6', B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6175, c_18])).
% 23.90/13.95  tff(c_6209, plain, (![B_19]: (k7_relat_1('#skF_6', B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_6190])).
% 23.90/13.95  tff(c_6386, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6370, c_6209])).
% 23.90/13.95  tff(c_6682, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6386])).
% 23.90/13.95  tff(c_2033, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 23.90/13.95  tff(c_6716, plain, (![B_843]: (k7_relat_1('#skF_5', B_843)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_843) | v1_xboole_0(B_843))), inference(negUnitSimplification, [status(thm)], [c_86, c_6549])).
% 23.90/13.95  tff(c_6719, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_6716])).
% 23.90/13.95  tff(c_6722, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_6719])).
% 23.90/13.95  tff(c_6729, plain, (k9_relat_1('#skF_5', '#skF_4')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6722, c_12])).
% 23.90/13.95  tff(c_6734, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2033, c_6729])).
% 23.90/13.95  tff(c_6736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6682, c_6734])).
% 23.90/13.95  tff(c_6737, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6386])).
% 23.90/13.95  tff(c_6196, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_6', A_23))=k3_xboole_0('#skF_4', A_23) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6175, c_26])).
% 23.90/13.95  tff(c_6213, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_6', A_23))=k3_xboole_0('#skF_4', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_6196])).
% 23.90/13.95  tff(c_6742, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6737, c_6213])).
% 23.90/13.95  tff(c_6748, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2032, c_6742])).
% 23.90/13.95  tff(c_6512, plain, (![A_829]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_829))=k7_relat_1('#skF_6', A_829) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6175, c_6482])).
% 23.90/13.95  tff(c_6534, plain, (![A_829]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_829))=k7_relat_1('#skF_6', A_829))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_6512])).
% 23.90/13.95  tff(c_6759, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6748, c_6534])).
% 23.90/13.95  tff(c_6762, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6737, c_6759])).
% 23.90/13.95  tff(c_6770, plain, (![D_847]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_847)=k7_relat_1('#skF_6', D_847) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_6768])).
% 23.90/13.95  tff(c_6778, plain, (![D_847]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_847)=k7_relat_1('#skF_6', D_847))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6770])).
% 23.90/13.95  tff(c_6317, plain, (![A_815, B_816, C_817]: (k9_subset_1(A_815, B_816, C_817)=k3_xboole_0(B_816, C_817) | ~m1_subset_1(C_817, k1_zfmisc_1(A_815)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.90/13.95  tff(c_6332, plain, (![B_816]: (k9_subset_1('#skF_1', B_816, '#skF_4')=k3_xboole_0(B_816, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_6317])).
% 23.90/13.95  tff(c_64, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 23.90/13.95  tff(c_115, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_64])).
% 23.90/13.95  tff(c_6351, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6332, c_6332, c_115])).
% 23.90/13.95  tff(c_9433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6834, c_6781, c_6762, c_6778, c_6824, c_6824, c_6351])).
% 23.90/13.95  tff(c_9434, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 23.90/13.95  tff(c_54878, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_9434])).
% 23.90/13.95  tff(c_75687, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75676, c_54878])).
% 23.90/13.95  tff(c_75701, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_59342, c_60010, c_60000, c_58711, c_58945, c_58711, c_62627, c_75687])).
% 23.90/13.95  tff(c_75703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_75701])).
% 23.90/13.95  tff(c_75704, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_9434])).
% 23.90/13.95  tff(c_75707, plain, (![C_3809, A_3810, B_3811]: (v4_relat_1(C_3809, A_3810) | ~m1_subset_1(C_3809, k1_zfmisc_1(k2_zfmisc_1(A_3810, B_3811))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.90/13.95  tff(c_75718, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_75707])).
% 23.90/13.95  tff(c_77855, plain, (![B_3983, A_3984]: (k1_relat_1(B_3983)=A_3984 | ~v1_partfun1(B_3983, A_3984) | ~v4_relat_1(B_3983, A_3984) | ~v1_relat_1(B_3983))), inference(cnfTransformation, [status(thm)], [f_125])).
% 23.90/13.95  tff(c_77864, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_75718, c_77855])).
% 23.90/13.95  tff(c_77873, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_77864])).
% 23.90/13.95  tff(c_78429, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_77873])).
% 23.90/13.95  tff(c_78628, plain, (![C_4037, A_4038, B_4039]: (v1_partfun1(C_4037, A_4038) | ~v1_funct_2(C_4037, A_4038, B_4039) | ~v1_funct_1(C_4037) | ~m1_subset_1(C_4037, k1_zfmisc_1(k2_zfmisc_1(A_4038, B_4039))) | v1_xboole_0(B_4039))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.90/13.95  tff(c_78631, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_78628])).
% 23.90/13.95  tff(c_78641, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_78631])).
% 23.90/13.95  tff(c_78643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_78429, c_78641])).
% 23.90/13.95  tff(c_78644, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_77873])).
% 23.90/13.95  tff(c_78665, plain, (![A_15]: (r1_xboole_0('#skF_4', A_15) | k9_relat_1('#skF_6', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_78644, c_16])).
% 23.90/13.95  tff(c_78843, plain, (![A_4050]: (r1_xboole_0('#skF_4', A_4050) | k9_relat_1('#skF_6', A_4050)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78665])).
% 23.90/13.95  tff(c_75776, plain, (![A_3831, B_3832]: (k7_relat_1(A_3831, B_3832)=k1_xboole_0 | ~r1_xboole_0(B_3832, k1_relat_1(A_3831)) | ~v1_relat_1(A_3831))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.90/13.95  tff(c_75799, plain, (![B_3832]: (k7_relat_1(k1_xboole_0, B_3832)=k1_xboole_0 | ~r1_xboole_0(B_3832, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10904, c_75776])).
% 23.90/13.95  tff(c_75806, plain, (![B_3832]: (k7_relat_1(k1_xboole_0, B_3832)=k1_xboole_0 | ~r1_xboole_0(B_3832, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_75799])).
% 23.90/13.95  tff(c_78871, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_78843, c_75806])).
% 23.90/13.95  tff(c_79186, plain, (k9_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_78871])).
% 23.90/13.95  tff(c_10905, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_9446])).
% 23.90/13.95  tff(c_75719, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_75707])).
% 23.90/13.95  tff(c_77861, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_75719, c_77855])).
% 23.90/13.95  tff(c_77870, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_77861])).
% 23.90/13.95  tff(c_77880, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_77870])).
% 23.90/13.95  tff(c_78357, plain, (![C_4020, A_4021, B_4022]: (v1_partfun1(C_4020, A_4021) | ~v1_funct_2(C_4020, A_4021, B_4022) | ~v1_funct_1(C_4020) | ~m1_subset_1(C_4020, k1_zfmisc_1(k2_zfmisc_1(A_4021, B_4022))) | v1_xboole_0(B_4022))), inference(cnfTransformation, [status(thm)], [f_117])).
% 23.90/13.95  tff(c_78363, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_78357])).
% 23.90/13.95  tff(c_78374, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_78363])).
% 23.90/13.95  tff(c_78376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_77880, c_78374])).
% 23.90/13.95  tff(c_78377, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_77870])).
% 23.90/13.95  tff(c_78389, plain, (![A_25]: (k7_relat_1('#skF_5', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_25) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_78377, c_28])).
% 23.90/13.95  tff(c_78886, plain, (![A_4053]: (k7_relat_1('#skF_5', A_4053)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_4053))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_78389])).
% 23.90/13.95  tff(c_78893, plain, (![B_28]: (k7_relat_1('#skF_5', B_28)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_28) | v1_xboole_0(B_28) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_78886])).
% 23.90/13.95  tff(c_79091, plain, (![B_4064]: (k7_relat_1('#skF_5', B_4064)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_4064) | v1_xboole_0(B_4064))), inference(negUnitSimplification, [status(thm)], [c_86, c_78893])).
% 23.90/13.95  tff(c_79094, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_79091])).
% 23.90/13.95  tff(c_79097, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_79094])).
% 23.90/13.95  tff(c_78404, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | k7_relat_1('#skF_5', A_25)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_78377, c_30])).
% 23.90/13.95  tff(c_78821, plain, (![A_4049]: (r1_xboole_0('#skF_3', A_4049) | k7_relat_1('#skF_5', A_4049)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_78404])).
% 23.90/13.95  tff(c_78662, plain, (![B_19]: (k7_relat_1('#skF_6', B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_78644, c_18])).
% 23.90/13.95  tff(c_78683, plain, (![B_19]: (k7_relat_1('#skF_6', B_19)=k1_xboole_0 | ~r1_xboole_0(B_19, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78662])).
% 23.90/13.95  tff(c_78837, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_78821, c_78683])).
% 23.90/13.95  tff(c_79189, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79097, c_78837])).
% 23.90/13.95  tff(c_78653, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_6', A_23))=k3_xboole_0('#skF_4', A_23) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_78644, c_26])).
% 23.90/13.95  tff(c_78677, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_6', A_23))=k3_xboole_0('#skF_4', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78653])).
% 23.90/13.95  tff(c_79193, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79189, c_78677])).
% 23.90/13.95  tff(c_79199, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10904, c_79193])).
% 23.90/13.95  tff(c_20, plain, (![B_21, A_20]: (k7_relat_1(B_21, k3_xboole_0(k1_relat_1(B_21), A_20))=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.90/13.95  tff(c_78650, plain, (![A_20]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_20))=k7_relat_1('#skF_6', A_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_78644, c_20])).
% 23.90/13.95  tff(c_78675, plain, (![A_20]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_20))=k7_relat_1('#skF_6', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78650])).
% 23.90/13.95  tff(c_79209, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_79199, c_78675])).
% 23.90/13.95  tff(c_79213, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79189, c_79209])).
% 23.90/13.95  tff(c_79238, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_79213, c_12])).
% 23.90/13.95  tff(c_79243, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_112, c_10905, c_79238])).
% 23.90/13.95  tff(c_79245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79186, c_79243])).
% 23.90/13.95  tff(c_79247, plain, (k9_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_78871])).
% 23.90/13.95  tff(c_78656, plain, (![A_25]: (k7_relat_1('#skF_6', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_25) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_78644, c_28])).
% 23.90/13.95  tff(c_78679, plain, (![A_25]: (k7_relat_1('#skF_6', A_25)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_25))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78656])).
% 23.90/13.95  tff(c_79299, plain, (![A_4080]: (k7_relat_1('#skF_6', A_4080)=k1_xboole_0 | k9_relat_1('#skF_6', A_4080)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_78843, c_78679])).
% 23.90/13.95  tff(c_79303, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_79247, c_79299])).
% 23.90/13.95  tff(c_78386, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_5', A_23))=k3_xboole_0('#skF_3', A_23) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_78377, c_26])).
% 23.90/13.95  tff(c_78410, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_5', A_23))=k3_xboole_0('#skF_3', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_78386])).
% 23.90/13.95  tff(c_79101, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79097, c_78410])).
% 23.90/13.95  tff(c_79107, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10904, c_79101])).
% 23.90/13.95  tff(c_77793, plain, (![A_3974, B_3975, C_3976]: (k9_subset_1(A_3974, B_3975, C_3976)=k3_xboole_0(B_3975, C_3976) | ~m1_subset_1(C_3976, k1_zfmisc_1(A_3974)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.90/13.95  tff(c_77808, plain, (![B_3975]: (k9_subset_1('#skF_1', B_3975, '#skF_4')=k3_xboole_0(B_3975, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_77793])).
% 23.90/13.95  tff(c_78383, plain, (![A_20]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_20))=k7_relat_1('#skF_5', A_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_78377, c_20])).
% 23.90/13.95  tff(c_78408, plain, (![A_20]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_20))=k7_relat_1('#skF_5', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_78383])).
% 23.90/13.95  tff(c_79114, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_79107, c_78408])).
% 23.90/13.95  tff(c_79117, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79097, c_79114])).
% 23.90/13.95  tff(c_78806, plain, (![A_4045, B_4046, C_4047, D_4048]: (k2_partfun1(A_4045, B_4046, C_4047, D_4048)=k7_relat_1(C_4047, D_4048) | ~m1_subset_1(C_4047, k1_zfmisc_1(k2_zfmisc_1(A_4045, B_4046))) | ~v1_funct_1(C_4047))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.90/13.95  tff(c_78808, plain, (![D_4048]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_4048)=k7_relat_1('#skF_6', D_4048) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_78806])).
% 23.90/13.95  tff(c_78816, plain, (![D_4048]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_4048)=k7_relat_1('#skF_6', D_4048))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_78808])).
% 23.90/13.95  tff(c_78810, plain, (![D_4048]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_4048)=k7_relat_1('#skF_5', D_4048) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_78806])).
% 23.90/13.95  tff(c_78819, plain, (![D_4048]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_4048)=k7_relat_1('#skF_5', D_4048))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78810])).
% 23.90/13.95  tff(c_79144, plain, (![E_4066, F_4069, A_4068, D_4067, C_4070, B_4065]: (v1_funct_1(k1_tmap_1(A_4068, B_4065, C_4070, D_4067, E_4066, F_4069)) | ~m1_subset_1(F_4069, k1_zfmisc_1(k2_zfmisc_1(D_4067, B_4065))) | ~v1_funct_2(F_4069, D_4067, B_4065) | ~v1_funct_1(F_4069) | ~m1_subset_1(E_4066, k1_zfmisc_1(k2_zfmisc_1(C_4070, B_4065))) | ~v1_funct_2(E_4066, C_4070, B_4065) | ~v1_funct_1(E_4066) | ~m1_subset_1(D_4067, k1_zfmisc_1(A_4068)) | v1_xboole_0(D_4067) | ~m1_subset_1(C_4070, k1_zfmisc_1(A_4068)) | v1_xboole_0(C_4070) | v1_xboole_0(B_4065) | v1_xboole_0(A_4068))), inference(cnfTransformation, [status(thm)], [f_213])).
% 23.90/13.95  tff(c_79146, plain, (![A_4068, C_4070, E_4066]: (v1_funct_1(k1_tmap_1(A_4068, '#skF_2', C_4070, '#skF_4', E_4066, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_4066, k1_zfmisc_1(k2_zfmisc_1(C_4070, '#skF_2'))) | ~v1_funct_2(E_4066, C_4070, '#skF_2') | ~v1_funct_1(E_4066) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4068)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_4070, k1_zfmisc_1(A_4068)) | v1_xboole_0(C_4070) | v1_xboole_0('#skF_2') | v1_xboole_0(A_4068))), inference(resolution, [status(thm)], [c_66, c_79144])).
% 23.90/13.95  tff(c_79154, plain, (![A_4068, C_4070, E_4066]: (v1_funct_1(k1_tmap_1(A_4068, '#skF_2', C_4070, '#skF_4', E_4066, '#skF_6')) | ~m1_subset_1(E_4066, k1_zfmisc_1(k2_zfmisc_1(C_4070, '#skF_2'))) | ~v1_funct_2(E_4066, C_4070, '#skF_2') | ~v1_funct_1(E_4066) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4068)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_4070, k1_zfmisc_1(A_4068)) | v1_xboole_0(C_4070) | v1_xboole_0('#skF_2') | v1_xboole_0(A_4068))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_79146])).
% 23.90/13.95  tff(c_80870, plain, (![A_4151, C_4152, E_4153]: (v1_funct_1(k1_tmap_1(A_4151, '#skF_2', C_4152, '#skF_4', E_4153, '#skF_6')) | ~m1_subset_1(E_4153, k1_zfmisc_1(k2_zfmisc_1(C_4152, '#skF_2'))) | ~v1_funct_2(E_4153, C_4152, '#skF_2') | ~v1_funct_1(E_4153) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4151)) | ~m1_subset_1(C_4152, k1_zfmisc_1(A_4151)) | v1_xboole_0(C_4152) | v1_xboole_0(A_4151))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_79154])).
% 23.90/13.95  tff(c_80877, plain, (![A_4151]: (v1_funct_1(k1_tmap_1(A_4151, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4151)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4151)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4151))), inference(resolution, [status(thm)], [c_72, c_80870])).
% 23.90/13.95  tff(c_80890, plain, (![A_4151]: (v1_funct_1(k1_tmap_1(A_4151, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4151)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4151)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4151))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_80877])).
% 23.90/13.95  tff(c_81694, plain, (![A_4171]: (v1_funct_1(k1_tmap_1(A_4171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4171)) | v1_xboole_0(A_4171))), inference(negUnitSimplification, [status(thm)], [c_86, c_80890])).
% 23.90/13.95  tff(c_81697, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_81694])).
% 23.90/13.95  tff(c_81700, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_81697])).
% 23.90/13.95  tff(c_81701, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_90, c_81700])).
% 23.90/13.95  tff(c_79614, plain, (![D_4105, A_4106, E_4107, C_4108, F_4110, B_4109]: (k2_partfun1(k4_subset_1(A_4106, C_4108, D_4105), B_4109, k1_tmap_1(A_4106, B_4109, C_4108, D_4105, E_4107, F_4110), C_4108)=E_4107 | ~m1_subset_1(k1_tmap_1(A_4106, B_4109, C_4108, D_4105, E_4107, F_4110), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_4106, C_4108, D_4105), B_4109))) | ~v1_funct_2(k1_tmap_1(A_4106, B_4109, C_4108, D_4105, E_4107, F_4110), k4_subset_1(A_4106, C_4108, D_4105), B_4109) | ~v1_funct_1(k1_tmap_1(A_4106, B_4109, C_4108, D_4105, E_4107, F_4110)) | k2_partfun1(D_4105, B_4109, F_4110, k9_subset_1(A_4106, C_4108, D_4105))!=k2_partfun1(C_4108, B_4109, E_4107, k9_subset_1(A_4106, C_4108, D_4105)) | ~m1_subset_1(F_4110, k1_zfmisc_1(k2_zfmisc_1(D_4105, B_4109))) | ~v1_funct_2(F_4110, D_4105, B_4109) | ~v1_funct_1(F_4110) | ~m1_subset_1(E_4107, k1_zfmisc_1(k2_zfmisc_1(C_4108, B_4109))) | ~v1_funct_2(E_4107, C_4108, B_4109) | ~v1_funct_1(E_4107) | ~m1_subset_1(D_4105, k1_zfmisc_1(A_4106)) | v1_xboole_0(D_4105) | ~m1_subset_1(C_4108, k1_zfmisc_1(A_4106)) | v1_xboole_0(C_4108) | v1_xboole_0(B_4109) | v1_xboole_0(A_4106))), inference(cnfTransformation, [status(thm)], [f_179])).
% 23.90/13.95  tff(c_86030, plain, (![F_4358, E_4355, A_4357, B_4354, D_4356, C_4359]: (k2_partfun1(k4_subset_1(A_4357, C_4359, D_4356), B_4354, k1_tmap_1(A_4357, B_4354, C_4359, D_4356, E_4355, F_4358), C_4359)=E_4355 | ~v1_funct_2(k1_tmap_1(A_4357, B_4354, C_4359, D_4356, E_4355, F_4358), k4_subset_1(A_4357, C_4359, D_4356), B_4354) | ~v1_funct_1(k1_tmap_1(A_4357, B_4354, C_4359, D_4356, E_4355, F_4358)) | k2_partfun1(D_4356, B_4354, F_4358, k9_subset_1(A_4357, C_4359, D_4356))!=k2_partfun1(C_4359, B_4354, E_4355, k9_subset_1(A_4357, C_4359, D_4356)) | ~m1_subset_1(F_4358, k1_zfmisc_1(k2_zfmisc_1(D_4356, B_4354))) | ~v1_funct_2(F_4358, D_4356, B_4354) | ~v1_funct_1(F_4358) | ~m1_subset_1(E_4355, k1_zfmisc_1(k2_zfmisc_1(C_4359, B_4354))) | ~v1_funct_2(E_4355, C_4359, B_4354) | ~v1_funct_1(E_4355) | ~m1_subset_1(D_4356, k1_zfmisc_1(A_4357)) | v1_xboole_0(D_4356) | ~m1_subset_1(C_4359, k1_zfmisc_1(A_4357)) | v1_xboole_0(C_4359) | v1_xboole_0(B_4354) | v1_xboole_0(A_4357))), inference(resolution, [status(thm)], [c_58, c_79614])).
% 23.90/13.95  tff(c_88799, plain, (![F_4456, E_4453, D_4454, A_4455, B_4452, C_4457]: (k2_partfun1(k4_subset_1(A_4455, C_4457, D_4454), B_4452, k1_tmap_1(A_4455, B_4452, C_4457, D_4454, E_4453, F_4456), C_4457)=E_4453 | ~v1_funct_1(k1_tmap_1(A_4455, B_4452, C_4457, D_4454, E_4453, F_4456)) | k2_partfun1(D_4454, B_4452, F_4456, k9_subset_1(A_4455, C_4457, D_4454))!=k2_partfun1(C_4457, B_4452, E_4453, k9_subset_1(A_4455, C_4457, D_4454)) | ~m1_subset_1(F_4456, k1_zfmisc_1(k2_zfmisc_1(D_4454, B_4452))) | ~v1_funct_2(F_4456, D_4454, B_4452) | ~v1_funct_1(F_4456) | ~m1_subset_1(E_4453, k1_zfmisc_1(k2_zfmisc_1(C_4457, B_4452))) | ~v1_funct_2(E_4453, C_4457, B_4452) | ~v1_funct_1(E_4453) | ~m1_subset_1(D_4454, k1_zfmisc_1(A_4455)) | v1_xboole_0(D_4454) | ~m1_subset_1(C_4457, k1_zfmisc_1(A_4455)) | v1_xboole_0(C_4457) | v1_xboole_0(B_4452) | v1_xboole_0(A_4455))), inference(resolution, [status(thm)], [c_60, c_86030])).
% 23.90/13.95  tff(c_88803, plain, (![A_4455, C_4457, E_4453]: (k2_partfun1(k4_subset_1(A_4455, C_4457, '#skF_4'), '#skF_2', k1_tmap_1(A_4455, '#skF_2', C_4457, '#skF_4', E_4453, '#skF_6'), C_4457)=E_4453 | ~v1_funct_1(k1_tmap_1(A_4455, '#skF_2', C_4457, '#skF_4', E_4453, '#skF_6')) | k2_partfun1(C_4457, '#skF_2', E_4453, k9_subset_1(A_4455, C_4457, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_4455, C_4457, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_4453, k1_zfmisc_1(k2_zfmisc_1(C_4457, '#skF_2'))) | ~v1_funct_2(E_4453, C_4457, '#skF_2') | ~v1_funct_1(E_4453) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4455)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_4457, k1_zfmisc_1(A_4455)) | v1_xboole_0(C_4457) | v1_xboole_0('#skF_2') | v1_xboole_0(A_4455))), inference(resolution, [status(thm)], [c_66, c_88799])).
% 23.90/13.95  tff(c_88812, plain, (![A_4455, C_4457, E_4453]: (k2_partfun1(k4_subset_1(A_4455, C_4457, '#skF_4'), '#skF_2', k1_tmap_1(A_4455, '#skF_2', C_4457, '#skF_4', E_4453, '#skF_6'), C_4457)=E_4453 | ~v1_funct_1(k1_tmap_1(A_4455, '#skF_2', C_4457, '#skF_4', E_4453, '#skF_6')) | k2_partfun1(C_4457, '#skF_2', E_4453, k9_subset_1(A_4455, C_4457, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4455, C_4457, '#skF_4')) | ~m1_subset_1(E_4453, k1_zfmisc_1(k2_zfmisc_1(C_4457, '#skF_2'))) | ~v1_funct_2(E_4453, C_4457, '#skF_2') | ~v1_funct_1(E_4453) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4455)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_4457, k1_zfmisc_1(A_4455)) | v1_xboole_0(C_4457) | v1_xboole_0('#skF_2') | v1_xboole_0(A_4455))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_78816, c_88803])).
% 23.90/13.95  tff(c_93830, plain, (![A_4545, C_4546, E_4547]: (k2_partfun1(k4_subset_1(A_4545, C_4546, '#skF_4'), '#skF_2', k1_tmap_1(A_4545, '#skF_2', C_4546, '#skF_4', E_4547, '#skF_6'), C_4546)=E_4547 | ~v1_funct_1(k1_tmap_1(A_4545, '#skF_2', C_4546, '#skF_4', E_4547, '#skF_6')) | k2_partfun1(C_4546, '#skF_2', E_4547, k9_subset_1(A_4545, C_4546, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4545, C_4546, '#skF_4')) | ~m1_subset_1(E_4547, k1_zfmisc_1(k2_zfmisc_1(C_4546, '#skF_2'))) | ~v1_funct_2(E_4547, C_4546, '#skF_2') | ~v1_funct_1(E_4547) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4545)) | ~m1_subset_1(C_4546, k1_zfmisc_1(A_4545)) | v1_xboole_0(C_4546) | v1_xboole_0(A_4545))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_88812])).
% 23.90/13.95  tff(c_93837, plain, (![A_4545]: (k2_partfun1(k4_subset_1(A_4545, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4545, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4545, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_4545, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4545, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4545)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4545)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4545))), inference(resolution, [status(thm)], [c_72, c_93830])).
% 23.90/13.95  tff(c_93850, plain, (![A_4545]: (k2_partfun1(k4_subset_1(A_4545, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4545, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4545, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4545, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4545, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4545)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4545)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4545))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_78819, c_93837])).
% 23.90/13.95  tff(c_95468, plain, (![A_4571]: (k2_partfun1(k4_subset_1(A_4571, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4571, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_4571, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4571, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4571, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4571)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4571)) | v1_xboole_0(A_4571))), inference(negUnitSimplification, [status(thm)], [c_86, c_93850])).
% 23.90/13.95  tff(c_75705, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_9434])).
% 23.90/13.95  tff(c_79805, plain, (![A_4121, G_4119, C_4122, D_4120, B_4123]: (k1_tmap_1(A_4121, B_4123, C_4122, D_4120, k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, C_4122), k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, D_4120))=G_4119 | ~m1_subset_1(G_4119, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_4121, C_4122, D_4120), B_4123))) | ~v1_funct_2(G_4119, k4_subset_1(A_4121, C_4122, D_4120), B_4123) | ~v1_funct_1(G_4119) | k2_partfun1(D_4120, B_4123, k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, D_4120), k9_subset_1(A_4121, C_4122, D_4120))!=k2_partfun1(C_4122, B_4123, k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, C_4122), k9_subset_1(A_4121, C_4122, D_4120)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, D_4120), k1_zfmisc_1(k2_zfmisc_1(D_4120, B_4123))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, D_4120), D_4120, B_4123) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, D_4120)) | ~m1_subset_1(k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, C_4122), k1_zfmisc_1(k2_zfmisc_1(C_4122, B_4123))) | ~v1_funct_2(k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, C_4122), C_4122, B_4123) | ~v1_funct_1(k2_partfun1(k4_subset_1(A_4121, C_4122, D_4120), B_4123, G_4119, C_4122)) | ~m1_subset_1(D_4120, k1_zfmisc_1(A_4121)) | v1_xboole_0(D_4120) | ~m1_subset_1(C_4122, k1_zfmisc_1(A_4121)) | v1_xboole_0(C_4122) | v1_xboole_0(B_4123) | v1_xboole_0(A_4121))), inference(cnfTransformation, [status(thm)], [f_179])).
% 23.90/13.95  tff(c_79807, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'))=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')) | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75705, c_79805])).
% 23.90/13.95  tff(c_79809, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')) | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_70, c_75705, c_68, c_75705, c_66, c_79303, c_78816, c_75705, c_79107, c_77808, c_79107, c_77808, c_75705, c_79807])).
% 23.90/13.95  tff(c_79810, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_82, c_79809])).
% 23.90/13.95  tff(c_82688, plain, (k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_81701, c_79810])).
% 23.90/13.95  tff(c_82689, plain, (~v1_funct_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_82688])).
% 23.90/13.95  tff(c_95477, plain, (~v1_funct_1('#skF_5') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_95468, c_82689])).
% 23.90/13.95  tff(c_95490, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_79303, c_79107, c_77808, c_79117, c_79107, c_77808, c_81701, c_76, c_95477])).
% 23.90/13.95  tff(c_95492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_95490])).
% 23.90/13.95  tff(c_95493, plain, (~v1_funct_2(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | k2_partfun1('#skF_3', '#skF_2', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), k1_xboole_0)!=k1_xboole_0 | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2'))) | k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3'), '#skF_6')=k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_82688])).
% 23.90/13.95  tff(c_96326, plain, (~m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitLeft, [status(thm)], [c_95493])).
% 23.90/13.95  tff(c_97802, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_96326])).
% 23.90/13.95  tff(c_97805, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_76, c_74, c_72, c_70, c_68, c_66, c_97802])).
% 23.90/13.95  tff(c_97807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_82, c_97805])).
% 23.90/13.95  tff(c_97809, plain, (m1_subset_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')))), inference(splitRight, [status(thm)], [c_95493])).
% 23.90/13.95  tff(c_56, plain, (![E_165, D_157, A_45, C_141, B_109, F_169]: (k2_partfun1(k4_subset_1(A_45, C_141, D_157), B_109, k1_tmap_1(A_45, B_109, C_141, D_157, E_165, F_169), C_141)=E_165 | ~m1_subset_1(k1_tmap_1(A_45, B_109, C_141, D_157, E_165, F_169), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_45, C_141, D_157), B_109))) | ~v1_funct_2(k1_tmap_1(A_45, B_109, C_141, D_157, E_165, F_169), k4_subset_1(A_45, C_141, D_157), B_109) | ~v1_funct_1(k1_tmap_1(A_45, B_109, C_141, D_157, E_165, F_169)) | k2_partfun1(D_157, B_109, F_169, k9_subset_1(A_45, C_141, D_157))!=k2_partfun1(C_141, B_109, E_165, k9_subset_1(A_45, C_141, D_157)) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(D_157, B_109))) | ~v1_funct_2(F_169, D_157, B_109) | ~v1_funct_1(F_169) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_141, B_109))) | ~v1_funct_2(E_165, C_141, B_109) | ~v1_funct_1(E_165) | ~m1_subset_1(D_157, k1_zfmisc_1(A_45)) | v1_xboole_0(D_157) | ~m1_subset_1(C_141, k1_zfmisc_1(A_45)) | v1_xboole_0(C_141) | v1_xboole_0(B_109) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_179])).
% 23.90/13.95  tff(c_97866, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_97809, c_56])).
% 23.90/13.95  tff(c_97900, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_76, c_74, c_72, c_70, c_68, c_66, c_79303, c_79107, c_77808, c_79117, c_79107, c_77808, c_78816, c_78819, c_81701, c_97866])).
% 23.90/13.95  tff(c_97901, plain, (~v1_funct_2(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_82, c_75704, c_97900])).
% 23.90/13.95  tff(c_97942, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_97901])).
% 23.90/13.95  tff(c_97945, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_76, c_74, c_72, c_70, c_68, c_66, c_97942])).
% 23.90/13.95  tff(c_97947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_82, c_97945])).
% 23.90/13.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.90/13.95  
% 23.90/13.95  Inference rules
% 23.90/13.95  ----------------------
% 23.90/13.95  #Ref     : 0
% 23.90/13.95  #Sup     : 20577
% 23.90/13.95  #Fact    : 0
% 23.90/13.95  #Define  : 0
% 23.90/13.95  #Split   : 132
% 23.90/13.95  #Chain   : 0
% 23.90/13.95  #Close   : 0
% 23.90/13.95  
% 23.90/13.95  Ordering : KBO
% 23.90/13.95  
% 23.90/13.95  Simplification rules
% 23.90/13.95  ----------------------
% 23.90/13.95  #Subsume      : 6084
% 23.90/13.95  #Demod        : 40288
% 23.90/13.95  #Tautology    : 6840
% 23.90/13.95  #SimpNegUnit  : 562
% 23.90/13.95  #BackRed      : 72
% 23.90/13.95  
% 23.90/13.95  #Partial instantiations: 0
% 23.90/13.95  #Strategies tried      : 1
% 23.90/13.95  
% 23.90/13.95  Timing (in seconds)
% 23.90/13.95  ----------------------
% 23.90/13.96  Preprocessing        : 0.44
% 23.90/13.96  Parsing              : 0.21
% 23.90/13.96  CNF conversion       : 0.07
% 23.90/13.96  Main loop            : 12.57
% 23.90/13.96  Inferencing          : 3.07
% 23.90/13.96  Reduction            : 5.73
% 23.90/13.96  Demodulation         : 4.53
% 23.90/13.96  BG Simplification    : 0.24
% 23.90/13.96  Subsumption          : 2.91
% 23.90/13.96  Abstraction          : 0.37
% 23.90/13.96  MUC search           : 0.00
% 23.90/13.96  Cooper               : 0.00
% 23.90/13.96  Total                : 13.16
% 23.90/13.96  Index Insertion      : 0.00
% 23.90/13.96  Index Deletion       : 0.00
% 23.90/13.96  Index Matching       : 0.00
% 23.90/13.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
