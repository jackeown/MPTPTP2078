%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:21 EST 2020

% Result     : Theorem 8.07s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 906 expanded)
%              Number of leaves         :   43 ( 331 expanded)
%              Depth                    :   14
%              Number of atoms          :  705 (4200 expanded)
%              Number of equality atoms :  134 ( 745 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
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

tff(c_14,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_966,plain,(
    ! [B_331,A_332] :
      ( v1_relat_1(B_331)
      | ~ m1_subset_1(B_331,k1_zfmisc_1(A_332))
      | ~ v1_relat_1(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_972,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_966])).

tff(c_984,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_972])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1016,plain,(
    ! [B_343,A_344] :
      ( k7_relat_1(B_343,A_344) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_343),A_344)
      | ~ v1_relat_1(B_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1040,plain,(
    ! [B_345] :
      ( k7_relat_1(B_345,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_345) ) ),
    inference(resolution,[status(thm)],[c_6,c_1016])).

tff(c_1050,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_984,c_1040])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_969,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_966])).

tff(c_981,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_969])).

tff(c_1051,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_981,c_1040])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | ~ r1_subset_1(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_987,plain,(
    ! [C_333,A_334,B_335] :
      ( v4_relat_1(C_333,A_334)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_994,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_987])).

tff(c_1087,plain,(
    ! [B_351,A_352] :
      ( k1_relat_1(B_351) = A_352
      | ~ v1_partfun1(B_351,A_352)
      | ~ v4_relat_1(B_351,A_352)
      | ~ v1_relat_1(B_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1093,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_994,c_1087])).

tff(c_1099,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_1093])).

tff(c_3896,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1099])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_4150,plain,(
    ! [C_835,A_836,B_837] :
      ( v1_partfun1(C_835,A_836)
      | ~ v1_funct_2(C_835,A_836,B_837)
      | ~ v1_funct_1(C_835)
      | ~ m1_subset_1(C_835,k1_zfmisc_1(k2_zfmisc_1(A_836,B_837)))
      | v1_xboole_0(B_837) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4153,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_4150])).

tff(c_4159,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4153])).

tff(c_4161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3896,c_4159])).

tff(c_4162,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1099])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4170,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_5',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4162,c_16])).

tff(c_4214,plain,(
    ! [A_841] :
      ( k7_relat_1('#skF_5',A_841) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_841) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_4170])).

tff(c_4221,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_4214])).

tff(c_4355,plain,(
    ! [B_850] :
      ( k7_relat_1('#skF_5',B_850) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_850)
      | v1_xboole_0(B_850) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4221])).

tff(c_4358,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_4355])).

tff(c_4361,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4358])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( r1_xboole_0(k1_relat_1(B_16),A_15)
      | k7_relat_1(B_16,A_15) != k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4173,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k7_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4162,c_18])).

tff(c_4203,plain,(
    ! [A_840] :
      ( r1_xboole_0('#skF_3',A_840)
      | k7_relat_1('#skF_5',A_840) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_4173])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4213,plain,(
    ! [A_840] :
      ( k3_xboole_0('#skF_3',A_840) = k1_xboole_0
      | k7_relat_1('#skF_5',A_840) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4203,c_2])).

tff(c_4375,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4361,c_4213])).

tff(c_3882,plain,(
    ! [A_804,B_805,C_806] :
      ( k9_subset_1(A_804,B_805,C_806) = k3_xboole_0(B_805,C_806)
      | ~ m1_subset_1(C_806,k1_zfmisc_1(A_804)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3894,plain,(
    ! [B_805] : k9_subset_1('#skF_1',B_805,'#skF_4') = k3_xboole_0(B_805,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_3882])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_4560,plain,(
    ! [D_876,A_879,E_880,B_878,F_877,C_875] :
      ( v1_funct_1(k1_tmap_1(A_879,B_878,C_875,D_876,E_880,F_877))
      | ~ m1_subset_1(F_877,k1_zfmisc_1(k2_zfmisc_1(D_876,B_878)))
      | ~ v1_funct_2(F_877,D_876,B_878)
      | ~ v1_funct_1(F_877)
      | ~ m1_subset_1(E_880,k1_zfmisc_1(k2_zfmisc_1(C_875,B_878)))
      | ~ v1_funct_2(E_880,C_875,B_878)
      | ~ v1_funct_1(E_880)
      | ~ m1_subset_1(D_876,k1_zfmisc_1(A_879))
      | v1_xboole_0(D_876)
      | ~ m1_subset_1(C_875,k1_zfmisc_1(A_879))
      | v1_xboole_0(C_875)
      | v1_xboole_0(B_878)
      | v1_xboole_0(A_879) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4564,plain,(
    ! [A_879,C_875,E_880] :
      ( v1_funct_1(k1_tmap_1(A_879,'#skF_2',C_875,'#skF_4',E_880,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_880,k1_zfmisc_1(k2_zfmisc_1(C_875,'#skF_2')))
      | ~ v1_funct_2(E_880,C_875,'#skF_2')
      | ~ v1_funct_1(E_880)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_879))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_875,k1_zfmisc_1(A_879))
      | v1_xboole_0(C_875)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_879) ) ),
    inference(resolution,[status(thm)],[c_52,c_4560])).

tff(c_4571,plain,(
    ! [A_879,C_875,E_880] :
      ( v1_funct_1(k1_tmap_1(A_879,'#skF_2',C_875,'#skF_4',E_880,'#skF_6'))
      | ~ m1_subset_1(E_880,k1_zfmisc_1(k2_zfmisc_1(C_875,'#skF_2')))
      | ~ v1_funct_2(E_880,C_875,'#skF_2')
      | ~ v1_funct_1(E_880)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_879))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_875,k1_zfmisc_1(A_879))
      | v1_xboole_0(C_875)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_879) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4564])).

tff(c_4602,plain,(
    ! [A_892,C_893,E_894] :
      ( v1_funct_1(k1_tmap_1(A_892,'#skF_2',C_893,'#skF_4',E_894,'#skF_6'))
      | ~ m1_subset_1(E_894,k1_zfmisc_1(k2_zfmisc_1(C_893,'#skF_2')))
      | ~ v1_funct_2(E_894,C_893,'#skF_2')
      | ~ v1_funct_1(E_894)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_892))
      | ~ m1_subset_1(C_893,k1_zfmisc_1(A_892))
      | v1_xboole_0(C_893)
      | v1_xboole_0(A_892) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_4571])).

tff(c_4604,plain,(
    ! [A_892] :
      ( v1_funct_1(k1_tmap_1(A_892,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_892))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_892))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_892) ) ),
    inference(resolution,[status(thm)],[c_58,c_4602])).

tff(c_4609,plain,(
    ! [A_892] :
      ( v1_funct_1(k1_tmap_1(A_892,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_892))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_892))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_892) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4604])).

tff(c_4622,plain,(
    ! [A_896] :
      ( v1_funct_1(k1_tmap_1(A_896,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_896))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_896))
      | v1_xboole_0(A_896) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4609])).

tff(c_4625,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4622])).

tff(c_4628,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4625])).

tff(c_4629,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4628])).

tff(c_4382,plain,(
    ! [A_851,B_852,C_853,D_854] :
      ( k2_partfun1(A_851,B_852,C_853,D_854) = k7_relat_1(C_853,D_854)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(A_851,B_852)))
      | ~ v1_funct_1(C_853) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4384,plain,(
    ! [D_854] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_854) = k7_relat_1('#skF_5',D_854)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_4382])).

tff(c_4389,plain,(
    ! [D_854] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_854) = k7_relat_1('#skF_5',D_854) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4384])).

tff(c_4386,plain,(
    ! [D_854] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_854) = k7_relat_1('#skF_6',D_854)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_4382])).

tff(c_4392,plain,(
    ! [D_854] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_854) = k7_relat_1('#skF_6',D_854) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4386])).

tff(c_46,plain,(
    ! [D_162,C_161,A_159,E_163,B_160,F_164] :
      ( v1_funct_2(k1_tmap_1(A_159,B_160,C_161,D_162,E_163,F_164),k4_subset_1(A_159,C_161,D_162),B_160)
      | ~ m1_subset_1(F_164,k1_zfmisc_1(k2_zfmisc_1(D_162,B_160)))
      | ~ v1_funct_2(F_164,D_162,B_160)
      | ~ v1_funct_1(F_164)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(C_161,B_160)))
      | ~ v1_funct_2(E_163,C_161,B_160)
      | ~ v1_funct_1(E_163)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(A_159))
      | v1_xboole_0(D_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(A_159))
      | v1_xboole_0(C_161)
      | v1_xboole_0(B_160)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_44,plain,(
    ! [D_162,C_161,A_159,E_163,B_160,F_164] :
      ( m1_subset_1(k1_tmap_1(A_159,B_160,C_161,D_162,E_163,F_164),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_159,C_161,D_162),B_160)))
      | ~ m1_subset_1(F_164,k1_zfmisc_1(k2_zfmisc_1(D_162,B_160)))
      | ~ v1_funct_2(F_164,D_162,B_160)
      | ~ v1_funct_1(F_164)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(C_161,B_160)))
      | ~ v1_funct_2(E_163,C_161,B_160)
      | ~ v1_funct_1(E_163)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(A_159))
      | v1_xboole_0(D_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(A_159))
      | v1_xboole_0(C_161)
      | v1_xboole_0(B_160)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4778,plain,(
    ! [F_925,C_929,A_927,E_924,B_928,D_926] :
      ( k2_partfun1(k4_subset_1(A_927,C_929,D_926),B_928,k1_tmap_1(A_927,B_928,C_929,D_926,E_924,F_925),C_929) = E_924
      | ~ m1_subset_1(k1_tmap_1(A_927,B_928,C_929,D_926,E_924,F_925),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_927,C_929,D_926),B_928)))
      | ~ v1_funct_2(k1_tmap_1(A_927,B_928,C_929,D_926,E_924,F_925),k4_subset_1(A_927,C_929,D_926),B_928)
      | ~ v1_funct_1(k1_tmap_1(A_927,B_928,C_929,D_926,E_924,F_925))
      | k2_partfun1(D_926,B_928,F_925,k9_subset_1(A_927,C_929,D_926)) != k2_partfun1(C_929,B_928,E_924,k9_subset_1(A_927,C_929,D_926))
      | ~ m1_subset_1(F_925,k1_zfmisc_1(k2_zfmisc_1(D_926,B_928)))
      | ~ v1_funct_2(F_925,D_926,B_928)
      | ~ v1_funct_1(F_925)
      | ~ m1_subset_1(E_924,k1_zfmisc_1(k2_zfmisc_1(C_929,B_928)))
      | ~ v1_funct_2(E_924,C_929,B_928)
      | ~ v1_funct_1(E_924)
      | ~ m1_subset_1(D_926,k1_zfmisc_1(A_927))
      | v1_xboole_0(D_926)
      | ~ m1_subset_1(C_929,k1_zfmisc_1(A_927))
      | v1_xboole_0(C_929)
      | v1_xboole_0(B_928)
      | v1_xboole_0(A_927) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5023,plain,(
    ! [E_1029,C_1024,B_1027,A_1028,F_1026,D_1025] :
      ( k2_partfun1(k4_subset_1(A_1028,C_1024,D_1025),B_1027,k1_tmap_1(A_1028,B_1027,C_1024,D_1025,E_1029,F_1026),C_1024) = E_1029
      | ~ v1_funct_2(k1_tmap_1(A_1028,B_1027,C_1024,D_1025,E_1029,F_1026),k4_subset_1(A_1028,C_1024,D_1025),B_1027)
      | ~ v1_funct_1(k1_tmap_1(A_1028,B_1027,C_1024,D_1025,E_1029,F_1026))
      | k2_partfun1(D_1025,B_1027,F_1026,k9_subset_1(A_1028,C_1024,D_1025)) != k2_partfun1(C_1024,B_1027,E_1029,k9_subset_1(A_1028,C_1024,D_1025))
      | ~ m1_subset_1(F_1026,k1_zfmisc_1(k2_zfmisc_1(D_1025,B_1027)))
      | ~ v1_funct_2(F_1026,D_1025,B_1027)
      | ~ v1_funct_1(F_1026)
      | ~ m1_subset_1(E_1029,k1_zfmisc_1(k2_zfmisc_1(C_1024,B_1027)))
      | ~ v1_funct_2(E_1029,C_1024,B_1027)
      | ~ v1_funct_1(E_1029)
      | ~ m1_subset_1(D_1025,k1_zfmisc_1(A_1028))
      | v1_xboole_0(D_1025)
      | ~ m1_subset_1(C_1024,k1_zfmisc_1(A_1028))
      | v1_xboole_0(C_1024)
      | v1_xboole_0(B_1027)
      | v1_xboole_0(A_1028) ) ),
    inference(resolution,[status(thm)],[c_44,c_4778])).

tff(c_5530,plain,(
    ! [F_1090,C_1088,D_1089,A_1092,E_1093,B_1091] :
      ( k2_partfun1(k4_subset_1(A_1092,C_1088,D_1089),B_1091,k1_tmap_1(A_1092,B_1091,C_1088,D_1089,E_1093,F_1090),C_1088) = E_1093
      | ~ v1_funct_1(k1_tmap_1(A_1092,B_1091,C_1088,D_1089,E_1093,F_1090))
      | k2_partfun1(D_1089,B_1091,F_1090,k9_subset_1(A_1092,C_1088,D_1089)) != k2_partfun1(C_1088,B_1091,E_1093,k9_subset_1(A_1092,C_1088,D_1089))
      | ~ m1_subset_1(F_1090,k1_zfmisc_1(k2_zfmisc_1(D_1089,B_1091)))
      | ~ v1_funct_2(F_1090,D_1089,B_1091)
      | ~ v1_funct_1(F_1090)
      | ~ m1_subset_1(E_1093,k1_zfmisc_1(k2_zfmisc_1(C_1088,B_1091)))
      | ~ v1_funct_2(E_1093,C_1088,B_1091)
      | ~ v1_funct_1(E_1093)
      | ~ m1_subset_1(D_1089,k1_zfmisc_1(A_1092))
      | v1_xboole_0(D_1089)
      | ~ m1_subset_1(C_1088,k1_zfmisc_1(A_1092))
      | v1_xboole_0(C_1088)
      | v1_xboole_0(B_1091)
      | v1_xboole_0(A_1092) ) ),
    inference(resolution,[status(thm)],[c_46,c_5023])).

tff(c_5536,plain,(
    ! [A_1092,C_1088,E_1093] :
      ( k2_partfun1(k4_subset_1(A_1092,C_1088,'#skF_4'),'#skF_2',k1_tmap_1(A_1092,'#skF_2',C_1088,'#skF_4',E_1093,'#skF_6'),C_1088) = E_1093
      | ~ v1_funct_1(k1_tmap_1(A_1092,'#skF_2',C_1088,'#skF_4',E_1093,'#skF_6'))
      | k2_partfun1(C_1088,'#skF_2',E_1093,k9_subset_1(A_1092,C_1088,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1092,C_1088,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1093,k1_zfmisc_1(k2_zfmisc_1(C_1088,'#skF_2')))
      | ~ v1_funct_2(E_1093,C_1088,'#skF_2')
      | ~ v1_funct_1(E_1093)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1092))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1088,k1_zfmisc_1(A_1092))
      | v1_xboole_0(C_1088)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1092) ) ),
    inference(resolution,[status(thm)],[c_52,c_5530])).

tff(c_5544,plain,(
    ! [A_1092,C_1088,E_1093] :
      ( k2_partfun1(k4_subset_1(A_1092,C_1088,'#skF_4'),'#skF_2',k1_tmap_1(A_1092,'#skF_2',C_1088,'#skF_4',E_1093,'#skF_6'),C_1088) = E_1093
      | ~ v1_funct_1(k1_tmap_1(A_1092,'#skF_2',C_1088,'#skF_4',E_1093,'#skF_6'))
      | k2_partfun1(C_1088,'#skF_2',E_1093,k9_subset_1(A_1092,C_1088,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1092,C_1088,'#skF_4'))
      | ~ m1_subset_1(E_1093,k1_zfmisc_1(k2_zfmisc_1(C_1088,'#skF_2')))
      | ~ v1_funct_2(E_1093,C_1088,'#skF_2')
      | ~ v1_funct_1(E_1093)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1092))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1088,k1_zfmisc_1(A_1092))
      | v1_xboole_0(C_1088)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1092) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4392,c_5536])).

tff(c_5740,plain,(
    ! [A_1128,C_1129,E_1130] :
      ( k2_partfun1(k4_subset_1(A_1128,C_1129,'#skF_4'),'#skF_2',k1_tmap_1(A_1128,'#skF_2',C_1129,'#skF_4',E_1130,'#skF_6'),C_1129) = E_1130
      | ~ v1_funct_1(k1_tmap_1(A_1128,'#skF_2',C_1129,'#skF_4',E_1130,'#skF_6'))
      | k2_partfun1(C_1129,'#skF_2',E_1130,k9_subset_1(A_1128,C_1129,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1128,C_1129,'#skF_4'))
      | ~ m1_subset_1(E_1130,k1_zfmisc_1(k2_zfmisc_1(C_1129,'#skF_2')))
      | ~ v1_funct_2(E_1130,C_1129,'#skF_2')
      | ~ v1_funct_1(E_1130)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1128))
      | ~ m1_subset_1(C_1129,k1_zfmisc_1(A_1128))
      | v1_xboole_0(C_1129)
      | v1_xboole_0(A_1128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_5544])).

tff(c_5745,plain,(
    ! [A_1128] :
      ( k2_partfun1(k4_subset_1(A_1128,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1128,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1128,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1128,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1128,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1128))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1128))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1128) ) ),
    inference(resolution,[status(thm)],[c_58,c_5740])).

tff(c_5753,plain,(
    ! [A_1128] :
      ( k2_partfun1(k4_subset_1(A_1128,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1128,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1128,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1128,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1128,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1128))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1128))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4389,c_5745])).

tff(c_5942,plain,(
    ! [A_1146] :
      ( k2_partfun1(k4_subset_1(A_1146,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1146,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1146,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1146,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1146,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1146))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1146))
      | v1_xboole_0(A_1146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5753])).

tff(c_1552,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1099])).

tff(c_1797,plain,(
    ! [C_440,A_441,B_442] :
      ( v1_partfun1(C_440,A_441)
      | ~ v1_funct_2(C_440,A_441,B_442)
      | ~ v1_funct_1(C_440)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442)))
      | v1_xboole_0(B_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1800,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1797])).

tff(c_1806,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1800])).

tff(c_1808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1552,c_1806])).

tff(c_1809,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1099])).

tff(c_1830,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_5',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_16])).

tff(c_1885,plain,(
    ! [A_450] :
      ( k7_relat_1('#skF_5',A_450) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_1830])).

tff(c_1892,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_1885])).

tff(c_2057,plain,(
    ! [B_469] :
      ( k7_relat_1('#skF_5',B_469) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_469)
      | v1_xboole_0(B_469) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1892])).

tff(c_2063,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2057])).

tff(c_2067,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2063])).

tff(c_1833,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k7_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_18])).

tff(c_1863,plain,(
    ! [A_448] :
      ( r1_xboole_0('#skF_3',A_448)
      | k7_relat_1('#skF_5',A_448) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_1833])).

tff(c_1873,plain,(
    ! [A_448] :
      ( k3_xboole_0('#skF_3',A_448) = k1_xboole_0
      | k7_relat_1('#skF_5',A_448) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1863,c_2])).

tff(c_2080,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2067,c_1873])).

tff(c_1811,plain,(
    ! [A_443,B_444,C_445] :
      ( k9_subset_1(A_443,B_444,C_445) = k3_xboole_0(B_444,C_445)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(A_443)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1823,plain,(
    ! [B_444] : k9_subset_1('#skF_1',B_444,'#skF_4') = k3_xboole_0(B_444,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1811])).

tff(c_2176,plain,(
    ! [F_481,A_483,C_479,B_482,D_480,E_484] :
      ( v1_funct_1(k1_tmap_1(A_483,B_482,C_479,D_480,E_484,F_481))
      | ~ m1_subset_1(F_481,k1_zfmisc_1(k2_zfmisc_1(D_480,B_482)))
      | ~ v1_funct_2(F_481,D_480,B_482)
      | ~ v1_funct_1(F_481)
      | ~ m1_subset_1(E_484,k1_zfmisc_1(k2_zfmisc_1(C_479,B_482)))
      | ~ v1_funct_2(E_484,C_479,B_482)
      | ~ v1_funct_1(E_484)
      | ~ m1_subset_1(D_480,k1_zfmisc_1(A_483))
      | v1_xboole_0(D_480)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(A_483))
      | v1_xboole_0(C_479)
      | v1_xboole_0(B_482)
      | v1_xboole_0(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2180,plain,(
    ! [A_483,C_479,E_484] :
      ( v1_funct_1(k1_tmap_1(A_483,'#skF_2',C_479,'#skF_4',E_484,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_484,k1_zfmisc_1(k2_zfmisc_1(C_479,'#skF_2')))
      | ~ v1_funct_2(E_484,C_479,'#skF_2')
      | ~ v1_funct_1(E_484)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_483))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_479,k1_zfmisc_1(A_483))
      | v1_xboole_0(C_479)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_483) ) ),
    inference(resolution,[status(thm)],[c_52,c_2176])).

tff(c_2187,plain,(
    ! [A_483,C_479,E_484] :
      ( v1_funct_1(k1_tmap_1(A_483,'#skF_2',C_479,'#skF_4',E_484,'#skF_6'))
      | ~ m1_subset_1(E_484,k1_zfmisc_1(k2_zfmisc_1(C_479,'#skF_2')))
      | ~ v1_funct_2(E_484,C_479,'#skF_2')
      | ~ v1_funct_1(E_484)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_483))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_479,k1_zfmisc_1(A_483))
      | v1_xboole_0(C_479)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2180])).

tff(c_2257,plain,(
    ! [A_494,C_495,E_496] :
      ( v1_funct_1(k1_tmap_1(A_494,'#skF_2',C_495,'#skF_4',E_496,'#skF_6'))
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(C_495,'#skF_2')))
      | ~ v1_funct_2(E_496,C_495,'#skF_2')
      | ~ v1_funct_1(E_496)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_494))
      | ~ m1_subset_1(C_495,k1_zfmisc_1(A_494))
      | v1_xboole_0(C_495)
      | v1_xboole_0(A_494) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_2187])).

tff(c_2259,plain,(
    ! [A_494] :
      ( v1_funct_1(k1_tmap_1(A_494,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_494))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_494))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_494) ) ),
    inference(resolution,[status(thm)],[c_58,c_2257])).

tff(c_2264,plain,(
    ! [A_494] :
      ( v1_funct_1(k1_tmap_1(A_494,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_494))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_494))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2259])).

tff(c_2278,plain,(
    ! [A_504] :
      ( v1_funct_1(k1_tmap_1(A_504,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_504))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_504))
      | v1_xboole_0(A_504) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2264])).

tff(c_2281,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_2278])).

tff(c_2284,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2281])).

tff(c_2285,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2284])).

tff(c_1931,plain,(
    ! [A_452,B_453,C_454,D_455] :
      ( k2_partfun1(A_452,B_453,C_454,D_455) = k7_relat_1(C_454,D_455)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453)))
      | ~ v1_funct_1(C_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1933,plain,(
    ! [D_455] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_455) = k7_relat_1('#skF_5',D_455)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_1931])).

tff(c_1938,plain,(
    ! [D_455] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_455) = k7_relat_1('#skF_5',D_455) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1933])).

tff(c_1935,plain,(
    ! [D_455] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_455) = k7_relat_1('#skF_6',D_455)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_1931])).

tff(c_1941,plain,(
    ! [D_455] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_455) = k7_relat_1('#skF_6',D_455) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1935])).

tff(c_2376,plain,(
    ! [E_521,B_525,F_522,C_526,D_523,A_524] :
      ( k2_partfun1(k4_subset_1(A_524,C_526,D_523),B_525,k1_tmap_1(A_524,B_525,C_526,D_523,E_521,F_522),D_523) = F_522
      | ~ m1_subset_1(k1_tmap_1(A_524,B_525,C_526,D_523,E_521,F_522),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_524,C_526,D_523),B_525)))
      | ~ v1_funct_2(k1_tmap_1(A_524,B_525,C_526,D_523,E_521,F_522),k4_subset_1(A_524,C_526,D_523),B_525)
      | ~ v1_funct_1(k1_tmap_1(A_524,B_525,C_526,D_523,E_521,F_522))
      | k2_partfun1(D_523,B_525,F_522,k9_subset_1(A_524,C_526,D_523)) != k2_partfun1(C_526,B_525,E_521,k9_subset_1(A_524,C_526,D_523))
      | ~ m1_subset_1(F_522,k1_zfmisc_1(k2_zfmisc_1(D_523,B_525)))
      | ~ v1_funct_2(F_522,D_523,B_525)
      | ~ v1_funct_1(F_522)
      | ~ m1_subset_1(E_521,k1_zfmisc_1(k2_zfmisc_1(C_526,B_525)))
      | ~ v1_funct_2(E_521,C_526,B_525)
      | ~ v1_funct_1(E_521)
      | ~ m1_subset_1(D_523,k1_zfmisc_1(A_524))
      | v1_xboole_0(D_523)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(A_524))
      | v1_xboole_0(C_526)
      | v1_xboole_0(B_525)
      | v1_xboole_0(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2760,plain,(
    ! [F_640,D_639,A_642,C_638,E_643,B_641] :
      ( k2_partfun1(k4_subset_1(A_642,C_638,D_639),B_641,k1_tmap_1(A_642,B_641,C_638,D_639,E_643,F_640),D_639) = F_640
      | ~ v1_funct_2(k1_tmap_1(A_642,B_641,C_638,D_639,E_643,F_640),k4_subset_1(A_642,C_638,D_639),B_641)
      | ~ v1_funct_1(k1_tmap_1(A_642,B_641,C_638,D_639,E_643,F_640))
      | k2_partfun1(D_639,B_641,F_640,k9_subset_1(A_642,C_638,D_639)) != k2_partfun1(C_638,B_641,E_643,k9_subset_1(A_642,C_638,D_639))
      | ~ m1_subset_1(F_640,k1_zfmisc_1(k2_zfmisc_1(D_639,B_641)))
      | ~ v1_funct_2(F_640,D_639,B_641)
      | ~ v1_funct_1(F_640)
      | ~ m1_subset_1(E_643,k1_zfmisc_1(k2_zfmisc_1(C_638,B_641)))
      | ~ v1_funct_2(E_643,C_638,B_641)
      | ~ v1_funct_1(E_643)
      | ~ m1_subset_1(D_639,k1_zfmisc_1(A_642))
      | v1_xboole_0(D_639)
      | ~ m1_subset_1(C_638,k1_zfmisc_1(A_642))
      | v1_xboole_0(C_638)
      | v1_xboole_0(B_641)
      | v1_xboole_0(A_642) ) ),
    inference(resolution,[status(thm)],[c_44,c_2376])).

tff(c_3155,plain,(
    ! [C_702,F_704,A_706,D_703,E_707,B_705] :
      ( k2_partfun1(k4_subset_1(A_706,C_702,D_703),B_705,k1_tmap_1(A_706,B_705,C_702,D_703,E_707,F_704),D_703) = F_704
      | ~ v1_funct_1(k1_tmap_1(A_706,B_705,C_702,D_703,E_707,F_704))
      | k2_partfun1(D_703,B_705,F_704,k9_subset_1(A_706,C_702,D_703)) != k2_partfun1(C_702,B_705,E_707,k9_subset_1(A_706,C_702,D_703))
      | ~ m1_subset_1(F_704,k1_zfmisc_1(k2_zfmisc_1(D_703,B_705)))
      | ~ v1_funct_2(F_704,D_703,B_705)
      | ~ v1_funct_1(F_704)
      | ~ m1_subset_1(E_707,k1_zfmisc_1(k2_zfmisc_1(C_702,B_705)))
      | ~ v1_funct_2(E_707,C_702,B_705)
      | ~ v1_funct_1(E_707)
      | ~ m1_subset_1(D_703,k1_zfmisc_1(A_706))
      | v1_xboole_0(D_703)
      | ~ m1_subset_1(C_702,k1_zfmisc_1(A_706))
      | v1_xboole_0(C_702)
      | v1_xboole_0(B_705)
      | v1_xboole_0(A_706) ) ),
    inference(resolution,[status(thm)],[c_46,c_2760])).

tff(c_3161,plain,(
    ! [A_706,C_702,E_707] :
      ( k2_partfun1(k4_subset_1(A_706,C_702,'#skF_4'),'#skF_2',k1_tmap_1(A_706,'#skF_2',C_702,'#skF_4',E_707,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_706,'#skF_2',C_702,'#skF_4',E_707,'#skF_6'))
      | k2_partfun1(C_702,'#skF_2',E_707,k9_subset_1(A_706,C_702,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_706,C_702,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_707,k1_zfmisc_1(k2_zfmisc_1(C_702,'#skF_2')))
      | ~ v1_funct_2(E_707,C_702,'#skF_2')
      | ~ v1_funct_1(E_707)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_706))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_702,k1_zfmisc_1(A_706))
      | v1_xboole_0(C_702)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_706) ) ),
    inference(resolution,[status(thm)],[c_52,c_3155])).

tff(c_3169,plain,(
    ! [A_706,C_702,E_707] :
      ( k2_partfun1(k4_subset_1(A_706,C_702,'#skF_4'),'#skF_2',k1_tmap_1(A_706,'#skF_2',C_702,'#skF_4',E_707,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_706,'#skF_2',C_702,'#skF_4',E_707,'#skF_6'))
      | k2_partfun1(C_702,'#skF_2',E_707,k9_subset_1(A_706,C_702,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_706,C_702,'#skF_4'))
      | ~ m1_subset_1(E_707,k1_zfmisc_1(k2_zfmisc_1(C_702,'#skF_2')))
      | ~ v1_funct_2(E_707,C_702,'#skF_2')
      | ~ v1_funct_1(E_707)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_706))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_702,k1_zfmisc_1(A_706))
      | v1_xboole_0(C_702)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_706) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1941,c_3161])).

tff(c_3250,plain,(
    ! [A_728,C_729,E_730] :
      ( k2_partfun1(k4_subset_1(A_728,C_729,'#skF_4'),'#skF_2',k1_tmap_1(A_728,'#skF_2',C_729,'#skF_4',E_730,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_728,'#skF_2',C_729,'#skF_4',E_730,'#skF_6'))
      | k2_partfun1(C_729,'#skF_2',E_730,k9_subset_1(A_728,C_729,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_728,C_729,'#skF_4'))
      | ~ m1_subset_1(E_730,k1_zfmisc_1(k2_zfmisc_1(C_729,'#skF_2')))
      | ~ v1_funct_2(E_730,C_729,'#skF_2')
      | ~ v1_funct_1(E_730)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_728))
      | ~ m1_subset_1(C_729,k1_zfmisc_1(A_728))
      | v1_xboole_0(C_729)
      | v1_xboole_0(A_728) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_3169])).

tff(c_3255,plain,(
    ! [A_728] :
      ( k2_partfun1(k4_subset_1(A_728,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_728,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_728,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_728,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_728,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_728))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_728))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_728) ) ),
    inference(resolution,[status(thm)],[c_58,c_3250])).

tff(c_3263,plain,(
    ! [A_728] :
      ( k2_partfun1(k4_subset_1(A_728,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_728,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_728,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_728,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_728,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_728))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_728))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_728) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1938,c_3255])).

tff(c_3329,plain,(
    ! [A_741] :
      ( k2_partfun1(k4_subset_1(A_741,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_741,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_741,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_741,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_741,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_741))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_741))
      | v1_xboole_0(A_741) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3263])).

tff(c_118,plain,(
    ! [B_232,A_233] :
      ( v1_relat_1(B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(A_233))
      | ~ v1_relat_1(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_136,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_124])).

tff(c_187,plain,(
    ! [B_247,A_248] :
      ( k7_relat_1(B_247,A_248) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_247),A_248)
      | ~ v1_relat_1(B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_207,plain,(
    ! [B_249] :
      ( k7_relat_1(B_249,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_217,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_207])).

tff(c_121,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_118])).

tff(c_133,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_121])).

tff(c_139,plain,(
    ! [C_234,A_235,B_236] :
      ( v4_relat_1(C_234,A_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_146,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_139])).

tff(c_285,plain,(
    ! [B_259,A_260] :
      ( k1_relat_1(B_259) = A_260
      | ~ v1_partfun1(B_259,A_260)
      | ~ v4_relat_1(B_259,A_260)
      | ~ v1_relat_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_291,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_146,c_285])).

tff(c_297,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_291])).

tff(c_524,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_664,plain,(
    ! [C_303,A_304,B_305] :
      ( v1_partfun1(C_303,A_304)
      | ~ v1_funct_2(C_303,A_304,B_305)
      | ~ v1_funct_1(C_303)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_304,B_305)))
      | v1_xboole_0(B_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_667,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_664])).

tff(c_673,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_667])).

tff(c_675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_524,c_673])).

tff(c_676,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_681,plain,(
    ! [A_15] :
      ( k7_relat_1('#skF_5',A_15) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_15)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_16])).

tff(c_720,plain,(
    ! [A_308] :
      ( k7_relat_1('#skF_5',A_308) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_681])).

tff(c_727,plain,(
    ! [B_18] :
      ( k7_relat_1('#skF_5',B_18) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_720])).

tff(c_859,plain,(
    ! [B_321] :
      ( k7_relat_1('#skF_5',B_321) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_321)
      | v1_xboole_0(B_321) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_727])).

tff(c_862,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_859])).

tff(c_865,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_862])).

tff(c_687,plain,(
    ! [A_15] :
      ( r1_xboole_0('#skF_3',A_15)
      | k7_relat_1('#skF_5',A_15) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_18])).

tff(c_709,plain,(
    ! [A_307] :
      ( r1_xboole_0('#skF_3',A_307)
      | k7_relat_1('#skF_5',A_307) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_687])).

tff(c_719,plain,(
    ! [A_307] :
      ( k3_xboole_0('#skF_3',A_307) = k1_xboole_0
      | k7_relat_1('#skF_5',A_307) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_709,c_2])).

tff(c_879,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_865,c_719])).

tff(c_218,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133,c_207])).

tff(c_778,plain,(
    ! [A_312,B_313,C_314,D_315] :
      ( k2_partfun1(A_312,B_313,C_314,D_315) = k7_relat_1(C_314,D_315)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | ~ v1_funct_1(C_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_782,plain,(
    ! [D_315] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_315) = k7_relat_1('#skF_6',D_315)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_778])).

tff(c_788,plain,(
    ! [D_315] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_315) = k7_relat_1('#skF_6',D_315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_782])).

tff(c_780,plain,(
    ! [D_315] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_315) = k7_relat_1('#skF_5',D_315)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_778])).

tff(c_785,plain,(
    ! [D_315] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_315) = k7_relat_1('#skF_5',D_315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_780])).

tff(c_220,plain,(
    ! [A_250,B_251,C_252] :
      ( k9_subset_1(A_250,B_251,C_252) = k3_xboole_0(B_251,C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(A_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_232,plain,(
    ! [B_251] : k9_subset_1('#skF_1',B_251,'#skF_4') = k3_xboole_0(B_251,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_220])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_115,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_257,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_232,c_115])).

tff(c_789,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_257])).

tff(c_961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_879,c_218,c_879,c_788,c_789])).

tff(c_962,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1100,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_962])).

tff(c_3340,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3329,c_1100])).

tff(c_3354,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1050,c_1051,c_2080,c_1823,c_2080,c_1823,c_2285,c_3340])).

tff(c_3356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3354])).

tff(c_3357,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_962])).

tff(c_5951,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5942,c_3357])).

tff(c_5962,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1050,c_1051,c_4375,c_3894,c_4375,c_3894,c_4629,c_5951])).

tff(c_5964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:23:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.21/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.07/2.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.07/2.76  
% 8.07/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.07/2.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.07/2.76  
% 8.07/2.76  %Foreground sorts:
% 8.07/2.76  
% 8.07/2.76  
% 8.07/2.76  %Background operators:
% 8.07/2.76  
% 8.07/2.76  
% 8.07/2.76  %Foreground operators:
% 8.07/2.76  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 8.07/2.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.07/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.07/2.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.07/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.07/2.76  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.07/2.76  tff('#skF_5', type, '#skF_5': $i).
% 8.07/2.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.07/2.76  tff('#skF_6', type, '#skF_6': $i).
% 8.07/2.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.07/2.76  tff('#skF_2', type, '#skF_2': $i).
% 8.07/2.76  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.07/2.76  tff('#skF_3', type, '#skF_3': $i).
% 8.07/2.76  tff('#skF_1', type, '#skF_1': $i).
% 8.07/2.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.07/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.07/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.07/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.07/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.07/2.76  tff('#skF_4', type, '#skF_4': $i).
% 8.07/2.76  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.07/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.07/2.76  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.07/2.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.07/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.07/2.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.07/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.07/2.76  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.07/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.07/2.76  
% 8.25/2.79  tff(f_225, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 8.25/2.79  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.25/2.79  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.25/2.79  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.25/2.79  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 8.25/2.79  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 8.25/2.79  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.25/2.79  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 8.25/2.79  tff(f_87, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.25/2.79  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.25/2.79  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.25/2.79  tff(f_183, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 8.25/2.79  tff(f_101, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.25/2.79  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 8.25/2.79  tff(c_76, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.25/2.79  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_966, plain, (![B_331, A_332]: (v1_relat_1(B_331) | ~m1_subset_1(B_331, k1_zfmisc_1(A_332)) | ~v1_relat_1(A_332))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.25/2.79  tff(c_972, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_966])).
% 8.25/2.79  tff(c_984, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_972])).
% 8.25/2.79  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.25/2.79  tff(c_1016, plain, (![B_343, A_344]: (k7_relat_1(B_343, A_344)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_343), A_344) | ~v1_relat_1(B_343))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.25/2.79  tff(c_1040, plain, (![B_345]: (k7_relat_1(B_345, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_345))), inference(resolution, [status(thm)], [c_6, c_1016])).
% 8.25/2.79  tff(c_1050, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_984, c_1040])).
% 8.25/2.79  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_969, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_966])).
% 8.25/2.79  tff(c_981, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_969])).
% 8.25/2.79  tff(c_1051, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_981, c_1040])).
% 8.25/2.79  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_64, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | ~r1_subset_1(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.25/2.79  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_987, plain, (![C_333, A_334, B_335]: (v4_relat_1(C_333, A_334) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.25/2.79  tff(c_994, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_987])).
% 8.25/2.79  tff(c_1087, plain, (![B_351, A_352]: (k1_relat_1(B_351)=A_352 | ~v1_partfun1(B_351, A_352) | ~v4_relat_1(B_351, A_352) | ~v1_relat_1(B_351))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.25/2.79  tff(c_1093, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_994, c_1087])).
% 8.25/2.79  tff(c_1099, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_1093])).
% 8.25/2.79  tff(c_3896, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1099])).
% 8.25/2.79  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_4150, plain, (![C_835, A_836, B_837]: (v1_partfun1(C_835, A_836) | ~v1_funct_2(C_835, A_836, B_837) | ~v1_funct_1(C_835) | ~m1_subset_1(C_835, k1_zfmisc_1(k2_zfmisc_1(A_836, B_837))) | v1_xboole_0(B_837))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.25/2.79  tff(c_4153, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_4150])).
% 8.25/2.79  tff(c_4159, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4153])).
% 8.25/2.79  tff(c_4161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3896, c_4159])).
% 8.25/2.79  tff(c_4162, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1099])).
% 8.25/2.79  tff(c_16, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.25/2.79  tff(c_4170, plain, (![A_15]: (k7_relat_1('#skF_5', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4162, c_16])).
% 8.25/2.79  tff(c_4214, plain, (![A_841]: (k7_relat_1('#skF_5', A_841)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_841))), inference(demodulation, [status(thm), theory('equality')], [c_981, c_4170])).
% 8.25/2.79  tff(c_4221, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_4214])).
% 8.25/2.79  tff(c_4355, plain, (![B_850]: (k7_relat_1('#skF_5', B_850)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_850) | v1_xboole_0(B_850))), inference(negUnitSimplification, [status(thm)], [c_72, c_4221])).
% 8.25/2.79  tff(c_4358, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_4355])).
% 8.25/2.79  tff(c_4361, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_4358])).
% 8.25/2.79  tff(c_18, plain, (![B_16, A_15]: (r1_xboole_0(k1_relat_1(B_16), A_15) | k7_relat_1(B_16, A_15)!=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.25/2.79  tff(c_4173, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k7_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4162, c_18])).
% 8.25/2.79  tff(c_4203, plain, (![A_840]: (r1_xboole_0('#skF_3', A_840) | k7_relat_1('#skF_5', A_840)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_981, c_4173])).
% 8.25/2.79  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.25/2.79  tff(c_4213, plain, (![A_840]: (k3_xboole_0('#skF_3', A_840)=k1_xboole_0 | k7_relat_1('#skF_5', A_840)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4203, c_2])).
% 8.25/2.79  tff(c_4375, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4361, c_4213])).
% 8.25/2.79  tff(c_3882, plain, (![A_804, B_805, C_806]: (k9_subset_1(A_804, B_805, C_806)=k3_xboole_0(B_805, C_806) | ~m1_subset_1(C_806, k1_zfmisc_1(A_804)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.25/2.79  tff(c_3894, plain, (![B_805]: (k9_subset_1('#skF_1', B_805, '#skF_4')=k3_xboole_0(B_805, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_3882])).
% 8.25/2.79  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_4560, plain, (![D_876, A_879, E_880, B_878, F_877, C_875]: (v1_funct_1(k1_tmap_1(A_879, B_878, C_875, D_876, E_880, F_877)) | ~m1_subset_1(F_877, k1_zfmisc_1(k2_zfmisc_1(D_876, B_878))) | ~v1_funct_2(F_877, D_876, B_878) | ~v1_funct_1(F_877) | ~m1_subset_1(E_880, k1_zfmisc_1(k2_zfmisc_1(C_875, B_878))) | ~v1_funct_2(E_880, C_875, B_878) | ~v1_funct_1(E_880) | ~m1_subset_1(D_876, k1_zfmisc_1(A_879)) | v1_xboole_0(D_876) | ~m1_subset_1(C_875, k1_zfmisc_1(A_879)) | v1_xboole_0(C_875) | v1_xboole_0(B_878) | v1_xboole_0(A_879))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.25/2.79  tff(c_4564, plain, (![A_879, C_875, E_880]: (v1_funct_1(k1_tmap_1(A_879, '#skF_2', C_875, '#skF_4', E_880, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_880, k1_zfmisc_1(k2_zfmisc_1(C_875, '#skF_2'))) | ~v1_funct_2(E_880, C_875, '#skF_2') | ~v1_funct_1(E_880) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_879)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_875, k1_zfmisc_1(A_879)) | v1_xboole_0(C_875) | v1_xboole_0('#skF_2') | v1_xboole_0(A_879))), inference(resolution, [status(thm)], [c_52, c_4560])).
% 8.25/2.79  tff(c_4571, plain, (![A_879, C_875, E_880]: (v1_funct_1(k1_tmap_1(A_879, '#skF_2', C_875, '#skF_4', E_880, '#skF_6')) | ~m1_subset_1(E_880, k1_zfmisc_1(k2_zfmisc_1(C_875, '#skF_2'))) | ~v1_funct_2(E_880, C_875, '#skF_2') | ~v1_funct_1(E_880) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_879)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_875, k1_zfmisc_1(A_879)) | v1_xboole_0(C_875) | v1_xboole_0('#skF_2') | v1_xboole_0(A_879))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4564])).
% 8.25/2.79  tff(c_4602, plain, (![A_892, C_893, E_894]: (v1_funct_1(k1_tmap_1(A_892, '#skF_2', C_893, '#skF_4', E_894, '#skF_6')) | ~m1_subset_1(E_894, k1_zfmisc_1(k2_zfmisc_1(C_893, '#skF_2'))) | ~v1_funct_2(E_894, C_893, '#skF_2') | ~v1_funct_1(E_894) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_892)) | ~m1_subset_1(C_893, k1_zfmisc_1(A_892)) | v1_xboole_0(C_893) | v1_xboole_0(A_892))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_4571])).
% 8.25/2.79  tff(c_4604, plain, (![A_892]: (v1_funct_1(k1_tmap_1(A_892, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_892)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_892)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_892))), inference(resolution, [status(thm)], [c_58, c_4602])).
% 8.25/2.79  tff(c_4609, plain, (![A_892]: (v1_funct_1(k1_tmap_1(A_892, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_892)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_892)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_892))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4604])).
% 8.25/2.79  tff(c_4622, plain, (![A_896]: (v1_funct_1(k1_tmap_1(A_896, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_896)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_896)) | v1_xboole_0(A_896))), inference(negUnitSimplification, [status(thm)], [c_72, c_4609])).
% 8.25/2.79  tff(c_4625, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4622])).
% 8.25/2.79  tff(c_4628, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4625])).
% 8.25/2.79  tff(c_4629, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_4628])).
% 8.25/2.79  tff(c_4382, plain, (![A_851, B_852, C_853, D_854]: (k2_partfun1(A_851, B_852, C_853, D_854)=k7_relat_1(C_853, D_854) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(A_851, B_852))) | ~v1_funct_1(C_853))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.25/2.79  tff(c_4384, plain, (![D_854]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_854)=k7_relat_1('#skF_5', D_854) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_4382])).
% 8.25/2.79  tff(c_4389, plain, (![D_854]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_854)=k7_relat_1('#skF_5', D_854))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4384])).
% 8.25/2.79  tff(c_4386, plain, (![D_854]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_854)=k7_relat_1('#skF_6', D_854) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_4382])).
% 8.25/2.79  tff(c_4392, plain, (![D_854]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_854)=k7_relat_1('#skF_6', D_854))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4386])).
% 8.25/2.79  tff(c_46, plain, (![D_162, C_161, A_159, E_163, B_160, F_164]: (v1_funct_2(k1_tmap_1(A_159, B_160, C_161, D_162, E_163, F_164), k4_subset_1(A_159, C_161, D_162), B_160) | ~m1_subset_1(F_164, k1_zfmisc_1(k2_zfmisc_1(D_162, B_160))) | ~v1_funct_2(F_164, D_162, B_160) | ~v1_funct_1(F_164) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(C_161, B_160))) | ~v1_funct_2(E_163, C_161, B_160) | ~v1_funct_1(E_163) | ~m1_subset_1(D_162, k1_zfmisc_1(A_159)) | v1_xboole_0(D_162) | ~m1_subset_1(C_161, k1_zfmisc_1(A_159)) | v1_xboole_0(C_161) | v1_xboole_0(B_160) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.25/2.79  tff(c_44, plain, (![D_162, C_161, A_159, E_163, B_160, F_164]: (m1_subset_1(k1_tmap_1(A_159, B_160, C_161, D_162, E_163, F_164), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_159, C_161, D_162), B_160))) | ~m1_subset_1(F_164, k1_zfmisc_1(k2_zfmisc_1(D_162, B_160))) | ~v1_funct_2(F_164, D_162, B_160) | ~v1_funct_1(F_164) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(C_161, B_160))) | ~v1_funct_2(E_163, C_161, B_160) | ~v1_funct_1(E_163) | ~m1_subset_1(D_162, k1_zfmisc_1(A_159)) | v1_xboole_0(D_162) | ~m1_subset_1(C_161, k1_zfmisc_1(A_159)) | v1_xboole_0(C_161) | v1_xboole_0(B_160) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.25/2.79  tff(c_4778, plain, (![F_925, C_929, A_927, E_924, B_928, D_926]: (k2_partfun1(k4_subset_1(A_927, C_929, D_926), B_928, k1_tmap_1(A_927, B_928, C_929, D_926, E_924, F_925), C_929)=E_924 | ~m1_subset_1(k1_tmap_1(A_927, B_928, C_929, D_926, E_924, F_925), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_927, C_929, D_926), B_928))) | ~v1_funct_2(k1_tmap_1(A_927, B_928, C_929, D_926, E_924, F_925), k4_subset_1(A_927, C_929, D_926), B_928) | ~v1_funct_1(k1_tmap_1(A_927, B_928, C_929, D_926, E_924, F_925)) | k2_partfun1(D_926, B_928, F_925, k9_subset_1(A_927, C_929, D_926))!=k2_partfun1(C_929, B_928, E_924, k9_subset_1(A_927, C_929, D_926)) | ~m1_subset_1(F_925, k1_zfmisc_1(k2_zfmisc_1(D_926, B_928))) | ~v1_funct_2(F_925, D_926, B_928) | ~v1_funct_1(F_925) | ~m1_subset_1(E_924, k1_zfmisc_1(k2_zfmisc_1(C_929, B_928))) | ~v1_funct_2(E_924, C_929, B_928) | ~v1_funct_1(E_924) | ~m1_subset_1(D_926, k1_zfmisc_1(A_927)) | v1_xboole_0(D_926) | ~m1_subset_1(C_929, k1_zfmisc_1(A_927)) | v1_xboole_0(C_929) | v1_xboole_0(B_928) | v1_xboole_0(A_927))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.25/2.79  tff(c_5023, plain, (![E_1029, C_1024, B_1027, A_1028, F_1026, D_1025]: (k2_partfun1(k4_subset_1(A_1028, C_1024, D_1025), B_1027, k1_tmap_1(A_1028, B_1027, C_1024, D_1025, E_1029, F_1026), C_1024)=E_1029 | ~v1_funct_2(k1_tmap_1(A_1028, B_1027, C_1024, D_1025, E_1029, F_1026), k4_subset_1(A_1028, C_1024, D_1025), B_1027) | ~v1_funct_1(k1_tmap_1(A_1028, B_1027, C_1024, D_1025, E_1029, F_1026)) | k2_partfun1(D_1025, B_1027, F_1026, k9_subset_1(A_1028, C_1024, D_1025))!=k2_partfun1(C_1024, B_1027, E_1029, k9_subset_1(A_1028, C_1024, D_1025)) | ~m1_subset_1(F_1026, k1_zfmisc_1(k2_zfmisc_1(D_1025, B_1027))) | ~v1_funct_2(F_1026, D_1025, B_1027) | ~v1_funct_1(F_1026) | ~m1_subset_1(E_1029, k1_zfmisc_1(k2_zfmisc_1(C_1024, B_1027))) | ~v1_funct_2(E_1029, C_1024, B_1027) | ~v1_funct_1(E_1029) | ~m1_subset_1(D_1025, k1_zfmisc_1(A_1028)) | v1_xboole_0(D_1025) | ~m1_subset_1(C_1024, k1_zfmisc_1(A_1028)) | v1_xboole_0(C_1024) | v1_xboole_0(B_1027) | v1_xboole_0(A_1028))), inference(resolution, [status(thm)], [c_44, c_4778])).
% 8.25/2.79  tff(c_5530, plain, (![F_1090, C_1088, D_1089, A_1092, E_1093, B_1091]: (k2_partfun1(k4_subset_1(A_1092, C_1088, D_1089), B_1091, k1_tmap_1(A_1092, B_1091, C_1088, D_1089, E_1093, F_1090), C_1088)=E_1093 | ~v1_funct_1(k1_tmap_1(A_1092, B_1091, C_1088, D_1089, E_1093, F_1090)) | k2_partfun1(D_1089, B_1091, F_1090, k9_subset_1(A_1092, C_1088, D_1089))!=k2_partfun1(C_1088, B_1091, E_1093, k9_subset_1(A_1092, C_1088, D_1089)) | ~m1_subset_1(F_1090, k1_zfmisc_1(k2_zfmisc_1(D_1089, B_1091))) | ~v1_funct_2(F_1090, D_1089, B_1091) | ~v1_funct_1(F_1090) | ~m1_subset_1(E_1093, k1_zfmisc_1(k2_zfmisc_1(C_1088, B_1091))) | ~v1_funct_2(E_1093, C_1088, B_1091) | ~v1_funct_1(E_1093) | ~m1_subset_1(D_1089, k1_zfmisc_1(A_1092)) | v1_xboole_0(D_1089) | ~m1_subset_1(C_1088, k1_zfmisc_1(A_1092)) | v1_xboole_0(C_1088) | v1_xboole_0(B_1091) | v1_xboole_0(A_1092))), inference(resolution, [status(thm)], [c_46, c_5023])).
% 8.25/2.79  tff(c_5536, plain, (![A_1092, C_1088, E_1093]: (k2_partfun1(k4_subset_1(A_1092, C_1088, '#skF_4'), '#skF_2', k1_tmap_1(A_1092, '#skF_2', C_1088, '#skF_4', E_1093, '#skF_6'), C_1088)=E_1093 | ~v1_funct_1(k1_tmap_1(A_1092, '#skF_2', C_1088, '#skF_4', E_1093, '#skF_6')) | k2_partfun1(C_1088, '#skF_2', E_1093, k9_subset_1(A_1092, C_1088, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1092, C_1088, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1093, k1_zfmisc_1(k2_zfmisc_1(C_1088, '#skF_2'))) | ~v1_funct_2(E_1093, C_1088, '#skF_2') | ~v1_funct_1(E_1093) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1092)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1088, k1_zfmisc_1(A_1092)) | v1_xboole_0(C_1088) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1092))), inference(resolution, [status(thm)], [c_52, c_5530])).
% 8.25/2.79  tff(c_5544, plain, (![A_1092, C_1088, E_1093]: (k2_partfun1(k4_subset_1(A_1092, C_1088, '#skF_4'), '#skF_2', k1_tmap_1(A_1092, '#skF_2', C_1088, '#skF_4', E_1093, '#skF_6'), C_1088)=E_1093 | ~v1_funct_1(k1_tmap_1(A_1092, '#skF_2', C_1088, '#skF_4', E_1093, '#skF_6')) | k2_partfun1(C_1088, '#skF_2', E_1093, k9_subset_1(A_1092, C_1088, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1092, C_1088, '#skF_4')) | ~m1_subset_1(E_1093, k1_zfmisc_1(k2_zfmisc_1(C_1088, '#skF_2'))) | ~v1_funct_2(E_1093, C_1088, '#skF_2') | ~v1_funct_1(E_1093) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1092)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1088, k1_zfmisc_1(A_1092)) | v1_xboole_0(C_1088) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1092))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4392, c_5536])).
% 8.25/2.79  tff(c_5740, plain, (![A_1128, C_1129, E_1130]: (k2_partfun1(k4_subset_1(A_1128, C_1129, '#skF_4'), '#skF_2', k1_tmap_1(A_1128, '#skF_2', C_1129, '#skF_4', E_1130, '#skF_6'), C_1129)=E_1130 | ~v1_funct_1(k1_tmap_1(A_1128, '#skF_2', C_1129, '#skF_4', E_1130, '#skF_6')) | k2_partfun1(C_1129, '#skF_2', E_1130, k9_subset_1(A_1128, C_1129, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1128, C_1129, '#skF_4')) | ~m1_subset_1(E_1130, k1_zfmisc_1(k2_zfmisc_1(C_1129, '#skF_2'))) | ~v1_funct_2(E_1130, C_1129, '#skF_2') | ~v1_funct_1(E_1130) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1128)) | ~m1_subset_1(C_1129, k1_zfmisc_1(A_1128)) | v1_xboole_0(C_1129) | v1_xboole_0(A_1128))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_5544])).
% 8.25/2.79  tff(c_5745, plain, (![A_1128]: (k2_partfun1(k4_subset_1(A_1128, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1128, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1128, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1128, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1128, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1128)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1128)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1128))), inference(resolution, [status(thm)], [c_58, c_5740])).
% 8.25/2.79  tff(c_5753, plain, (![A_1128]: (k2_partfun1(k4_subset_1(A_1128, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1128, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1128, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1128, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1128, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1128)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1128)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1128))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4389, c_5745])).
% 8.25/2.79  tff(c_5942, plain, (![A_1146]: (k2_partfun1(k4_subset_1(A_1146, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1146, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1146, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1146, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1146, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1146)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1146)) | v1_xboole_0(A_1146))), inference(negUnitSimplification, [status(thm)], [c_72, c_5753])).
% 8.25/2.79  tff(c_1552, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1099])).
% 8.25/2.79  tff(c_1797, plain, (![C_440, A_441, B_442]: (v1_partfun1(C_440, A_441) | ~v1_funct_2(C_440, A_441, B_442) | ~v1_funct_1(C_440) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))) | v1_xboole_0(B_442))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.25/2.79  tff(c_1800, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_1797])).
% 8.25/2.79  tff(c_1806, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1800])).
% 8.25/2.79  tff(c_1808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1552, c_1806])).
% 8.25/2.79  tff(c_1809, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1099])).
% 8.25/2.79  tff(c_1830, plain, (![A_15]: (k7_relat_1('#skF_5', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1809, c_16])).
% 8.25/2.79  tff(c_1885, plain, (![A_450]: (k7_relat_1('#skF_5', A_450)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_450))), inference(demodulation, [status(thm), theory('equality')], [c_981, c_1830])).
% 8.25/2.79  tff(c_1892, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1885])).
% 8.25/2.79  tff(c_2057, plain, (![B_469]: (k7_relat_1('#skF_5', B_469)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_469) | v1_xboole_0(B_469))), inference(negUnitSimplification, [status(thm)], [c_72, c_1892])).
% 8.25/2.79  tff(c_2063, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2057])).
% 8.25/2.79  tff(c_2067, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_2063])).
% 8.25/2.79  tff(c_1833, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k7_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1809, c_18])).
% 8.25/2.79  tff(c_1863, plain, (![A_448]: (r1_xboole_0('#skF_3', A_448) | k7_relat_1('#skF_5', A_448)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_981, c_1833])).
% 8.25/2.79  tff(c_1873, plain, (![A_448]: (k3_xboole_0('#skF_3', A_448)=k1_xboole_0 | k7_relat_1('#skF_5', A_448)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1863, c_2])).
% 8.25/2.79  tff(c_2080, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2067, c_1873])).
% 8.25/2.79  tff(c_1811, plain, (![A_443, B_444, C_445]: (k9_subset_1(A_443, B_444, C_445)=k3_xboole_0(B_444, C_445) | ~m1_subset_1(C_445, k1_zfmisc_1(A_443)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.25/2.79  tff(c_1823, plain, (![B_444]: (k9_subset_1('#skF_1', B_444, '#skF_4')=k3_xboole_0(B_444, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_1811])).
% 8.25/2.79  tff(c_2176, plain, (![F_481, A_483, C_479, B_482, D_480, E_484]: (v1_funct_1(k1_tmap_1(A_483, B_482, C_479, D_480, E_484, F_481)) | ~m1_subset_1(F_481, k1_zfmisc_1(k2_zfmisc_1(D_480, B_482))) | ~v1_funct_2(F_481, D_480, B_482) | ~v1_funct_1(F_481) | ~m1_subset_1(E_484, k1_zfmisc_1(k2_zfmisc_1(C_479, B_482))) | ~v1_funct_2(E_484, C_479, B_482) | ~v1_funct_1(E_484) | ~m1_subset_1(D_480, k1_zfmisc_1(A_483)) | v1_xboole_0(D_480) | ~m1_subset_1(C_479, k1_zfmisc_1(A_483)) | v1_xboole_0(C_479) | v1_xboole_0(B_482) | v1_xboole_0(A_483))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.25/2.79  tff(c_2180, plain, (![A_483, C_479, E_484]: (v1_funct_1(k1_tmap_1(A_483, '#skF_2', C_479, '#skF_4', E_484, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_484, k1_zfmisc_1(k2_zfmisc_1(C_479, '#skF_2'))) | ~v1_funct_2(E_484, C_479, '#skF_2') | ~v1_funct_1(E_484) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_483)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_479, k1_zfmisc_1(A_483)) | v1_xboole_0(C_479) | v1_xboole_0('#skF_2') | v1_xboole_0(A_483))), inference(resolution, [status(thm)], [c_52, c_2176])).
% 8.25/2.79  tff(c_2187, plain, (![A_483, C_479, E_484]: (v1_funct_1(k1_tmap_1(A_483, '#skF_2', C_479, '#skF_4', E_484, '#skF_6')) | ~m1_subset_1(E_484, k1_zfmisc_1(k2_zfmisc_1(C_479, '#skF_2'))) | ~v1_funct_2(E_484, C_479, '#skF_2') | ~v1_funct_1(E_484) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_483)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_479, k1_zfmisc_1(A_483)) | v1_xboole_0(C_479) | v1_xboole_0('#skF_2') | v1_xboole_0(A_483))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2180])).
% 8.25/2.79  tff(c_2257, plain, (![A_494, C_495, E_496]: (v1_funct_1(k1_tmap_1(A_494, '#skF_2', C_495, '#skF_4', E_496, '#skF_6')) | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(C_495, '#skF_2'))) | ~v1_funct_2(E_496, C_495, '#skF_2') | ~v1_funct_1(E_496) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_494)) | ~m1_subset_1(C_495, k1_zfmisc_1(A_494)) | v1_xboole_0(C_495) | v1_xboole_0(A_494))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_2187])).
% 8.25/2.79  tff(c_2259, plain, (![A_494]: (v1_funct_1(k1_tmap_1(A_494, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_494)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_494)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_494))), inference(resolution, [status(thm)], [c_58, c_2257])).
% 8.25/2.79  tff(c_2264, plain, (![A_494]: (v1_funct_1(k1_tmap_1(A_494, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_494)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_494)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_494))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2259])).
% 8.25/2.79  tff(c_2278, plain, (![A_504]: (v1_funct_1(k1_tmap_1(A_504, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_504)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_504)) | v1_xboole_0(A_504))), inference(negUnitSimplification, [status(thm)], [c_72, c_2264])).
% 8.25/2.79  tff(c_2281, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_2278])).
% 8.25/2.79  tff(c_2284, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2281])).
% 8.25/2.79  tff(c_2285, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_2284])).
% 8.25/2.79  tff(c_1931, plain, (![A_452, B_453, C_454, D_455]: (k2_partfun1(A_452, B_453, C_454, D_455)=k7_relat_1(C_454, D_455) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))) | ~v1_funct_1(C_454))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.25/2.79  tff(c_1933, plain, (![D_455]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_455)=k7_relat_1('#skF_5', D_455) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_1931])).
% 8.25/2.79  tff(c_1938, plain, (![D_455]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_455)=k7_relat_1('#skF_5', D_455))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1933])).
% 8.25/2.79  tff(c_1935, plain, (![D_455]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_455)=k7_relat_1('#skF_6', D_455) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_1931])).
% 8.25/2.79  tff(c_1941, plain, (![D_455]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_455)=k7_relat_1('#skF_6', D_455))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1935])).
% 8.25/2.79  tff(c_2376, plain, (![E_521, B_525, F_522, C_526, D_523, A_524]: (k2_partfun1(k4_subset_1(A_524, C_526, D_523), B_525, k1_tmap_1(A_524, B_525, C_526, D_523, E_521, F_522), D_523)=F_522 | ~m1_subset_1(k1_tmap_1(A_524, B_525, C_526, D_523, E_521, F_522), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_524, C_526, D_523), B_525))) | ~v1_funct_2(k1_tmap_1(A_524, B_525, C_526, D_523, E_521, F_522), k4_subset_1(A_524, C_526, D_523), B_525) | ~v1_funct_1(k1_tmap_1(A_524, B_525, C_526, D_523, E_521, F_522)) | k2_partfun1(D_523, B_525, F_522, k9_subset_1(A_524, C_526, D_523))!=k2_partfun1(C_526, B_525, E_521, k9_subset_1(A_524, C_526, D_523)) | ~m1_subset_1(F_522, k1_zfmisc_1(k2_zfmisc_1(D_523, B_525))) | ~v1_funct_2(F_522, D_523, B_525) | ~v1_funct_1(F_522) | ~m1_subset_1(E_521, k1_zfmisc_1(k2_zfmisc_1(C_526, B_525))) | ~v1_funct_2(E_521, C_526, B_525) | ~v1_funct_1(E_521) | ~m1_subset_1(D_523, k1_zfmisc_1(A_524)) | v1_xboole_0(D_523) | ~m1_subset_1(C_526, k1_zfmisc_1(A_524)) | v1_xboole_0(C_526) | v1_xboole_0(B_525) | v1_xboole_0(A_524))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.25/2.79  tff(c_2760, plain, (![F_640, D_639, A_642, C_638, E_643, B_641]: (k2_partfun1(k4_subset_1(A_642, C_638, D_639), B_641, k1_tmap_1(A_642, B_641, C_638, D_639, E_643, F_640), D_639)=F_640 | ~v1_funct_2(k1_tmap_1(A_642, B_641, C_638, D_639, E_643, F_640), k4_subset_1(A_642, C_638, D_639), B_641) | ~v1_funct_1(k1_tmap_1(A_642, B_641, C_638, D_639, E_643, F_640)) | k2_partfun1(D_639, B_641, F_640, k9_subset_1(A_642, C_638, D_639))!=k2_partfun1(C_638, B_641, E_643, k9_subset_1(A_642, C_638, D_639)) | ~m1_subset_1(F_640, k1_zfmisc_1(k2_zfmisc_1(D_639, B_641))) | ~v1_funct_2(F_640, D_639, B_641) | ~v1_funct_1(F_640) | ~m1_subset_1(E_643, k1_zfmisc_1(k2_zfmisc_1(C_638, B_641))) | ~v1_funct_2(E_643, C_638, B_641) | ~v1_funct_1(E_643) | ~m1_subset_1(D_639, k1_zfmisc_1(A_642)) | v1_xboole_0(D_639) | ~m1_subset_1(C_638, k1_zfmisc_1(A_642)) | v1_xboole_0(C_638) | v1_xboole_0(B_641) | v1_xboole_0(A_642))), inference(resolution, [status(thm)], [c_44, c_2376])).
% 8.25/2.79  tff(c_3155, plain, (![C_702, F_704, A_706, D_703, E_707, B_705]: (k2_partfun1(k4_subset_1(A_706, C_702, D_703), B_705, k1_tmap_1(A_706, B_705, C_702, D_703, E_707, F_704), D_703)=F_704 | ~v1_funct_1(k1_tmap_1(A_706, B_705, C_702, D_703, E_707, F_704)) | k2_partfun1(D_703, B_705, F_704, k9_subset_1(A_706, C_702, D_703))!=k2_partfun1(C_702, B_705, E_707, k9_subset_1(A_706, C_702, D_703)) | ~m1_subset_1(F_704, k1_zfmisc_1(k2_zfmisc_1(D_703, B_705))) | ~v1_funct_2(F_704, D_703, B_705) | ~v1_funct_1(F_704) | ~m1_subset_1(E_707, k1_zfmisc_1(k2_zfmisc_1(C_702, B_705))) | ~v1_funct_2(E_707, C_702, B_705) | ~v1_funct_1(E_707) | ~m1_subset_1(D_703, k1_zfmisc_1(A_706)) | v1_xboole_0(D_703) | ~m1_subset_1(C_702, k1_zfmisc_1(A_706)) | v1_xboole_0(C_702) | v1_xboole_0(B_705) | v1_xboole_0(A_706))), inference(resolution, [status(thm)], [c_46, c_2760])).
% 8.25/2.79  tff(c_3161, plain, (![A_706, C_702, E_707]: (k2_partfun1(k4_subset_1(A_706, C_702, '#skF_4'), '#skF_2', k1_tmap_1(A_706, '#skF_2', C_702, '#skF_4', E_707, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_706, '#skF_2', C_702, '#skF_4', E_707, '#skF_6')) | k2_partfun1(C_702, '#skF_2', E_707, k9_subset_1(A_706, C_702, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_706, C_702, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_707, k1_zfmisc_1(k2_zfmisc_1(C_702, '#skF_2'))) | ~v1_funct_2(E_707, C_702, '#skF_2') | ~v1_funct_1(E_707) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_706)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_702, k1_zfmisc_1(A_706)) | v1_xboole_0(C_702) | v1_xboole_0('#skF_2') | v1_xboole_0(A_706))), inference(resolution, [status(thm)], [c_52, c_3155])).
% 8.25/2.79  tff(c_3169, plain, (![A_706, C_702, E_707]: (k2_partfun1(k4_subset_1(A_706, C_702, '#skF_4'), '#skF_2', k1_tmap_1(A_706, '#skF_2', C_702, '#skF_4', E_707, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_706, '#skF_2', C_702, '#skF_4', E_707, '#skF_6')) | k2_partfun1(C_702, '#skF_2', E_707, k9_subset_1(A_706, C_702, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_706, C_702, '#skF_4')) | ~m1_subset_1(E_707, k1_zfmisc_1(k2_zfmisc_1(C_702, '#skF_2'))) | ~v1_funct_2(E_707, C_702, '#skF_2') | ~v1_funct_1(E_707) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_706)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_702, k1_zfmisc_1(A_706)) | v1_xboole_0(C_702) | v1_xboole_0('#skF_2') | v1_xboole_0(A_706))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1941, c_3161])).
% 8.25/2.79  tff(c_3250, plain, (![A_728, C_729, E_730]: (k2_partfun1(k4_subset_1(A_728, C_729, '#skF_4'), '#skF_2', k1_tmap_1(A_728, '#skF_2', C_729, '#skF_4', E_730, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_728, '#skF_2', C_729, '#skF_4', E_730, '#skF_6')) | k2_partfun1(C_729, '#skF_2', E_730, k9_subset_1(A_728, C_729, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_728, C_729, '#skF_4')) | ~m1_subset_1(E_730, k1_zfmisc_1(k2_zfmisc_1(C_729, '#skF_2'))) | ~v1_funct_2(E_730, C_729, '#skF_2') | ~v1_funct_1(E_730) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_728)) | ~m1_subset_1(C_729, k1_zfmisc_1(A_728)) | v1_xboole_0(C_729) | v1_xboole_0(A_728))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_3169])).
% 8.25/2.79  tff(c_3255, plain, (![A_728]: (k2_partfun1(k4_subset_1(A_728, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_728, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_728, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_728, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_728, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_728)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_728)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_728))), inference(resolution, [status(thm)], [c_58, c_3250])).
% 8.25/2.79  tff(c_3263, plain, (![A_728]: (k2_partfun1(k4_subset_1(A_728, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_728, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_728, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_728, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_728, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_728)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_728)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_728))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1938, c_3255])).
% 8.25/2.79  tff(c_3329, plain, (![A_741]: (k2_partfun1(k4_subset_1(A_741, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_741, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_741, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_741, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_741, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_741)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_741)) | v1_xboole_0(A_741))), inference(negUnitSimplification, [status(thm)], [c_72, c_3263])).
% 8.25/2.79  tff(c_118, plain, (![B_232, A_233]: (v1_relat_1(B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(A_233)) | ~v1_relat_1(A_233))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.25/2.79  tff(c_124, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_118])).
% 8.25/2.79  tff(c_136, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_124])).
% 8.25/2.79  tff(c_187, plain, (![B_247, A_248]: (k7_relat_1(B_247, A_248)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_247), A_248) | ~v1_relat_1(B_247))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.25/2.79  tff(c_207, plain, (![B_249]: (k7_relat_1(B_249, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_6, c_187])).
% 8.25/2.79  tff(c_217, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_136, c_207])).
% 8.25/2.79  tff(c_121, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_118])).
% 8.25/2.79  tff(c_133, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_121])).
% 8.25/2.79  tff(c_139, plain, (![C_234, A_235, B_236]: (v4_relat_1(C_234, A_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.25/2.79  tff(c_146, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_139])).
% 8.25/2.79  tff(c_285, plain, (![B_259, A_260]: (k1_relat_1(B_259)=A_260 | ~v1_partfun1(B_259, A_260) | ~v4_relat_1(B_259, A_260) | ~v1_relat_1(B_259))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.25/2.79  tff(c_291, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_146, c_285])).
% 8.25/2.79  tff(c_297, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_291])).
% 8.25/2.79  tff(c_524, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_297])).
% 8.25/2.79  tff(c_664, plain, (![C_303, A_304, B_305]: (v1_partfun1(C_303, A_304) | ~v1_funct_2(C_303, A_304, B_305) | ~v1_funct_1(C_303) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_304, B_305))) | v1_xboole_0(B_305))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.25/2.79  tff(c_667, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_664])).
% 8.25/2.79  tff(c_673, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_667])).
% 8.25/2.79  tff(c_675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_524, c_673])).
% 8.25/2.79  tff(c_676, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_297])).
% 8.25/2.79  tff(c_681, plain, (![A_15]: (k7_relat_1('#skF_5', A_15)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_15) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_676, c_16])).
% 8.25/2.79  tff(c_720, plain, (![A_308]: (k7_relat_1('#skF_5', A_308)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_308))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_681])).
% 8.25/2.79  tff(c_727, plain, (![B_18]: (k7_relat_1('#skF_5', B_18)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_18) | v1_xboole_0(B_18) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_720])).
% 8.25/2.79  tff(c_859, plain, (![B_321]: (k7_relat_1('#skF_5', B_321)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_321) | v1_xboole_0(B_321))), inference(negUnitSimplification, [status(thm)], [c_72, c_727])).
% 8.25/2.79  tff(c_862, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_859])).
% 8.25/2.79  tff(c_865, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_862])).
% 8.25/2.79  tff(c_687, plain, (![A_15]: (r1_xboole_0('#skF_3', A_15) | k7_relat_1('#skF_5', A_15)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_676, c_18])).
% 8.25/2.79  tff(c_709, plain, (![A_307]: (r1_xboole_0('#skF_3', A_307) | k7_relat_1('#skF_5', A_307)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_687])).
% 8.25/2.79  tff(c_719, plain, (![A_307]: (k3_xboole_0('#skF_3', A_307)=k1_xboole_0 | k7_relat_1('#skF_5', A_307)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_709, c_2])).
% 8.25/2.79  tff(c_879, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_865, c_719])).
% 8.25/2.79  tff(c_218, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_133, c_207])).
% 8.25/2.79  tff(c_778, plain, (![A_312, B_313, C_314, D_315]: (k2_partfun1(A_312, B_313, C_314, D_315)=k7_relat_1(C_314, D_315) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))) | ~v1_funct_1(C_314))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.25/2.79  tff(c_782, plain, (![D_315]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_315)=k7_relat_1('#skF_6', D_315) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_778])).
% 8.25/2.79  tff(c_788, plain, (![D_315]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_315)=k7_relat_1('#skF_6', D_315))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_782])).
% 8.25/2.79  tff(c_780, plain, (![D_315]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_315)=k7_relat_1('#skF_5', D_315) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_778])).
% 8.25/2.79  tff(c_785, plain, (![D_315]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_315)=k7_relat_1('#skF_5', D_315))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_780])).
% 8.25/2.79  tff(c_220, plain, (![A_250, B_251, C_252]: (k9_subset_1(A_250, B_251, C_252)=k3_xboole_0(B_251, C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(A_250)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.25/2.79  tff(c_232, plain, (![B_251]: (k9_subset_1('#skF_1', B_251, '#skF_4')=k3_xboole_0(B_251, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_220])).
% 8.25/2.79  tff(c_50, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 8.25/2.79  tff(c_115, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 8.25/2.79  tff(c_257, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_232, c_115])).
% 8.25/2.79  tff(c_789, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_785, c_257])).
% 8.25/2.79  tff(c_961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_879, c_218, c_879, c_788, c_789])).
% 8.25/2.79  tff(c_962, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 8.25/2.79  tff(c_1100, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_962])).
% 8.25/2.79  tff(c_3340, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3329, c_1100])).
% 8.25/2.79  tff(c_3354, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1050, c_1051, c_2080, c_1823, c_2080, c_1823, c_2285, c_3340])).
% 8.25/2.79  tff(c_3356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3354])).
% 8.25/2.79  tff(c_3357, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_962])).
% 8.25/2.79  tff(c_5951, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5942, c_3357])).
% 8.25/2.79  tff(c_5962, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1050, c_1051, c_4375, c_3894, c_4375, c_3894, c_4629, c_5951])).
% 8.25/2.79  tff(c_5964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5962])).
% 8.25/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.25/2.79  
% 8.25/2.79  Inference rules
% 8.25/2.79  ----------------------
% 8.25/2.79  #Ref     : 0
% 8.25/2.79  #Sup     : 1190
% 8.25/2.79  #Fact    : 0
% 8.25/2.79  #Define  : 0
% 8.25/2.79  #Split   : 38
% 8.25/2.79  #Chain   : 0
% 8.25/2.79  #Close   : 0
% 8.25/2.79  
% 8.25/2.79  Ordering : KBO
% 8.25/2.79  
% 8.25/2.79  Simplification rules
% 8.25/2.79  ----------------------
% 8.25/2.79  #Subsume      : 119
% 8.25/2.79  #Demod        : 862
% 8.25/2.79  #Tautology    : 611
% 8.25/2.80  #SimpNegUnit  : 258
% 8.25/2.80  #BackRed      : 14
% 8.25/2.80  
% 8.25/2.80  #Partial instantiations: 0
% 8.25/2.80  #Strategies tried      : 1
% 8.25/2.80  
% 8.25/2.80  Timing (in seconds)
% 8.25/2.80  ----------------------
% 8.25/2.80  Preprocessing        : 0.42
% 8.25/2.80  Parsing              : 0.20
% 8.25/2.80  CNF conversion       : 0.06
% 8.25/2.80  Main loop            : 1.57
% 8.25/2.80  Inferencing          : 0.58
% 8.25/2.80  Reduction            : 0.50
% 8.25/2.80  Demodulation         : 0.36
% 8.25/2.80  BG Simplification    : 0.05
% 8.25/2.80  Subsumption          : 0.33
% 8.25/2.80  Abstraction          : 0.07
% 8.25/2.80  MUC search           : 0.00
% 8.25/2.80  Cooper               : 0.00
% 8.25/2.80  Total                : 2.05
% 8.25/2.80  Index Insertion      : 0.00
% 8.25/2.80  Index Deletion       : 0.00
% 8.25/2.80  Index Matching       : 0.00
% 8.25/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
