%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:18 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  171 (1698 expanded)
%              Number of leaves         :   42 ( 590 expanded)
%              Depth                    :   19
%              Number of atoms          :  611 (7669 expanded)
%              Number of equality atoms :  115 (1616 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_213,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

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

tff(f_171,axiom,(
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

tff(f_137,axiom,(
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

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_1179,plain,(
    ! [A_364,B_365,C_366,D_367] :
      ( k2_partfun1(A_364,B_365,C_366,D_367) = k7_relat_1(C_366,D_367)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365)))
      | ~ v1_funct_1(C_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1183,plain,(
    ! [D_367] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_367) = k7_relat_1('#skF_5',D_367)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_1179])).

tff(c_1189,plain,(
    ! [D_367] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_367) = k7_relat_1('#skF_5',D_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1183])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_1181,plain,(
    ! [D_367] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_367) = k7_relat_1('#skF_6',D_367)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_1179])).

tff(c_1186,plain,(
    ! [D_367] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_367) = k7_relat_1('#skF_6',D_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1181])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_60,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | ~ r1_subset_1(A_9,B_10)
      | v1_xboole_0(B_10)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,(
    ! [C_222,A_223,B_224] :
      ( v1_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_312,plain,(
    ! [C_264,A_265,B_266] :
      ( v4_relat_1(C_264,A_265)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_320,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_312])).

tff(c_418,plain,(
    ! [B_286,A_287] :
      ( k1_relat_1(B_286) = A_287
      | ~ v1_partfun1(B_286,A_287)
      | ~ v4_relat_1(B_286,A_287)
      | ~ v1_relat_1(B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_421,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_320,c_418])).

tff(c_427,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_421])).

tff(c_431,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_789,plain,(
    ! [C_331,A_332,B_333] :
      ( v1_partfun1(C_331,A_332)
      | ~ v1_funct_2(C_331,A_332,B_333)
      | ~ v1_funct_1(C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_332,B_333)))
      | v1_xboole_0(B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_795,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_789])).

tff(c_802,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_795])).

tff(c_804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_431,c_802])).

tff(c_805,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_813,plain,(
    ! [A_7] :
      ( k7_relat_1('#skF_5',A_7) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_10])).

tff(c_1088,plain,(
    ! [A_354] :
      ( k7_relat_1('#skF_5',A_354) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',A_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_813])).

tff(c_1095,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_5',B_10) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_10)
      | v1_xboole_0(B_10)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_1088])).

tff(c_1168,plain,(
    ! [B_363] :
      ( k7_relat_1('#skF_5',B_363) = k1_xboole_0
      | ~ r1_subset_1('#skF_3',B_363)
      | v1_xboole_0(B_363) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1095])).

tff(c_1174,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1168])).

tff(c_1178,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1174])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(k1_relat_1(B_8),A_7)
      | k7_relat_1(B_8,A_7) != k1_xboole_0
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_816,plain,(
    ! [A_7] :
      ( r1_xboole_0('#skF_3',A_7)
      | k7_relat_1('#skF_5',A_7) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_12])).

tff(c_1077,plain,(
    ! [A_353] :
      ( r1_xboole_0('#skF_3',A_353)
      | k7_relat_1('#skF_5',A_353) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_816])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1087,plain,(
    ! [A_353] :
      ( k3_xboole_0('#skF_3',A_353) = k1_xboole_0
      | k7_relat_1('#skF_5',A_353) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1077,c_2])).

tff(c_1202,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_1087])).

tff(c_369,plain,(
    ! [A_279,B_280,C_281] :
      ( k9_subset_1(A_279,B_280,C_281) = k3_xboole_0(B_280,C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(A_279)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_381,plain,(
    ! [B_280] : k9_subset_1('#skF_1',B_280,'#skF_4') = k3_xboole_0(B_280,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_369])).

tff(c_93,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_86])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    ! [B_238,A_239] :
      ( k7_relat_1(B_238,A_239) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_238),A_239)
      | ~ v1_relat_1(B_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_218,plain,(
    ! [B_249,B_250] :
      ( k7_relat_1(B_249,B_250) = k1_xboole_0
      | ~ v1_relat_1(B_249)
      | k3_xboole_0(k1_relat_1(B_249),B_250) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_224,plain,(
    ! [B_251] :
      ( k7_relat_1(B_251,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_218])).

tff(c_232,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_224])).

tff(c_231,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_224])).

tff(c_115,plain,(
    ! [A_232,B_233] :
      ( r1_xboole_0(A_232,B_233)
      | ~ r1_subset_1(A_232,B_233)
      | v1_xboole_0(B_233)
      | v1_xboole_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_295,plain,(
    ! [A_262,B_263] :
      ( k3_xboole_0(A_262,B_263) = k1_xboole_0
      | ~ r1_subset_1(A_262,B_263)
      | v1_xboole_0(B_263)
      | v1_xboole_0(A_262) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_301,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_295])).

tff(c_305,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64,c_301])).

tff(c_237,plain,(
    ! [A_252,B_253,C_254,D_255] :
      ( k2_partfun1(A_252,B_253,C_254,D_255) = k7_relat_1(C_254,D_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ v1_funct_1(C_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_239,plain,(
    ! [D_255] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_255) = k7_relat_1('#skF_6',D_255)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_237])).

tff(c_244,plain,(
    ! [D_255] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_255) = k7_relat_1('#skF_6',D_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_239])).

tff(c_241,plain,(
    ! [D_255] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_255) = k7_relat_1('#skF_5',D_255)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_237])).

tff(c_247,plain,(
    ! [D_255] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_255) = k7_relat_1('#skF_5',D_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_241])).

tff(c_153,plain,(
    ! [A_240,B_241,C_242] :
      ( k9_subset_1(A_240,B_241,C_242) = k3_xboole_0(B_241,C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(A_240)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [B_241] : k9_subset_1('#skF_1',B_241,'#skF_4') = k3_xboole_0(B_241,'#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_153])).

tff(c_46,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_95,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_175,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_165,c_95])).

tff(c_270,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_247,c_175])).

tff(c_306,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_305,c_270])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_231,c_306])).

tff(c_311,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1105,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_381,c_311])).

tff(c_1206,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_1202,c_1105])).

tff(c_1234,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_1186,c_1206])).

tff(c_1104,plain,(
    ! [B_2] :
      ( k7_relat_1('#skF_5',B_2) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1088])).

tff(c_1241,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1234,c_1104])).

tff(c_1249,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1241])).

tff(c_1253,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1234])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_2789,plain,(
    ! [C_661,D_658,B_659,A_662,F_657,E_660] :
      ( v1_funct_1(k1_tmap_1(A_662,B_659,C_661,D_658,E_660,F_657))
      | ~ m1_subset_1(F_657,k1_zfmisc_1(k2_zfmisc_1(D_658,B_659)))
      | ~ v1_funct_2(F_657,D_658,B_659)
      | ~ v1_funct_1(F_657)
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(C_661,B_659)))
      | ~ v1_funct_2(E_660,C_661,B_659)
      | ~ v1_funct_1(E_660)
      | ~ m1_subset_1(D_658,k1_zfmisc_1(A_662))
      | v1_xboole_0(D_658)
      | ~ m1_subset_1(C_661,k1_zfmisc_1(A_662))
      | v1_xboole_0(C_661)
      | v1_xboole_0(B_659)
      | v1_xboole_0(A_662) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2791,plain,(
    ! [A_662,C_661,E_660] :
      ( v1_funct_1(k1_tmap_1(A_662,'#skF_2',C_661,'#skF_4',E_660,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(C_661,'#skF_2')))
      | ~ v1_funct_2(E_660,C_661,'#skF_2')
      | ~ v1_funct_1(E_660)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_662))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_661,k1_zfmisc_1(A_662))
      | v1_xboole_0(C_661)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_662) ) ),
    inference(resolution,[status(thm)],[c_48,c_2789])).

tff(c_2796,plain,(
    ! [A_662,C_661,E_660] :
      ( v1_funct_1(k1_tmap_1(A_662,'#skF_2',C_661,'#skF_4',E_660,'#skF_6'))
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(C_661,'#skF_2')))
      | ~ v1_funct_2(E_660,C_661,'#skF_2')
      | ~ v1_funct_1(E_660)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_662))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_661,k1_zfmisc_1(A_662))
      | v1_xboole_0(C_661)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2791])).

tff(c_2802,plain,(
    ! [A_663,C_664,E_665] :
      ( v1_funct_1(k1_tmap_1(A_663,'#skF_2',C_664,'#skF_4',E_665,'#skF_6'))
      | ~ m1_subset_1(E_665,k1_zfmisc_1(k2_zfmisc_1(C_664,'#skF_2')))
      | ~ v1_funct_2(E_665,C_664,'#skF_2')
      | ~ v1_funct_1(E_665)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_663))
      | ~ m1_subset_1(C_664,k1_zfmisc_1(A_663))
      | v1_xboole_0(C_664)
      | v1_xboole_0(A_663) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_2796])).

tff(c_2806,plain,(
    ! [A_663] :
      ( v1_funct_1(k1_tmap_1(A_663,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_663))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_663))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_663) ) ),
    inference(resolution,[status(thm)],[c_54,c_2802])).

tff(c_2813,plain,(
    ! [A_663] :
      ( v1_funct_1(k1_tmap_1(A_663,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_663))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_663))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_663) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2806])).

tff(c_2823,plain,(
    ! [A_673] :
      ( v1_funct_1(k1_tmap_1(A_673,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_673))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_673))
      | v1_xboole_0(A_673) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2813])).

tff(c_2826,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2823])).

tff(c_2829,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2826])).

tff(c_2830,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2829])).

tff(c_42,plain,(
    ! [B_155,D_157,A_154,F_159,C_156,E_158] :
      ( v1_funct_2(k1_tmap_1(A_154,B_155,C_156,D_157,E_158,F_159),k4_subset_1(A_154,C_156,D_157),B_155)
      | ~ m1_subset_1(F_159,k1_zfmisc_1(k2_zfmisc_1(D_157,B_155)))
      | ~ v1_funct_2(F_159,D_157,B_155)
      | ~ v1_funct_1(F_159)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(C_156,B_155)))
      | ~ v1_funct_2(E_158,C_156,B_155)
      | ~ v1_funct_1(E_158)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(A_154))
      | v1_xboole_0(D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(A_154))
      | v1_xboole_0(C_156)
      | v1_xboole_0(B_155)
      | v1_xboole_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_40,plain,(
    ! [B_155,D_157,A_154,F_159,C_156,E_158] :
      ( m1_subset_1(k1_tmap_1(A_154,B_155,C_156,D_157,E_158,F_159),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_154,C_156,D_157),B_155)))
      | ~ m1_subset_1(F_159,k1_zfmisc_1(k2_zfmisc_1(D_157,B_155)))
      | ~ v1_funct_2(F_159,D_157,B_155)
      | ~ v1_funct_1(F_159)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(C_156,B_155)))
      | ~ v1_funct_2(E_158,C_156,B_155)
      | ~ v1_funct_1(E_158)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(A_154))
      | v1_xboole_0(D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(A_154))
      | v1_xboole_0(C_156)
      | v1_xboole_0(B_155)
      | v1_xboole_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_3053,plain,(
    ! [C_720,D_719,B_717,E_722,A_721,F_718] :
      ( k2_partfun1(k4_subset_1(A_721,C_720,D_719),B_717,k1_tmap_1(A_721,B_717,C_720,D_719,E_722,F_718),C_720) = E_722
      | ~ m1_subset_1(k1_tmap_1(A_721,B_717,C_720,D_719,E_722,F_718),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_721,C_720,D_719),B_717)))
      | ~ v1_funct_2(k1_tmap_1(A_721,B_717,C_720,D_719,E_722,F_718),k4_subset_1(A_721,C_720,D_719),B_717)
      | ~ v1_funct_1(k1_tmap_1(A_721,B_717,C_720,D_719,E_722,F_718))
      | k2_partfun1(D_719,B_717,F_718,k9_subset_1(A_721,C_720,D_719)) != k2_partfun1(C_720,B_717,E_722,k9_subset_1(A_721,C_720,D_719))
      | ~ m1_subset_1(F_718,k1_zfmisc_1(k2_zfmisc_1(D_719,B_717)))
      | ~ v1_funct_2(F_718,D_719,B_717)
      | ~ v1_funct_1(F_718)
      | ~ m1_subset_1(E_722,k1_zfmisc_1(k2_zfmisc_1(C_720,B_717)))
      | ~ v1_funct_2(E_722,C_720,B_717)
      | ~ v1_funct_1(E_722)
      | ~ m1_subset_1(D_719,k1_zfmisc_1(A_721))
      | v1_xboole_0(D_719)
      | ~ m1_subset_1(C_720,k1_zfmisc_1(A_721))
      | v1_xboole_0(C_720)
      | v1_xboole_0(B_717)
      | v1_xboole_0(A_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3463,plain,(
    ! [C_807,A_808,B_805,F_803,D_804,E_806] :
      ( k2_partfun1(k4_subset_1(A_808,C_807,D_804),B_805,k1_tmap_1(A_808,B_805,C_807,D_804,E_806,F_803),C_807) = E_806
      | ~ v1_funct_2(k1_tmap_1(A_808,B_805,C_807,D_804,E_806,F_803),k4_subset_1(A_808,C_807,D_804),B_805)
      | ~ v1_funct_1(k1_tmap_1(A_808,B_805,C_807,D_804,E_806,F_803))
      | k2_partfun1(D_804,B_805,F_803,k9_subset_1(A_808,C_807,D_804)) != k2_partfun1(C_807,B_805,E_806,k9_subset_1(A_808,C_807,D_804))
      | ~ m1_subset_1(F_803,k1_zfmisc_1(k2_zfmisc_1(D_804,B_805)))
      | ~ v1_funct_2(F_803,D_804,B_805)
      | ~ v1_funct_1(F_803)
      | ~ m1_subset_1(E_806,k1_zfmisc_1(k2_zfmisc_1(C_807,B_805)))
      | ~ v1_funct_2(E_806,C_807,B_805)
      | ~ v1_funct_1(E_806)
      | ~ m1_subset_1(D_804,k1_zfmisc_1(A_808))
      | v1_xboole_0(D_804)
      | ~ m1_subset_1(C_807,k1_zfmisc_1(A_808))
      | v1_xboole_0(C_807)
      | v1_xboole_0(B_805)
      | v1_xboole_0(A_808) ) ),
    inference(resolution,[status(thm)],[c_40,c_3053])).

tff(c_3705,plain,(
    ! [C_856,E_855,A_857,D_853,B_854,F_852] :
      ( k2_partfun1(k4_subset_1(A_857,C_856,D_853),B_854,k1_tmap_1(A_857,B_854,C_856,D_853,E_855,F_852),C_856) = E_855
      | ~ v1_funct_1(k1_tmap_1(A_857,B_854,C_856,D_853,E_855,F_852))
      | k2_partfun1(D_853,B_854,F_852,k9_subset_1(A_857,C_856,D_853)) != k2_partfun1(C_856,B_854,E_855,k9_subset_1(A_857,C_856,D_853))
      | ~ m1_subset_1(F_852,k1_zfmisc_1(k2_zfmisc_1(D_853,B_854)))
      | ~ v1_funct_2(F_852,D_853,B_854)
      | ~ v1_funct_1(F_852)
      | ~ m1_subset_1(E_855,k1_zfmisc_1(k2_zfmisc_1(C_856,B_854)))
      | ~ v1_funct_2(E_855,C_856,B_854)
      | ~ v1_funct_1(E_855)
      | ~ m1_subset_1(D_853,k1_zfmisc_1(A_857))
      | v1_xboole_0(D_853)
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_857))
      | v1_xboole_0(C_856)
      | v1_xboole_0(B_854)
      | v1_xboole_0(A_857) ) ),
    inference(resolution,[status(thm)],[c_42,c_3463])).

tff(c_3709,plain,(
    ! [A_857,C_856,E_855] :
      ( k2_partfun1(k4_subset_1(A_857,C_856,'#skF_4'),'#skF_2',k1_tmap_1(A_857,'#skF_2',C_856,'#skF_4',E_855,'#skF_6'),C_856) = E_855
      | ~ v1_funct_1(k1_tmap_1(A_857,'#skF_2',C_856,'#skF_4',E_855,'#skF_6'))
      | k2_partfun1(C_856,'#skF_2',E_855,k9_subset_1(A_857,C_856,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_857,C_856,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_855,k1_zfmisc_1(k2_zfmisc_1(C_856,'#skF_2')))
      | ~ v1_funct_2(E_855,C_856,'#skF_2')
      | ~ v1_funct_1(E_855)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_857))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_857))
      | v1_xboole_0(C_856)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_857) ) ),
    inference(resolution,[status(thm)],[c_48,c_3705])).

tff(c_3715,plain,(
    ! [A_857,C_856,E_855] :
      ( k2_partfun1(k4_subset_1(A_857,C_856,'#skF_4'),'#skF_2',k1_tmap_1(A_857,'#skF_2',C_856,'#skF_4',E_855,'#skF_6'),C_856) = E_855
      | ~ v1_funct_1(k1_tmap_1(A_857,'#skF_2',C_856,'#skF_4',E_855,'#skF_6'))
      | k2_partfun1(C_856,'#skF_2',E_855,k9_subset_1(A_857,C_856,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_857,C_856,'#skF_4'))
      | ~ m1_subset_1(E_855,k1_zfmisc_1(k2_zfmisc_1(C_856,'#skF_2')))
      | ~ v1_funct_2(E_855,C_856,'#skF_2')
      | ~ v1_funct_1(E_855)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_857))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_856,k1_zfmisc_1(A_857))
      | v1_xboole_0(C_856)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1186,c_3709])).

tff(c_4056,plain,(
    ! [A_918,C_919,E_920] :
      ( k2_partfun1(k4_subset_1(A_918,C_919,'#skF_4'),'#skF_2',k1_tmap_1(A_918,'#skF_2',C_919,'#skF_4',E_920,'#skF_6'),C_919) = E_920
      | ~ v1_funct_1(k1_tmap_1(A_918,'#skF_2',C_919,'#skF_4',E_920,'#skF_6'))
      | k2_partfun1(C_919,'#skF_2',E_920,k9_subset_1(A_918,C_919,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_918,C_919,'#skF_4'))
      | ~ m1_subset_1(E_920,k1_zfmisc_1(k2_zfmisc_1(C_919,'#skF_2')))
      | ~ v1_funct_2(E_920,C_919,'#skF_2')
      | ~ v1_funct_1(E_920)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_918))
      | ~ m1_subset_1(C_919,k1_zfmisc_1(A_918))
      | v1_xboole_0(C_919)
      | v1_xboole_0(A_918) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_3715])).

tff(c_4063,plain,(
    ! [A_918] :
      ( k2_partfun1(k4_subset_1(A_918,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_918,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_918,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_918,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_918,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_918))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_918))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_918) ) ),
    inference(resolution,[status(thm)],[c_54,c_4056])).

tff(c_4073,plain,(
    ! [A_918] :
      ( k2_partfun1(k4_subset_1(A_918,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_918,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_918,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_918,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_918,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_918))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_918))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_918) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1189,c_4063])).

tff(c_4075,plain,(
    ! [A_921] :
      ( k2_partfun1(k4_subset_1(A_921,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_921,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_921,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_921,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_921,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_921))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_921))
      | v1_xboole_0(A_921) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4073])).

tff(c_1446,plain,(
    ! [C_391,D_388,F_387,E_390,B_389,A_392] :
      ( v1_funct_1(k1_tmap_1(A_392,B_389,C_391,D_388,E_390,F_387))
      | ~ m1_subset_1(F_387,k1_zfmisc_1(k2_zfmisc_1(D_388,B_389)))
      | ~ v1_funct_2(F_387,D_388,B_389)
      | ~ v1_funct_1(F_387)
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(C_391,B_389)))
      | ~ v1_funct_2(E_390,C_391,B_389)
      | ~ v1_funct_1(E_390)
      | ~ m1_subset_1(D_388,k1_zfmisc_1(A_392))
      | v1_xboole_0(D_388)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(A_392))
      | v1_xboole_0(C_391)
      | v1_xboole_0(B_389)
      | v1_xboole_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1448,plain,(
    ! [A_392,C_391,E_390] :
      ( v1_funct_1(k1_tmap_1(A_392,'#skF_2',C_391,'#skF_4',E_390,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(C_391,'#skF_2')))
      | ~ v1_funct_2(E_390,C_391,'#skF_2')
      | ~ v1_funct_1(E_390)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_392))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_391,k1_zfmisc_1(A_392))
      | v1_xboole_0(C_391)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_392) ) ),
    inference(resolution,[status(thm)],[c_48,c_1446])).

tff(c_1453,plain,(
    ! [A_392,C_391,E_390] :
      ( v1_funct_1(k1_tmap_1(A_392,'#skF_2',C_391,'#skF_4',E_390,'#skF_6'))
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(C_391,'#skF_2')))
      | ~ v1_funct_2(E_390,C_391,'#skF_2')
      | ~ v1_funct_1(E_390)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_392))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_391,k1_zfmisc_1(A_392))
      | v1_xboole_0(C_391)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1448])).

tff(c_1459,plain,(
    ! [A_393,C_394,E_395] :
      ( v1_funct_1(k1_tmap_1(A_393,'#skF_2',C_394,'#skF_4',E_395,'#skF_6'))
      | ~ m1_subset_1(E_395,k1_zfmisc_1(k2_zfmisc_1(C_394,'#skF_2')))
      | ~ v1_funct_2(E_395,C_394,'#skF_2')
      | ~ v1_funct_1(E_395)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_393))
      | ~ m1_subset_1(C_394,k1_zfmisc_1(A_393))
      | v1_xboole_0(C_394)
      | v1_xboole_0(A_393) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1453])).

tff(c_1463,plain,(
    ! [A_393] :
      ( v1_funct_1(k1_tmap_1(A_393,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_393))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_393))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_393) ) ),
    inference(resolution,[status(thm)],[c_54,c_1459])).

tff(c_1470,plain,(
    ! [A_393] :
      ( v1_funct_1(k1_tmap_1(A_393,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_393))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_393))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1463])).

tff(c_1479,plain,(
    ! [A_397] :
      ( v1_funct_1(k1_tmap_1(A_397,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_397))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_397))
      | v1_xboole_0(A_397) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1470])).

tff(c_1482,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1479])).

tff(c_1485,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1482])).

tff(c_1486,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1485])).

tff(c_1616,plain,(
    ! [F_427,E_431,A_430,C_429,D_428,B_426] :
      ( k2_partfun1(k4_subset_1(A_430,C_429,D_428),B_426,k1_tmap_1(A_430,B_426,C_429,D_428,E_431,F_427),D_428) = F_427
      | ~ m1_subset_1(k1_tmap_1(A_430,B_426,C_429,D_428,E_431,F_427),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_430,C_429,D_428),B_426)))
      | ~ v1_funct_2(k1_tmap_1(A_430,B_426,C_429,D_428,E_431,F_427),k4_subset_1(A_430,C_429,D_428),B_426)
      | ~ v1_funct_1(k1_tmap_1(A_430,B_426,C_429,D_428,E_431,F_427))
      | k2_partfun1(D_428,B_426,F_427,k9_subset_1(A_430,C_429,D_428)) != k2_partfun1(C_429,B_426,E_431,k9_subset_1(A_430,C_429,D_428))
      | ~ m1_subset_1(F_427,k1_zfmisc_1(k2_zfmisc_1(D_428,B_426)))
      | ~ v1_funct_2(F_427,D_428,B_426)
      | ~ v1_funct_1(F_427)
      | ~ m1_subset_1(E_431,k1_zfmisc_1(k2_zfmisc_1(C_429,B_426)))
      | ~ v1_funct_2(E_431,C_429,B_426)
      | ~ v1_funct_1(E_431)
      | ~ m1_subset_1(D_428,k1_zfmisc_1(A_430))
      | v1_xboole_0(D_428)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(A_430))
      | v1_xboole_0(C_429)
      | v1_xboole_0(B_426)
      | v1_xboole_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1873,plain,(
    ! [A_517,B_514,D_513,E_515,F_512,C_516] :
      ( k2_partfun1(k4_subset_1(A_517,C_516,D_513),B_514,k1_tmap_1(A_517,B_514,C_516,D_513,E_515,F_512),D_513) = F_512
      | ~ v1_funct_2(k1_tmap_1(A_517,B_514,C_516,D_513,E_515,F_512),k4_subset_1(A_517,C_516,D_513),B_514)
      | ~ v1_funct_1(k1_tmap_1(A_517,B_514,C_516,D_513,E_515,F_512))
      | k2_partfun1(D_513,B_514,F_512,k9_subset_1(A_517,C_516,D_513)) != k2_partfun1(C_516,B_514,E_515,k9_subset_1(A_517,C_516,D_513))
      | ~ m1_subset_1(F_512,k1_zfmisc_1(k2_zfmisc_1(D_513,B_514)))
      | ~ v1_funct_2(F_512,D_513,B_514)
      | ~ v1_funct_1(F_512)
      | ~ m1_subset_1(E_515,k1_zfmisc_1(k2_zfmisc_1(C_516,B_514)))
      | ~ v1_funct_2(E_515,C_516,B_514)
      | ~ v1_funct_1(E_515)
      | ~ m1_subset_1(D_513,k1_zfmisc_1(A_517))
      | v1_xboole_0(D_513)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(A_517))
      | v1_xboole_0(C_516)
      | v1_xboole_0(B_514)
      | v1_xboole_0(A_517) ) ),
    inference(resolution,[status(thm)],[c_40,c_1616])).

tff(c_2330,plain,(
    ! [F_582,D_583,B_584,C_586,E_585,A_587] :
      ( k2_partfun1(k4_subset_1(A_587,C_586,D_583),B_584,k1_tmap_1(A_587,B_584,C_586,D_583,E_585,F_582),D_583) = F_582
      | ~ v1_funct_1(k1_tmap_1(A_587,B_584,C_586,D_583,E_585,F_582))
      | k2_partfun1(D_583,B_584,F_582,k9_subset_1(A_587,C_586,D_583)) != k2_partfun1(C_586,B_584,E_585,k9_subset_1(A_587,C_586,D_583))
      | ~ m1_subset_1(F_582,k1_zfmisc_1(k2_zfmisc_1(D_583,B_584)))
      | ~ v1_funct_2(F_582,D_583,B_584)
      | ~ v1_funct_1(F_582)
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(C_586,B_584)))
      | ~ v1_funct_2(E_585,C_586,B_584)
      | ~ v1_funct_1(E_585)
      | ~ m1_subset_1(D_583,k1_zfmisc_1(A_587))
      | v1_xboole_0(D_583)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(A_587))
      | v1_xboole_0(C_586)
      | v1_xboole_0(B_584)
      | v1_xboole_0(A_587) ) ),
    inference(resolution,[status(thm)],[c_42,c_1873])).

tff(c_2334,plain,(
    ! [A_587,C_586,E_585] :
      ( k2_partfun1(k4_subset_1(A_587,C_586,'#skF_4'),'#skF_2',k1_tmap_1(A_587,'#skF_2',C_586,'#skF_4',E_585,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_587,'#skF_2',C_586,'#skF_4',E_585,'#skF_6'))
      | k2_partfun1(C_586,'#skF_2',E_585,k9_subset_1(A_587,C_586,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_587,C_586,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(C_586,'#skF_2')))
      | ~ v1_funct_2(E_585,C_586,'#skF_2')
      | ~ v1_funct_1(E_585)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_587))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_586,k1_zfmisc_1(A_587))
      | v1_xboole_0(C_586)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_587) ) ),
    inference(resolution,[status(thm)],[c_48,c_2330])).

tff(c_2340,plain,(
    ! [A_587,C_586,E_585] :
      ( k2_partfun1(k4_subset_1(A_587,C_586,'#skF_4'),'#skF_2',k1_tmap_1(A_587,'#skF_2',C_586,'#skF_4',E_585,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_587,'#skF_2',C_586,'#skF_4',E_585,'#skF_6'))
      | k2_partfun1(C_586,'#skF_2',E_585,k9_subset_1(A_587,C_586,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_587,C_586,'#skF_4'))
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(C_586,'#skF_2')))
      | ~ v1_funct_2(E_585,C_586,'#skF_2')
      | ~ v1_funct_1(E_585)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_587))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_586,k1_zfmisc_1(A_587))
      | v1_xboole_0(C_586)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_587) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1186,c_2334])).

tff(c_2643,plain,(
    ! [A_645,C_646,E_647] :
      ( k2_partfun1(k4_subset_1(A_645,C_646,'#skF_4'),'#skF_2',k1_tmap_1(A_645,'#skF_2',C_646,'#skF_4',E_647,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_645,'#skF_2',C_646,'#skF_4',E_647,'#skF_6'))
      | k2_partfun1(C_646,'#skF_2',E_647,k9_subset_1(A_645,C_646,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_645,C_646,'#skF_4'))
      | ~ m1_subset_1(E_647,k1_zfmisc_1(k2_zfmisc_1(C_646,'#skF_2')))
      | ~ v1_funct_2(E_647,C_646,'#skF_2')
      | ~ v1_funct_1(E_647)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_645))
      | ~ m1_subset_1(C_646,k1_zfmisc_1(A_645))
      | v1_xboole_0(C_646)
      | v1_xboole_0(A_645) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_2340])).

tff(c_2650,plain,(
    ! [A_645] :
      ( k2_partfun1(k4_subset_1(A_645,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_645,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_645,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_645,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_645,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_645))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_645))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_645) ) ),
    inference(resolution,[status(thm)],[c_54,c_2643])).

tff(c_2660,plain,(
    ! [A_645] :
      ( k2_partfun1(k4_subset_1(A_645,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_645,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_645,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_645,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_645,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_645))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_645))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_645) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1189,c_2650])).

tff(c_2662,plain,(
    ! [A_648] :
      ( k2_partfun1(k4_subset_1(A_648,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_648,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_648,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_648,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_648,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_648))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_648))
      | v1_xboole_0(A_648) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2660])).

tff(c_310,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1352,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_2673,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2662,c_1352])).

tff(c_2687,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1249,c_1202,c_381,c_1253,c_1202,c_381,c_1486,c_2673])).

tff(c_2689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2687])).

tff(c_2690,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_4084,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4075,c_2690])).

tff(c_4095,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1249,c_1202,c_381,c_1253,c_1202,c_381,c_2830,c_4084])).

tff(c_4097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:22:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.80/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.69  
% 7.80/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/2.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.80/2.69  
% 7.80/2.69  %Foreground sorts:
% 7.80/2.69  
% 7.80/2.69  
% 7.80/2.69  %Background operators:
% 7.80/2.69  
% 7.80/2.69  
% 7.80/2.69  %Foreground operators:
% 7.80/2.69  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 7.80/2.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.80/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.80/2.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.80/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.80/2.69  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.80/2.69  tff('#skF_5', type, '#skF_5': $i).
% 7.80/2.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.80/2.69  tff('#skF_6', type, '#skF_6': $i).
% 7.80/2.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.80/2.69  tff('#skF_2', type, '#skF_2': $i).
% 7.80/2.69  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.80/2.69  tff('#skF_3', type, '#skF_3': $i).
% 7.80/2.69  tff('#skF_1', type, '#skF_1': $i).
% 7.80/2.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.80/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.80/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.80/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.80/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.80/2.69  tff('#skF_4', type, '#skF_4': $i).
% 7.80/2.69  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.80/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.80/2.69  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.80/2.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.80/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.80/2.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.80/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.80/2.69  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.80/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.80/2.69  
% 7.98/2.72  tff(f_213, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 7.98/2.72  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.98/2.72  tff(f_89, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.98/2.72  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 7.98/2.72  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.98/2.72  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.98/2.72  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 7.98/2.72  tff(f_75, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.98/2.72  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 7.98/2.72  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.98/2.72  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.98/2.72  tff(f_171, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 7.98/2.72  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 7.98/2.72  tff(c_72, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.98/2.72  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_1179, plain, (![A_364, B_365, C_366, D_367]: (k2_partfun1(A_364, B_365, C_366, D_367)=k7_relat_1(C_366, D_367) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))) | ~v1_funct_1(C_366))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.98/2.72  tff(c_1183, plain, (![D_367]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_367)=k7_relat_1('#skF_5', D_367) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_1179])).
% 7.98/2.72  tff(c_1189, plain, (![D_367]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_367)=k7_relat_1('#skF_5', D_367))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1183])).
% 7.98/2.72  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_1181, plain, (![D_367]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_367)=k7_relat_1('#skF_6', D_367) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_1179])).
% 7.98/2.72  tff(c_1186, plain, (![D_367]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_367)=k7_relat_1('#skF_6', D_367))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1181])).
% 7.98/2.72  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_60, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_16, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | ~r1_subset_1(A_9, B_10) | v1_xboole_0(B_10) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.98/2.72  tff(c_86, plain, (![C_222, A_223, B_224]: (v1_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.98/2.72  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_86])).
% 7.98/2.72  tff(c_70, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_312, plain, (![C_264, A_265, B_266]: (v4_relat_1(C_264, A_265) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.98/2.72  tff(c_320, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_312])).
% 7.98/2.72  tff(c_418, plain, (![B_286, A_287]: (k1_relat_1(B_286)=A_287 | ~v1_partfun1(B_286, A_287) | ~v4_relat_1(B_286, A_287) | ~v1_relat_1(B_286))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.98/2.72  tff(c_421, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_320, c_418])).
% 7.98/2.72  tff(c_427, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_421])).
% 7.98/2.72  tff(c_431, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_427])).
% 7.98/2.72  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_789, plain, (![C_331, A_332, B_333]: (v1_partfun1(C_331, A_332) | ~v1_funct_2(C_331, A_332, B_333) | ~v1_funct_1(C_331) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_332, B_333))) | v1_xboole_0(B_333))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.98/2.72  tff(c_795, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_789])).
% 7.98/2.72  tff(c_802, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_795])).
% 7.98/2.72  tff(c_804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_431, c_802])).
% 7.98/2.72  tff(c_805, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_427])).
% 7.98/2.72  tff(c_10, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.98/2.72  tff(c_813, plain, (![A_7]: (k7_relat_1('#skF_5', A_7)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_805, c_10])).
% 7.98/2.72  tff(c_1088, plain, (![A_354]: (k7_relat_1('#skF_5', A_354)=k1_xboole_0 | ~r1_xboole_0('#skF_3', A_354))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_813])).
% 7.98/2.72  tff(c_1095, plain, (![B_10]: (k7_relat_1('#skF_5', B_10)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_10) | v1_xboole_0(B_10) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_1088])).
% 7.98/2.72  tff(c_1168, plain, (![B_363]: (k7_relat_1('#skF_5', B_363)=k1_xboole_0 | ~r1_subset_1('#skF_3', B_363) | v1_xboole_0(B_363))), inference(negUnitSimplification, [status(thm)], [c_68, c_1095])).
% 7.98/2.72  tff(c_1174, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1168])).
% 7.98/2.72  tff(c_1178, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_1174])).
% 7.98/2.72  tff(c_12, plain, (![B_8, A_7]: (r1_xboole_0(k1_relat_1(B_8), A_7) | k7_relat_1(B_8, A_7)!=k1_xboole_0 | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.98/2.72  tff(c_816, plain, (![A_7]: (r1_xboole_0('#skF_3', A_7) | k7_relat_1('#skF_5', A_7)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_805, c_12])).
% 7.98/2.72  tff(c_1077, plain, (![A_353]: (r1_xboole_0('#skF_3', A_353) | k7_relat_1('#skF_5', A_353)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_816])).
% 7.98/2.72  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.98/2.72  tff(c_1087, plain, (![A_353]: (k3_xboole_0('#skF_3', A_353)=k1_xboole_0 | k7_relat_1('#skF_5', A_353)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1077, c_2])).
% 7.98/2.72  tff(c_1202, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1178, c_1087])).
% 7.98/2.72  tff(c_369, plain, (![A_279, B_280, C_281]: (k9_subset_1(A_279, B_280, C_281)=k3_xboole_0(B_280, C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(A_279)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.98/2.72  tff(c_381, plain, (![B_280]: (k9_subset_1('#skF_1', B_280, '#skF_4')=k3_xboole_0(B_280, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_369])).
% 7.98/2.72  tff(c_93, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_86])).
% 7.98/2.72  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.98/2.72  tff(c_138, plain, (![B_238, A_239]: (k7_relat_1(B_238, A_239)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_238), A_239) | ~v1_relat_1(B_238))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.98/2.72  tff(c_218, plain, (![B_249, B_250]: (k7_relat_1(B_249, B_250)=k1_xboole_0 | ~v1_relat_1(B_249) | k3_xboole_0(k1_relat_1(B_249), B_250)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_138])).
% 7.98/2.72  tff(c_224, plain, (![B_251]: (k7_relat_1(B_251, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_251))), inference(superposition, [status(thm), theory('equality')], [c_6, c_218])).
% 7.98/2.72  tff(c_232, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_224])).
% 7.98/2.72  tff(c_231, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_224])).
% 7.98/2.72  tff(c_115, plain, (![A_232, B_233]: (r1_xboole_0(A_232, B_233) | ~r1_subset_1(A_232, B_233) | v1_xboole_0(B_233) | v1_xboole_0(A_232))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.98/2.72  tff(c_295, plain, (![A_262, B_263]: (k3_xboole_0(A_262, B_263)=k1_xboole_0 | ~r1_subset_1(A_262, B_263) | v1_xboole_0(B_263) | v1_xboole_0(A_262))), inference(resolution, [status(thm)], [c_115, c_2])).
% 7.98/2.72  tff(c_301, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_295])).
% 7.98/2.72  tff(c_305, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_64, c_301])).
% 7.98/2.72  tff(c_237, plain, (![A_252, B_253, C_254, D_255]: (k2_partfun1(A_252, B_253, C_254, D_255)=k7_relat_1(C_254, D_255) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))) | ~v1_funct_1(C_254))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.98/2.72  tff(c_239, plain, (![D_255]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_255)=k7_relat_1('#skF_6', D_255) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_237])).
% 7.98/2.72  tff(c_244, plain, (![D_255]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_255)=k7_relat_1('#skF_6', D_255))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_239])).
% 7.98/2.72  tff(c_241, plain, (![D_255]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_255)=k7_relat_1('#skF_5', D_255) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_237])).
% 7.98/2.72  tff(c_247, plain, (![D_255]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_255)=k7_relat_1('#skF_5', D_255))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_241])).
% 7.98/2.72  tff(c_153, plain, (![A_240, B_241, C_242]: (k9_subset_1(A_240, B_241, C_242)=k3_xboole_0(B_241, C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(A_240)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.98/2.72  tff(c_165, plain, (![B_241]: (k9_subset_1('#skF_1', B_241, '#skF_4')=k3_xboole_0(B_241, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_153])).
% 7.98/2.72  tff(c_46, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_95, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 7.98/2.72  tff(c_175, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_165, c_95])).
% 7.98/2.72  tff(c_270, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_247, c_175])).
% 7.98/2.72  tff(c_306, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_305, c_305, c_270])).
% 7.98/2.72  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_231, c_306])).
% 7.98/2.72  tff(c_311, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 7.98/2.72  tff(c_1105, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_381, c_311])).
% 7.98/2.72  tff(c_1206, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_1202, c_1105])).
% 7.98/2.72  tff(c_1234, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_1186, c_1206])).
% 7.98/2.72  tff(c_1104, plain, (![B_2]: (k7_relat_1('#skF_5', B_2)=k1_xboole_0 | k3_xboole_0('#skF_3', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1088])).
% 7.98/2.72  tff(c_1241, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1234, c_1104])).
% 7.98/2.72  tff(c_1249, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1241])).
% 7.98/2.72  tff(c_1253, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1234])).
% 7.98/2.72  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 7.98/2.72  tff(c_2789, plain, (![C_661, D_658, B_659, A_662, F_657, E_660]: (v1_funct_1(k1_tmap_1(A_662, B_659, C_661, D_658, E_660, F_657)) | ~m1_subset_1(F_657, k1_zfmisc_1(k2_zfmisc_1(D_658, B_659))) | ~v1_funct_2(F_657, D_658, B_659) | ~v1_funct_1(F_657) | ~m1_subset_1(E_660, k1_zfmisc_1(k2_zfmisc_1(C_661, B_659))) | ~v1_funct_2(E_660, C_661, B_659) | ~v1_funct_1(E_660) | ~m1_subset_1(D_658, k1_zfmisc_1(A_662)) | v1_xboole_0(D_658) | ~m1_subset_1(C_661, k1_zfmisc_1(A_662)) | v1_xboole_0(C_661) | v1_xboole_0(B_659) | v1_xboole_0(A_662))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.98/2.72  tff(c_2791, plain, (![A_662, C_661, E_660]: (v1_funct_1(k1_tmap_1(A_662, '#skF_2', C_661, '#skF_4', E_660, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_660, k1_zfmisc_1(k2_zfmisc_1(C_661, '#skF_2'))) | ~v1_funct_2(E_660, C_661, '#skF_2') | ~v1_funct_1(E_660) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_662)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_661, k1_zfmisc_1(A_662)) | v1_xboole_0(C_661) | v1_xboole_0('#skF_2') | v1_xboole_0(A_662))), inference(resolution, [status(thm)], [c_48, c_2789])).
% 7.98/2.72  tff(c_2796, plain, (![A_662, C_661, E_660]: (v1_funct_1(k1_tmap_1(A_662, '#skF_2', C_661, '#skF_4', E_660, '#skF_6')) | ~m1_subset_1(E_660, k1_zfmisc_1(k2_zfmisc_1(C_661, '#skF_2'))) | ~v1_funct_2(E_660, C_661, '#skF_2') | ~v1_funct_1(E_660) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_662)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_661, k1_zfmisc_1(A_662)) | v1_xboole_0(C_661) | v1_xboole_0('#skF_2') | v1_xboole_0(A_662))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2791])).
% 7.98/2.72  tff(c_2802, plain, (![A_663, C_664, E_665]: (v1_funct_1(k1_tmap_1(A_663, '#skF_2', C_664, '#skF_4', E_665, '#skF_6')) | ~m1_subset_1(E_665, k1_zfmisc_1(k2_zfmisc_1(C_664, '#skF_2'))) | ~v1_funct_2(E_665, C_664, '#skF_2') | ~v1_funct_1(E_665) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_663)) | ~m1_subset_1(C_664, k1_zfmisc_1(A_663)) | v1_xboole_0(C_664) | v1_xboole_0(A_663))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_2796])).
% 7.98/2.72  tff(c_2806, plain, (![A_663]: (v1_funct_1(k1_tmap_1(A_663, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_663)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_663)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_663))), inference(resolution, [status(thm)], [c_54, c_2802])).
% 7.98/2.72  tff(c_2813, plain, (![A_663]: (v1_funct_1(k1_tmap_1(A_663, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_663)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_663)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_663))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2806])).
% 7.98/2.72  tff(c_2823, plain, (![A_673]: (v1_funct_1(k1_tmap_1(A_673, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_673)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_673)) | v1_xboole_0(A_673))), inference(negUnitSimplification, [status(thm)], [c_68, c_2813])).
% 7.98/2.72  tff(c_2826, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_2823])).
% 7.98/2.72  tff(c_2829, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2826])).
% 7.98/2.72  tff(c_2830, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2829])).
% 7.98/2.72  tff(c_42, plain, (![B_155, D_157, A_154, F_159, C_156, E_158]: (v1_funct_2(k1_tmap_1(A_154, B_155, C_156, D_157, E_158, F_159), k4_subset_1(A_154, C_156, D_157), B_155) | ~m1_subset_1(F_159, k1_zfmisc_1(k2_zfmisc_1(D_157, B_155))) | ~v1_funct_2(F_159, D_157, B_155) | ~v1_funct_1(F_159) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(C_156, B_155))) | ~v1_funct_2(E_158, C_156, B_155) | ~v1_funct_1(E_158) | ~m1_subset_1(D_157, k1_zfmisc_1(A_154)) | v1_xboole_0(D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(A_154)) | v1_xboole_0(C_156) | v1_xboole_0(B_155) | v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.98/2.72  tff(c_40, plain, (![B_155, D_157, A_154, F_159, C_156, E_158]: (m1_subset_1(k1_tmap_1(A_154, B_155, C_156, D_157, E_158, F_159), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_154, C_156, D_157), B_155))) | ~m1_subset_1(F_159, k1_zfmisc_1(k2_zfmisc_1(D_157, B_155))) | ~v1_funct_2(F_159, D_157, B_155) | ~v1_funct_1(F_159) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(C_156, B_155))) | ~v1_funct_2(E_158, C_156, B_155) | ~v1_funct_1(E_158) | ~m1_subset_1(D_157, k1_zfmisc_1(A_154)) | v1_xboole_0(D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(A_154)) | v1_xboole_0(C_156) | v1_xboole_0(B_155) | v1_xboole_0(A_154))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.98/2.72  tff(c_3053, plain, (![C_720, D_719, B_717, E_722, A_721, F_718]: (k2_partfun1(k4_subset_1(A_721, C_720, D_719), B_717, k1_tmap_1(A_721, B_717, C_720, D_719, E_722, F_718), C_720)=E_722 | ~m1_subset_1(k1_tmap_1(A_721, B_717, C_720, D_719, E_722, F_718), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_721, C_720, D_719), B_717))) | ~v1_funct_2(k1_tmap_1(A_721, B_717, C_720, D_719, E_722, F_718), k4_subset_1(A_721, C_720, D_719), B_717) | ~v1_funct_1(k1_tmap_1(A_721, B_717, C_720, D_719, E_722, F_718)) | k2_partfun1(D_719, B_717, F_718, k9_subset_1(A_721, C_720, D_719))!=k2_partfun1(C_720, B_717, E_722, k9_subset_1(A_721, C_720, D_719)) | ~m1_subset_1(F_718, k1_zfmisc_1(k2_zfmisc_1(D_719, B_717))) | ~v1_funct_2(F_718, D_719, B_717) | ~v1_funct_1(F_718) | ~m1_subset_1(E_722, k1_zfmisc_1(k2_zfmisc_1(C_720, B_717))) | ~v1_funct_2(E_722, C_720, B_717) | ~v1_funct_1(E_722) | ~m1_subset_1(D_719, k1_zfmisc_1(A_721)) | v1_xboole_0(D_719) | ~m1_subset_1(C_720, k1_zfmisc_1(A_721)) | v1_xboole_0(C_720) | v1_xboole_0(B_717) | v1_xboole_0(A_721))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.98/2.72  tff(c_3463, plain, (![C_807, A_808, B_805, F_803, D_804, E_806]: (k2_partfun1(k4_subset_1(A_808, C_807, D_804), B_805, k1_tmap_1(A_808, B_805, C_807, D_804, E_806, F_803), C_807)=E_806 | ~v1_funct_2(k1_tmap_1(A_808, B_805, C_807, D_804, E_806, F_803), k4_subset_1(A_808, C_807, D_804), B_805) | ~v1_funct_1(k1_tmap_1(A_808, B_805, C_807, D_804, E_806, F_803)) | k2_partfun1(D_804, B_805, F_803, k9_subset_1(A_808, C_807, D_804))!=k2_partfun1(C_807, B_805, E_806, k9_subset_1(A_808, C_807, D_804)) | ~m1_subset_1(F_803, k1_zfmisc_1(k2_zfmisc_1(D_804, B_805))) | ~v1_funct_2(F_803, D_804, B_805) | ~v1_funct_1(F_803) | ~m1_subset_1(E_806, k1_zfmisc_1(k2_zfmisc_1(C_807, B_805))) | ~v1_funct_2(E_806, C_807, B_805) | ~v1_funct_1(E_806) | ~m1_subset_1(D_804, k1_zfmisc_1(A_808)) | v1_xboole_0(D_804) | ~m1_subset_1(C_807, k1_zfmisc_1(A_808)) | v1_xboole_0(C_807) | v1_xboole_0(B_805) | v1_xboole_0(A_808))), inference(resolution, [status(thm)], [c_40, c_3053])).
% 7.98/2.72  tff(c_3705, plain, (![C_856, E_855, A_857, D_853, B_854, F_852]: (k2_partfun1(k4_subset_1(A_857, C_856, D_853), B_854, k1_tmap_1(A_857, B_854, C_856, D_853, E_855, F_852), C_856)=E_855 | ~v1_funct_1(k1_tmap_1(A_857, B_854, C_856, D_853, E_855, F_852)) | k2_partfun1(D_853, B_854, F_852, k9_subset_1(A_857, C_856, D_853))!=k2_partfun1(C_856, B_854, E_855, k9_subset_1(A_857, C_856, D_853)) | ~m1_subset_1(F_852, k1_zfmisc_1(k2_zfmisc_1(D_853, B_854))) | ~v1_funct_2(F_852, D_853, B_854) | ~v1_funct_1(F_852) | ~m1_subset_1(E_855, k1_zfmisc_1(k2_zfmisc_1(C_856, B_854))) | ~v1_funct_2(E_855, C_856, B_854) | ~v1_funct_1(E_855) | ~m1_subset_1(D_853, k1_zfmisc_1(A_857)) | v1_xboole_0(D_853) | ~m1_subset_1(C_856, k1_zfmisc_1(A_857)) | v1_xboole_0(C_856) | v1_xboole_0(B_854) | v1_xboole_0(A_857))), inference(resolution, [status(thm)], [c_42, c_3463])).
% 7.98/2.72  tff(c_3709, plain, (![A_857, C_856, E_855]: (k2_partfun1(k4_subset_1(A_857, C_856, '#skF_4'), '#skF_2', k1_tmap_1(A_857, '#skF_2', C_856, '#skF_4', E_855, '#skF_6'), C_856)=E_855 | ~v1_funct_1(k1_tmap_1(A_857, '#skF_2', C_856, '#skF_4', E_855, '#skF_6')) | k2_partfun1(C_856, '#skF_2', E_855, k9_subset_1(A_857, C_856, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_857, C_856, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_855, k1_zfmisc_1(k2_zfmisc_1(C_856, '#skF_2'))) | ~v1_funct_2(E_855, C_856, '#skF_2') | ~v1_funct_1(E_855) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_857)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_856, k1_zfmisc_1(A_857)) | v1_xboole_0(C_856) | v1_xboole_0('#skF_2') | v1_xboole_0(A_857))), inference(resolution, [status(thm)], [c_48, c_3705])).
% 7.98/2.72  tff(c_3715, plain, (![A_857, C_856, E_855]: (k2_partfun1(k4_subset_1(A_857, C_856, '#skF_4'), '#skF_2', k1_tmap_1(A_857, '#skF_2', C_856, '#skF_4', E_855, '#skF_6'), C_856)=E_855 | ~v1_funct_1(k1_tmap_1(A_857, '#skF_2', C_856, '#skF_4', E_855, '#skF_6')) | k2_partfun1(C_856, '#skF_2', E_855, k9_subset_1(A_857, C_856, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_857, C_856, '#skF_4')) | ~m1_subset_1(E_855, k1_zfmisc_1(k2_zfmisc_1(C_856, '#skF_2'))) | ~v1_funct_2(E_855, C_856, '#skF_2') | ~v1_funct_1(E_855) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_857)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_856, k1_zfmisc_1(A_857)) | v1_xboole_0(C_856) | v1_xboole_0('#skF_2') | v1_xboole_0(A_857))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1186, c_3709])).
% 7.98/2.72  tff(c_4056, plain, (![A_918, C_919, E_920]: (k2_partfun1(k4_subset_1(A_918, C_919, '#skF_4'), '#skF_2', k1_tmap_1(A_918, '#skF_2', C_919, '#skF_4', E_920, '#skF_6'), C_919)=E_920 | ~v1_funct_1(k1_tmap_1(A_918, '#skF_2', C_919, '#skF_4', E_920, '#skF_6')) | k2_partfun1(C_919, '#skF_2', E_920, k9_subset_1(A_918, C_919, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_918, C_919, '#skF_4')) | ~m1_subset_1(E_920, k1_zfmisc_1(k2_zfmisc_1(C_919, '#skF_2'))) | ~v1_funct_2(E_920, C_919, '#skF_2') | ~v1_funct_1(E_920) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_918)) | ~m1_subset_1(C_919, k1_zfmisc_1(A_918)) | v1_xboole_0(C_919) | v1_xboole_0(A_918))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_3715])).
% 7.98/2.72  tff(c_4063, plain, (![A_918]: (k2_partfun1(k4_subset_1(A_918, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_918, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_918, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_918, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_918, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_918)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_918)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_918))), inference(resolution, [status(thm)], [c_54, c_4056])).
% 7.98/2.72  tff(c_4073, plain, (![A_918]: (k2_partfun1(k4_subset_1(A_918, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_918, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_918, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_918, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_918, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_918)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_918)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_918))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1189, c_4063])).
% 7.98/2.72  tff(c_4075, plain, (![A_921]: (k2_partfun1(k4_subset_1(A_921, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_921, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_921, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_921, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_921, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_921)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_921)) | v1_xboole_0(A_921))), inference(negUnitSimplification, [status(thm)], [c_68, c_4073])).
% 7.98/2.72  tff(c_1446, plain, (![C_391, D_388, F_387, E_390, B_389, A_392]: (v1_funct_1(k1_tmap_1(A_392, B_389, C_391, D_388, E_390, F_387)) | ~m1_subset_1(F_387, k1_zfmisc_1(k2_zfmisc_1(D_388, B_389))) | ~v1_funct_2(F_387, D_388, B_389) | ~v1_funct_1(F_387) | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(C_391, B_389))) | ~v1_funct_2(E_390, C_391, B_389) | ~v1_funct_1(E_390) | ~m1_subset_1(D_388, k1_zfmisc_1(A_392)) | v1_xboole_0(D_388) | ~m1_subset_1(C_391, k1_zfmisc_1(A_392)) | v1_xboole_0(C_391) | v1_xboole_0(B_389) | v1_xboole_0(A_392))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.98/2.72  tff(c_1448, plain, (![A_392, C_391, E_390]: (v1_funct_1(k1_tmap_1(A_392, '#skF_2', C_391, '#skF_4', E_390, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(C_391, '#skF_2'))) | ~v1_funct_2(E_390, C_391, '#skF_2') | ~v1_funct_1(E_390) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_392)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_391, k1_zfmisc_1(A_392)) | v1_xboole_0(C_391) | v1_xboole_0('#skF_2') | v1_xboole_0(A_392))), inference(resolution, [status(thm)], [c_48, c_1446])).
% 7.98/2.72  tff(c_1453, plain, (![A_392, C_391, E_390]: (v1_funct_1(k1_tmap_1(A_392, '#skF_2', C_391, '#skF_4', E_390, '#skF_6')) | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(C_391, '#skF_2'))) | ~v1_funct_2(E_390, C_391, '#skF_2') | ~v1_funct_1(E_390) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_392)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_391, k1_zfmisc_1(A_392)) | v1_xboole_0(C_391) | v1_xboole_0('#skF_2') | v1_xboole_0(A_392))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1448])).
% 7.98/2.72  tff(c_1459, plain, (![A_393, C_394, E_395]: (v1_funct_1(k1_tmap_1(A_393, '#skF_2', C_394, '#skF_4', E_395, '#skF_6')) | ~m1_subset_1(E_395, k1_zfmisc_1(k2_zfmisc_1(C_394, '#skF_2'))) | ~v1_funct_2(E_395, C_394, '#skF_2') | ~v1_funct_1(E_395) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_393)) | ~m1_subset_1(C_394, k1_zfmisc_1(A_393)) | v1_xboole_0(C_394) | v1_xboole_0(A_393))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1453])).
% 7.98/2.72  tff(c_1463, plain, (![A_393]: (v1_funct_1(k1_tmap_1(A_393, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_393)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_393)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_393))), inference(resolution, [status(thm)], [c_54, c_1459])).
% 7.98/2.72  tff(c_1470, plain, (![A_393]: (v1_funct_1(k1_tmap_1(A_393, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_393)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_393)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_393))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1463])).
% 7.98/2.72  tff(c_1479, plain, (![A_397]: (v1_funct_1(k1_tmap_1(A_397, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_397)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_397)) | v1_xboole_0(A_397))), inference(negUnitSimplification, [status(thm)], [c_68, c_1470])).
% 7.98/2.72  tff(c_1482, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_1479])).
% 7.98/2.72  tff(c_1485, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1482])).
% 7.98/2.72  tff(c_1486, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1485])).
% 7.98/2.72  tff(c_1616, plain, (![F_427, E_431, A_430, C_429, D_428, B_426]: (k2_partfun1(k4_subset_1(A_430, C_429, D_428), B_426, k1_tmap_1(A_430, B_426, C_429, D_428, E_431, F_427), D_428)=F_427 | ~m1_subset_1(k1_tmap_1(A_430, B_426, C_429, D_428, E_431, F_427), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_430, C_429, D_428), B_426))) | ~v1_funct_2(k1_tmap_1(A_430, B_426, C_429, D_428, E_431, F_427), k4_subset_1(A_430, C_429, D_428), B_426) | ~v1_funct_1(k1_tmap_1(A_430, B_426, C_429, D_428, E_431, F_427)) | k2_partfun1(D_428, B_426, F_427, k9_subset_1(A_430, C_429, D_428))!=k2_partfun1(C_429, B_426, E_431, k9_subset_1(A_430, C_429, D_428)) | ~m1_subset_1(F_427, k1_zfmisc_1(k2_zfmisc_1(D_428, B_426))) | ~v1_funct_2(F_427, D_428, B_426) | ~v1_funct_1(F_427) | ~m1_subset_1(E_431, k1_zfmisc_1(k2_zfmisc_1(C_429, B_426))) | ~v1_funct_2(E_431, C_429, B_426) | ~v1_funct_1(E_431) | ~m1_subset_1(D_428, k1_zfmisc_1(A_430)) | v1_xboole_0(D_428) | ~m1_subset_1(C_429, k1_zfmisc_1(A_430)) | v1_xboole_0(C_429) | v1_xboole_0(B_426) | v1_xboole_0(A_430))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.98/2.72  tff(c_1873, plain, (![A_517, B_514, D_513, E_515, F_512, C_516]: (k2_partfun1(k4_subset_1(A_517, C_516, D_513), B_514, k1_tmap_1(A_517, B_514, C_516, D_513, E_515, F_512), D_513)=F_512 | ~v1_funct_2(k1_tmap_1(A_517, B_514, C_516, D_513, E_515, F_512), k4_subset_1(A_517, C_516, D_513), B_514) | ~v1_funct_1(k1_tmap_1(A_517, B_514, C_516, D_513, E_515, F_512)) | k2_partfun1(D_513, B_514, F_512, k9_subset_1(A_517, C_516, D_513))!=k2_partfun1(C_516, B_514, E_515, k9_subset_1(A_517, C_516, D_513)) | ~m1_subset_1(F_512, k1_zfmisc_1(k2_zfmisc_1(D_513, B_514))) | ~v1_funct_2(F_512, D_513, B_514) | ~v1_funct_1(F_512) | ~m1_subset_1(E_515, k1_zfmisc_1(k2_zfmisc_1(C_516, B_514))) | ~v1_funct_2(E_515, C_516, B_514) | ~v1_funct_1(E_515) | ~m1_subset_1(D_513, k1_zfmisc_1(A_517)) | v1_xboole_0(D_513) | ~m1_subset_1(C_516, k1_zfmisc_1(A_517)) | v1_xboole_0(C_516) | v1_xboole_0(B_514) | v1_xboole_0(A_517))), inference(resolution, [status(thm)], [c_40, c_1616])).
% 7.98/2.72  tff(c_2330, plain, (![F_582, D_583, B_584, C_586, E_585, A_587]: (k2_partfun1(k4_subset_1(A_587, C_586, D_583), B_584, k1_tmap_1(A_587, B_584, C_586, D_583, E_585, F_582), D_583)=F_582 | ~v1_funct_1(k1_tmap_1(A_587, B_584, C_586, D_583, E_585, F_582)) | k2_partfun1(D_583, B_584, F_582, k9_subset_1(A_587, C_586, D_583))!=k2_partfun1(C_586, B_584, E_585, k9_subset_1(A_587, C_586, D_583)) | ~m1_subset_1(F_582, k1_zfmisc_1(k2_zfmisc_1(D_583, B_584))) | ~v1_funct_2(F_582, D_583, B_584) | ~v1_funct_1(F_582) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(C_586, B_584))) | ~v1_funct_2(E_585, C_586, B_584) | ~v1_funct_1(E_585) | ~m1_subset_1(D_583, k1_zfmisc_1(A_587)) | v1_xboole_0(D_583) | ~m1_subset_1(C_586, k1_zfmisc_1(A_587)) | v1_xboole_0(C_586) | v1_xboole_0(B_584) | v1_xboole_0(A_587))), inference(resolution, [status(thm)], [c_42, c_1873])).
% 7.98/2.72  tff(c_2334, plain, (![A_587, C_586, E_585]: (k2_partfun1(k4_subset_1(A_587, C_586, '#skF_4'), '#skF_2', k1_tmap_1(A_587, '#skF_2', C_586, '#skF_4', E_585, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_587, '#skF_2', C_586, '#skF_4', E_585, '#skF_6')) | k2_partfun1(C_586, '#skF_2', E_585, k9_subset_1(A_587, C_586, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_587, C_586, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(C_586, '#skF_2'))) | ~v1_funct_2(E_585, C_586, '#skF_2') | ~v1_funct_1(E_585) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_587)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_586, k1_zfmisc_1(A_587)) | v1_xboole_0(C_586) | v1_xboole_0('#skF_2') | v1_xboole_0(A_587))), inference(resolution, [status(thm)], [c_48, c_2330])).
% 7.98/2.72  tff(c_2340, plain, (![A_587, C_586, E_585]: (k2_partfun1(k4_subset_1(A_587, C_586, '#skF_4'), '#skF_2', k1_tmap_1(A_587, '#skF_2', C_586, '#skF_4', E_585, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_587, '#skF_2', C_586, '#skF_4', E_585, '#skF_6')) | k2_partfun1(C_586, '#skF_2', E_585, k9_subset_1(A_587, C_586, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_587, C_586, '#skF_4')) | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(C_586, '#skF_2'))) | ~v1_funct_2(E_585, C_586, '#skF_2') | ~v1_funct_1(E_585) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_587)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_586, k1_zfmisc_1(A_587)) | v1_xboole_0(C_586) | v1_xboole_0('#skF_2') | v1_xboole_0(A_587))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1186, c_2334])).
% 7.98/2.72  tff(c_2643, plain, (![A_645, C_646, E_647]: (k2_partfun1(k4_subset_1(A_645, C_646, '#skF_4'), '#skF_2', k1_tmap_1(A_645, '#skF_2', C_646, '#skF_4', E_647, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_645, '#skF_2', C_646, '#skF_4', E_647, '#skF_6')) | k2_partfun1(C_646, '#skF_2', E_647, k9_subset_1(A_645, C_646, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_645, C_646, '#skF_4')) | ~m1_subset_1(E_647, k1_zfmisc_1(k2_zfmisc_1(C_646, '#skF_2'))) | ~v1_funct_2(E_647, C_646, '#skF_2') | ~v1_funct_1(E_647) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_645)) | ~m1_subset_1(C_646, k1_zfmisc_1(A_645)) | v1_xboole_0(C_646) | v1_xboole_0(A_645))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_2340])).
% 7.98/2.72  tff(c_2650, plain, (![A_645]: (k2_partfun1(k4_subset_1(A_645, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_645, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_645, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_645, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_645, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_645)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_645)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_645))), inference(resolution, [status(thm)], [c_54, c_2643])).
% 7.98/2.72  tff(c_2660, plain, (![A_645]: (k2_partfun1(k4_subset_1(A_645, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_645, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_645, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_645, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_645, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_645)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_645)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_645))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1189, c_2650])).
% 7.98/2.72  tff(c_2662, plain, (![A_648]: (k2_partfun1(k4_subset_1(A_648, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_648, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_648, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_648, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_648, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_648)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_648)) | v1_xboole_0(A_648))), inference(negUnitSimplification, [status(thm)], [c_68, c_2660])).
% 7.98/2.72  tff(c_310, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 7.98/2.72  tff(c_1352, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_310])).
% 7.98/2.72  tff(c_2673, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2662, c_1352])).
% 7.98/2.72  tff(c_2687, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1249, c_1202, c_381, c_1253, c_1202, c_381, c_1486, c_2673])).
% 7.98/2.72  tff(c_2689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2687])).
% 7.98/2.72  tff(c_2690, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_310])).
% 7.98/2.72  tff(c_4084, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4075, c_2690])).
% 7.98/2.72  tff(c_4095, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1249, c_1202, c_381, c_1253, c_1202, c_381, c_2830, c_4084])).
% 7.98/2.72  tff(c_4097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_4095])).
% 7.98/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/2.72  
% 7.98/2.72  Inference rules
% 7.98/2.72  ----------------------
% 7.98/2.72  #Ref     : 0
% 7.98/2.72  #Sup     : 821
% 7.98/2.72  #Fact    : 0
% 7.98/2.72  #Define  : 0
% 7.98/2.72  #Split   : 32
% 7.98/2.72  #Chain   : 0
% 7.98/2.72  #Close   : 0
% 7.98/2.72  
% 7.98/2.72  Ordering : KBO
% 7.98/2.72  
% 7.98/2.72  Simplification rules
% 7.98/2.72  ----------------------
% 7.98/2.72  #Subsume      : 71
% 7.98/2.72  #Demod        : 707
% 7.98/2.72  #Tautology    : 392
% 7.98/2.72  #SimpNegUnit  : 207
% 7.98/2.72  #BackRed      : 12
% 7.98/2.72  
% 7.98/2.72  #Partial instantiations: 0
% 7.98/2.72  #Strategies tried      : 1
% 7.98/2.72  
% 7.98/2.72  Timing (in seconds)
% 7.98/2.72  ----------------------
% 7.98/2.72  Preprocessing        : 0.41
% 7.98/2.72  Parsing              : 0.20
% 7.98/2.72  CNF conversion       : 0.06
% 7.98/2.72  Main loop            : 1.48
% 7.98/2.72  Inferencing          : 0.57
% 7.98/2.72  Reduction            : 0.49
% 7.98/2.72  Demodulation         : 0.36
% 7.98/2.72  BG Simplification    : 0.06
% 7.98/2.72  Subsumption          : 0.26
% 7.98/2.72  Abstraction          : 0.07
% 7.98/2.72  MUC search           : 0.00
% 7.98/2.72  Cooper               : 0.00
% 7.98/2.72  Total                : 1.94
% 7.98/2.72  Index Insertion      : 0.00
% 7.98/2.72  Index Deletion       : 0.00
% 7.98/2.72  Index Matching       : 0.00
% 7.98/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
