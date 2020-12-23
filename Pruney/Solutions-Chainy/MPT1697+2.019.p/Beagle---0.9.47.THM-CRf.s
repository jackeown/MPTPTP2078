%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:12 EST 2020

% Result     : Theorem 16.29s
% Output     : CNFRefutation 16.63s
% Verified   : 
% Statistics : Number of formulae       :  275 (1186 expanded)
%              Number of leaves         :   44 ( 428 expanded)
%              Depth                    :   16
%              Number of atoms          :  830 (5873 expanded)
%              Number of equality atoms :  181 (1098 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
       => r1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_64,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_1602,plain,(
    ! [B_403,A_404] :
      ( r1_subset_1(B_403,A_404)
      | ~ r1_subset_1(A_404,B_403)
      | v1_xboole_0(B_403)
      | v1_xboole_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1604,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1602])).

tff(c_1607,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_1604])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | ~ r1_subset_1(A_17,B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_1524,plain,(
    ! [C_385,A_386,B_387] :
      ( v1_relat_1(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1531,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1524])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_1533,plain,(
    ! [C_388,A_389,B_390] :
      ( v4_relat_1(C_388,A_389)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1540,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1533])).

tff(c_1663,plain,(
    ! [B_412,A_413] :
      ( k1_relat_1(B_412) = A_413
      | ~ v1_partfun1(B_412,A_413)
      | ~ v4_relat_1(B_412,A_413)
      | ~ v1_relat_1(B_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1669,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1540,c_1663])).

tff(c_1675,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_1669])).

tff(c_14752,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1675])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_15173,plain,(
    ! [C_1082,A_1083,B_1084] :
      ( v1_partfun1(C_1082,A_1083)
      | ~ v1_funct_2(C_1082,A_1083,B_1084)
      | ~ v1_funct_1(C_1082)
      | ~ m1_subset_1(C_1082,k1_zfmisc_1(k2_zfmisc_1(A_1083,B_1084)))
      | v1_xboole_0(B_1084) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_15176,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_15173])).

tff(c_15182,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_15176])).

tff(c_15184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_14752,c_15182])).

tff(c_15185,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1675])).

tff(c_12,plain,(
    ! [A_12,B_14] :
      ( k7_relat_1(A_12,B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,k1_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_15193,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_5',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15185,c_12])).

tff(c_15219,plain,(
    ! [B_1086] :
      ( k7_relat_1('#skF_5',B_1086) = k1_xboole_0
      | ~ r1_xboole_0(B_1086,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_15193])).

tff(c_15223,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_5',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_15219])).

tff(c_15312,plain,(
    ! [A_1093] :
      ( k7_relat_1('#skF_5',A_1093) = k1_xboole_0
      | ~ r1_subset_1(A_1093,'#skF_3')
      | v1_xboole_0(A_1093) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_15223])).

tff(c_15315,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1607,c_15312])).

tff(c_15318,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_15315])).

tff(c_1542,plain,(
    ! [B_391,A_392] :
      ( k7_relat_1(B_391,A_392) = B_391
      | ~ v4_relat_1(B_391,A_392)
      | ~ v1_relat_1(B_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1548,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1540,c_1542])).

tff(c_1554,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_1548])).

tff(c_15248,plain,(
    ! [C_1088,A_1089,B_1090] :
      ( k7_relat_1(k7_relat_1(C_1088,A_1089),B_1090) = k7_relat_1(C_1088,k3_xboole_0(A_1089,B_1090))
      | ~ v1_relat_1(C_1088) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_15266,plain,(
    ! [B_1090] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_1090)) = k7_relat_1('#skF_5',B_1090)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1554,c_15248])).

tff(c_15275,plain,(
    ! [B_1090] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_1090)) = k7_relat_1('#skF_5',B_1090) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_15266])).

tff(c_15433,plain,(
    ! [A_1100,B_1101,C_1102,D_1103] :
      ( k2_partfun1(A_1100,B_1101,C_1102,D_1103) = k7_relat_1(C_1102,D_1103)
      | ~ m1_subset_1(C_1102,k1_zfmisc_1(k2_zfmisc_1(A_1100,B_1101)))
      | ~ v1_funct_1(C_1102) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_15435,plain,(
    ! [D_1103] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1103) = k7_relat_1('#skF_5',D_1103)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_15433])).

tff(c_15440,plain,(
    ! [D_1103] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1103) = k7_relat_1('#skF_5',D_1103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_15435])).

tff(c_1613,plain,(
    ! [A_405,B_406,C_407] :
      ( k9_subset_1(A_405,B_406,C_407) = k3_xboole_0(B_406,C_407)
      | ~ m1_subset_1(C_407,k1_zfmisc_1(A_405)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1624,plain,(
    ! [B_406] : k9_subset_1('#skF_1',B_406,'#skF_4') = k3_xboole_0(B_406,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1613])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_105,plain,(
    ! [C_233,A_234,B_235] :
      ( v1_relat_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_113,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_105])).

tff(c_124,plain,(
    ! [C_241,A_242,B_243] :
      ( v4_relat_1(C_241,A_242)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_132,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_124])).

tff(c_240,plain,(
    ! [B_260,A_261] :
      ( k1_relat_1(B_260) = A_261
      | ~ v1_partfun1(B_260,A_261)
      | ~ v4_relat_1(B_260,A_261)
      | ~ v1_relat_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_243,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_132,c_240])).

tff(c_249,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_243])).

tff(c_253,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_814,plain,(
    ! [C_311,A_312,B_313] :
      ( v1_partfun1(C_311,A_312)
      | ~ v1_funct_2(C_311,A_312,B_313)
      | ~ v1_funct_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313)))
      | v1_xboole_0(B_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_820,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_814])).

tff(c_827,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_820])).

tff(c_829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_253,c_827])).

tff(c_830,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_838,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_6',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_12])).

tff(c_1105,plain,(
    ! [B_339] :
      ( k7_relat_1('#skF_6',B_339) = k1_xboole_0
      | ~ r1_xboole_0(B_339,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_838])).

tff(c_1109,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_6',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_1105])).

tff(c_1305,plain,(
    ! [A_355] :
      ( k7_relat_1('#skF_6',A_355) = k1_xboole_0
      | ~ r1_subset_1(A_355,'#skF_4')
      | v1_xboole_0(A_355) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1109])).

tff(c_1308,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1305])).

tff(c_1311,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1308])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( k7_relat_1(k7_relat_1(C_11,A_9),B_10) = k7_relat_1(C_11,k3_xboole_0(A_9,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1318,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_10])).

tff(c_1326,plain,(
    ! [B_10] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1318])).

tff(c_1269,plain,(
    ! [A_349,B_350,C_351,D_352] :
      ( k2_partfun1(A_349,B_350,C_351,D_352) = k7_relat_1(C_351,D_352)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_349,B_350)))
      | ~ v1_funct_1(C_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1273,plain,(
    ! [D_352] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_352) = k7_relat_1('#skF_6',D_352)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_1269])).

tff(c_1279,plain,(
    ! [D_352] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_352) = k7_relat_1('#skF_6',D_352) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1273])).

tff(c_179,plain,(
    ! [B_251,A_252] :
      ( r1_subset_1(B_251,A_252)
      | ~ r1_subset_1(A_252,B_251)
      | v1_xboole_0(B_251)
      | v1_xboole_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_181,plain,
    ( r1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_179])).

tff(c_184,plain,(
    r1_subset_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_181])).

tff(c_112,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_105])).

tff(c_131,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_124])).

tff(c_246,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_240])).

tff(c_252,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_246])).

tff(c_847,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_1063,plain,(
    ! [C_335,A_336,B_337] :
      ( v1_partfun1(C_335,A_336)
      | ~ v1_funct_2(C_335,A_336,B_337)
      | ~ v1_funct_1(C_335)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_336,B_337)))
      | v1_xboole_0(B_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1066,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1063])).

tff(c_1072,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1066])).

tff(c_1074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_847,c_1072])).

tff(c_1075,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_1083,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_5',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_12])).

tff(c_1092,plain,(
    ! [B_338] :
      ( k7_relat_1('#skF_5',B_338) = k1_xboole_0
      | ~ r1_xboole_0(B_338,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1083])).

tff(c_1096,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_5',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_1092])).

tff(c_1224,plain,(
    ! [A_347] :
      ( k7_relat_1('#skF_5',A_347) = k1_xboole_0
      | ~ r1_subset_1(A_347,'#skF_3')
      | v1_xboole_0(A_347) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1096])).

tff(c_1227,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_1224])).

tff(c_1230,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1227])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_14])).

tff(c_138,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_135])).

tff(c_1134,plain,(
    ! [C_341,A_342,B_343] :
      ( k7_relat_1(k7_relat_1(C_341,A_342),B_343) = k7_relat_1(C_341,k3_xboole_0(A_342,B_343))
      | ~ v1_relat_1(C_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1155,plain,(
    ! [B_343] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_343)) = k7_relat_1('#skF_5',B_343)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_1134])).

tff(c_1163,plain,(
    ! [B_343] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_343)) = k7_relat_1('#skF_5',B_343) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1155])).

tff(c_1271,plain,(
    ! [D_352] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_352) = k7_relat_1('#skF_5',D_352)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_1269])).

tff(c_1276,plain,(
    ! [D_352] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_352) = k7_relat_1('#skF_5',D_352) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1271])).

tff(c_190,plain,(
    ! [A_253,B_254,C_255] :
      ( k9_subset_1(A_253,B_254,C_255) = k3_xboole_0(B_254,C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(A_253)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    ! [B_254] : k9_subset_1('#skF_1',B_254,'#skF_4') = k3_xboole_0(B_254,'#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_190])).

tff(c_50,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_104,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_203,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_201,c_104])).

tff(c_1280,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1276,c_203])).

tff(c_1281,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_1163,c_1280])).

tff(c_1300,plain,(
    k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_1281])).

tff(c_1329,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1300])).

tff(c_153,plain,(
    ! [A_244,B_245] :
      ( r1_xboole_0(A_244,B_245)
      | ~ r1_subset_1(A_244,B_245)
      | v1_xboole_0(B_245)
      | v1_xboole_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1409,plain,(
    ! [A_374,B_375] :
      ( k3_xboole_0(A_374,B_375) = k1_xboole_0
      | ~ r1_subset_1(A_374,B_375)
      | v1_xboole_0(B_375)
      | v1_xboole_0(A_374) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_1415,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_1409])).

tff(c_1422,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_72,c_1415])).

tff(c_141,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_132,c_14])).

tff(c_144,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_141])).

tff(c_1152,plain,(
    ! [B_343] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',B_343)) = k7_relat_1('#skF_6',B_343)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1134])).

tff(c_1161,plain,(
    ! [B_343] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',B_343)) = k7_relat_1('#skF_6',B_343) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1152])).

tff(c_1438,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_1161])).

tff(c_1442,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1311,c_1438])).

tff(c_1418,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1409])).

tff(c_1425,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_1418])).

tff(c_1454,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_1326])).

tff(c_1520,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_1454])).

tff(c_1521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1329,c_1520])).

tff(c_1523,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1626,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1624,c_1523])).

tff(c_15444,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15440,c_1626])).

tff(c_15445,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15318,c_15275,c_15444])).

tff(c_15437,plain,(
    ! [D_1103] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1103) = k7_relat_1('#skF_6',D_1103)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_15433])).

tff(c_15443,plain,(
    ! [D_1103] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1103) = k7_relat_1('#skF_6',D_1103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_15437])).

tff(c_15467,plain,(
    k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15445,c_15443])).

tff(c_1532,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1524])).

tff(c_1541,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1533])).

tff(c_1666,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1541,c_1663])).

tff(c_1672,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1666])).

tff(c_1676,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1672])).

tff(c_2259,plain,(
    ! [C_462,A_463,B_464] :
      ( v1_partfun1(C_462,A_463)
      | ~ v1_funct_2(C_462,A_463,B_464)
      | ~ v1_funct_1(C_462)
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))
      | v1_xboole_0(B_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2265,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2259])).

tff(c_2272,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2265])).

tff(c_2274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1676,c_2272])).

tff(c_2275,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1672])).

tff(c_2283,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_6',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2275,c_12])).

tff(c_15206,plain,(
    ! [B_1085] :
      ( k7_relat_1('#skF_6',B_1085) = k1_xboole_0
      | ~ r1_xboole_0(B_1085,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_2283])).

tff(c_15210,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_6',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_15206])).

tff(c_15387,plain,(
    ! [A_1096] :
      ( k7_relat_1('#skF_6',A_1096) = k1_xboole_0
      | ~ r1_subset_1(A_1096,'#skF_4')
      | v1_xboole_0(A_1096) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_15210])).

tff(c_15390,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_15387])).

tff(c_15393,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_15390])).

tff(c_15397,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15393,c_10])).

tff(c_15407,plain,(
    ! [B_10] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_15397])).

tff(c_15477,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15467,c_15407])).

tff(c_15615,plain,(
    ! [A_1115,C_1119,F_1118,D_1114,B_1116,E_1117] :
      ( v1_funct_1(k1_tmap_1(A_1115,B_1116,C_1119,D_1114,E_1117,F_1118))
      | ~ m1_subset_1(F_1118,k1_zfmisc_1(k2_zfmisc_1(D_1114,B_1116)))
      | ~ v1_funct_2(F_1118,D_1114,B_1116)
      | ~ v1_funct_1(F_1118)
      | ~ m1_subset_1(E_1117,k1_zfmisc_1(k2_zfmisc_1(C_1119,B_1116)))
      | ~ v1_funct_2(E_1117,C_1119,B_1116)
      | ~ v1_funct_1(E_1117)
      | ~ m1_subset_1(D_1114,k1_zfmisc_1(A_1115))
      | v1_xboole_0(D_1114)
      | ~ m1_subset_1(C_1119,k1_zfmisc_1(A_1115))
      | v1_xboole_0(C_1119)
      | v1_xboole_0(B_1116)
      | v1_xboole_0(A_1115) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_15619,plain,(
    ! [A_1115,C_1119,E_1117] :
      ( v1_funct_1(k1_tmap_1(A_1115,'#skF_2',C_1119,'#skF_4',E_1117,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1117,k1_zfmisc_1(k2_zfmisc_1(C_1119,'#skF_2')))
      | ~ v1_funct_2(E_1117,C_1119,'#skF_2')
      | ~ v1_funct_1(E_1117)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1115))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1119,k1_zfmisc_1(A_1115))
      | v1_xboole_0(C_1119)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1115) ) ),
    inference(resolution,[status(thm)],[c_52,c_15615])).

tff(c_15626,plain,(
    ! [A_1115,C_1119,E_1117] :
      ( v1_funct_1(k1_tmap_1(A_1115,'#skF_2',C_1119,'#skF_4',E_1117,'#skF_6'))
      | ~ m1_subset_1(E_1117,k1_zfmisc_1(k2_zfmisc_1(C_1119,'#skF_2')))
      | ~ v1_funct_2(E_1117,C_1119,'#skF_2')
      | ~ v1_funct_1(E_1117)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1115))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1119,k1_zfmisc_1(A_1115))
      | v1_xboole_0(C_1119)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_15619])).

tff(c_16088,plain,(
    ! [A_1171,C_1172,E_1173] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2',C_1172,'#skF_4',E_1173,'#skF_6'))
      | ~ m1_subset_1(E_1173,k1_zfmisc_1(k2_zfmisc_1(C_1172,'#skF_2')))
      | ~ v1_funct_2(E_1173,C_1172,'#skF_2')
      | ~ v1_funct_1(E_1173)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1(C_1172,k1_zfmisc_1(A_1171))
      | v1_xboole_0(C_1172)
      | v1_xboole_0(A_1171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_15626])).

tff(c_16093,plain,(
    ! [A_1171] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1171))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1171) ) ),
    inference(resolution,[status(thm)],[c_58,c_16088])).

tff(c_16101,plain,(
    ! [A_1171] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1171))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_16093])).

tff(c_16273,plain,(
    ! [A_1194] :
      ( v1_funct_1(k1_tmap_1(A_1194,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1194))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1194))
      | v1_xboole_0(A_1194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_16101])).

tff(c_16276,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_16273])).

tff(c_16279,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16276])).

tff(c_16280,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16279])).

tff(c_46,plain,(
    ! [C_166,D_167,E_168,A_164,B_165,F_169] :
      ( v1_funct_2(k1_tmap_1(A_164,B_165,C_166,D_167,E_168,F_169),k4_subset_1(A_164,C_166,D_167),B_165)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(D_167,B_165)))
      | ~ v1_funct_2(F_169,D_167,B_165)
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(C_166,B_165)))
      | ~ v1_funct_2(E_168,C_166,B_165)
      | ~ v1_funct_1(E_168)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(A_164))
      | v1_xboole_0(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(A_164))
      | v1_xboole_0(C_166)
      | v1_xboole_0(B_165)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_44,plain,(
    ! [C_166,D_167,E_168,A_164,B_165,F_169] :
      ( m1_subset_1(k1_tmap_1(A_164,B_165,C_166,D_167,E_168,F_169),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_164,C_166,D_167),B_165)))
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(D_167,B_165)))
      | ~ v1_funct_2(F_169,D_167,B_165)
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(C_166,B_165)))
      | ~ v1_funct_2(E_168,C_166,B_165)
      | ~ v1_funct_1(E_168)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(A_164))
      | v1_xboole_0(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(A_164))
      | v1_xboole_0(C_166)
      | v1_xboole_0(B_165)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_16082,plain,(
    ! [A_1165,B_1168,E_1169,C_1166,F_1167,D_1170] :
      ( k2_partfun1(k4_subset_1(A_1165,C_1166,D_1170),B_1168,k1_tmap_1(A_1165,B_1168,C_1166,D_1170,E_1169,F_1167),C_1166) = E_1169
      | ~ m1_subset_1(k1_tmap_1(A_1165,B_1168,C_1166,D_1170,E_1169,F_1167),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1165,C_1166,D_1170),B_1168)))
      | ~ v1_funct_2(k1_tmap_1(A_1165,B_1168,C_1166,D_1170,E_1169,F_1167),k4_subset_1(A_1165,C_1166,D_1170),B_1168)
      | ~ v1_funct_1(k1_tmap_1(A_1165,B_1168,C_1166,D_1170,E_1169,F_1167))
      | k2_partfun1(D_1170,B_1168,F_1167,k9_subset_1(A_1165,C_1166,D_1170)) != k2_partfun1(C_1166,B_1168,E_1169,k9_subset_1(A_1165,C_1166,D_1170))
      | ~ m1_subset_1(F_1167,k1_zfmisc_1(k2_zfmisc_1(D_1170,B_1168)))
      | ~ v1_funct_2(F_1167,D_1170,B_1168)
      | ~ v1_funct_1(F_1167)
      | ~ m1_subset_1(E_1169,k1_zfmisc_1(k2_zfmisc_1(C_1166,B_1168)))
      | ~ v1_funct_2(E_1169,C_1166,B_1168)
      | ~ v1_funct_1(E_1169)
      | ~ m1_subset_1(D_1170,k1_zfmisc_1(A_1165))
      | v1_xboole_0(D_1170)
      | ~ m1_subset_1(C_1166,k1_zfmisc_1(A_1165))
      | v1_xboole_0(C_1166)
      | v1_xboole_0(B_1168)
      | v1_xboole_0(A_1165) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_17762,plain,(
    ! [C_1358,A_1354,B_1355,E_1356,F_1357,D_1353] :
      ( k2_partfun1(k4_subset_1(A_1354,C_1358,D_1353),B_1355,k1_tmap_1(A_1354,B_1355,C_1358,D_1353,E_1356,F_1357),C_1358) = E_1356
      | ~ v1_funct_2(k1_tmap_1(A_1354,B_1355,C_1358,D_1353,E_1356,F_1357),k4_subset_1(A_1354,C_1358,D_1353),B_1355)
      | ~ v1_funct_1(k1_tmap_1(A_1354,B_1355,C_1358,D_1353,E_1356,F_1357))
      | k2_partfun1(D_1353,B_1355,F_1357,k9_subset_1(A_1354,C_1358,D_1353)) != k2_partfun1(C_1358,B_1355,E_1356,k9_subset_1(A_1354,C_1358,D_1353))
      | ~ m1_subset_1(F_1357,k1_zfmisc_1(k2_zfmisc_1(D_1353,B_1355)))
      | ~ v1_funct_2(F_1357,D_1353,B_1355)
      | ~ v1_funct_1(F_1357)
      | ~ m1_subset_1(E_1356,k1_zfmisc_1(k2_zfmisc_1(C_1358,B_1355)))
      | ~ v1_funct_2(E_1356,C_1358,B_1355)
      | ~ v1_funct_1(E_1356)
      | ~ m1_subset_1(D_1353,k1_zfmisc_1(A_1354))
      | v1_xboole_0(D_1353)
      | ~ m1_subset_1(C_1358,k1_zfmisc_1(A_1354))
      | v1_xboole_0(C_1358)
      | v1_xboole_0(B_1355)
      | v1_xboole_0(A_1354) ) ),
    inference(resolution,[status(thm)],[c_44,c_16082])).

tff(c_22214,plain,(
    ! [B_1555,D_1553,C_1558,A_1554,F_1557,E_1556] :
      ( k2_partfun1(k4_subset_1(A_1554,C_1558,D_1553),B_1555,k1_tmap_1(A_1554,B_1555,C_1558,D_1553,E_1556,F_1557),C_1558) = E_1556
      | ~ v1_funct_1(k1_tmap_1(A_1554,B_1555,C_1558,D_1553,E_1556,F_1557))
      | k2_partfun1(D_1553,B_1555,F_1557,k9_subset_1(A_1554,C_1558,D_1553)) != k2_partfun1(C_1558,B_1555,E_1556,k9_subset_1(A_1554,C_1558,D_1553))
      | ~ m1_subset_1(F_1557,k1_zfmisc_1(k2_zfmisc_1(D_1553,B_1555)))
      | ~ v1_funct_2(F_1557,D_1553,B_1555)
      | ~ v1_funct_1(F_1557)
      | ~ m1_subset_1(E_1556,k1_zfmisc_1(k2_zfmisc_1(C_1558,B_1555)))
      | ~ v1_funct_2(E_1556,C_1558,B_1555)
      | ~ v1_funct_1(E_1556)
      | ~ m1_subset_1(D_1553,k1_zfmisc_1(A_1554))
      | v1_xboole_0(D_1553)
      | ~ m1_subset_1(C_1558,k1_zfmisc_1(A_1554))
      | v1_xboole_0(C_1558)
      | v1_xboole_0(B_1555)
      | v1_xboole_0(A_1554) ) ),
    inference(resolution,[status(thm)],[c_46,c_17762])).

tff(c_22220,plain,(
    ! [A_1554,C_1558,E_1556] :
      ( k2_partfun1(k4_subset_1(A_1554,C_1558,'#skF_4'),'#skF_2',k1_tmap_1(A_1554,'#skF_2',C_1558,'#skF_4',E_1556,'#skF_6'),C_1558) = E_1556
      | ~ v1_funct_1(k1_tmap_1(A_1554,'#skF_2',C_1558,'#skF_4',E_1556,'#skF_6'))
      | k2_partfun1(C_1558,'#skF_2',E_1556,k9_subset_1(A_1554,C_1558,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1554,C_1558,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1556,k1_zfmisc_1(k2_zfmisc_1(C_1558,'#skF_2')))
      | ~ v1_funct_2(E_1556,C_1558,'#skF_2')
      | ~ v1_funct_1(E_1556)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1554))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1558,k1_zfmisc_1(A_1554))
      | v1_xboole_0(C_1558)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1554) ) ),
    inference(resolution,[status(thm)],[c_52,c_22214])).

tff(c_22228,plain,(
    ! [A_1554,C_1558,E_1556] :
      ( k2_partfun1(k4_subset_1(A_1554,C_1558,'#skF_4'),'#skF_2',k1_tmap_1(A_1554,'#skF_2',C_1558,'#skF_4',E_1556,'#skF_6'),C_1558) = E_1556
      | ~ v1_funct_1(k1_tmap_1(A_1554,'#skF_2',C_1558,'#skF_4',E_1556,'#skF_6'))
      | k2_partfun1(C_1558,'#skF_2',E_1556,k9_subset_1(A_1554,C_1558,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1554,C_1558,'#skF_4'))
      | ~ m1_subset_1(E_1556,k1_zfmisc_1(k2_zfmisc_1(C_1558,'#skF_2')))
      | ~ v1_funct_2(E_1556,C_1558,'#skF_2')
      | ~ v1_funct_1(E_1556)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1554))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1558,k1_zfmisc_1(A_1554))
      | v1_xboole_0(C_1558)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_15443,c_22220])).

tff(c_29933,plain,(
    ! [A_1675,C_1676,E_1677] :
      ( k2_partfun1(k4_subset_1(A_1675,C_1676,'#skF_4'),'#skF_2',k1_tmap_1(A_1675,'#skF_2',C_1676,'#skF_4',E_1677,'#skF_6'),C_1676) = E_1677
      | ~ v1_funct_1(k1_tmap_1(A_1675,'#skF_2',C_1676,'#skF_4',E_1677,'#skF_6'))
      | k2_partfun1(C_1676,'#skF_2',E_1677,k9_subset_1(A_1675,C_1676,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1675,C_1676,'#skF_4'))
      | ~ m1_subset_1(E_1677,k1_zfmisc_1(k2_zfmisc_1(C_1676,'#skF_2')))
      | ~ v1_funct_2(E_1677,C_1676,'#skF_2')
      | ~ v1_funct_1(E_1677)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1675))
      | ~ m1_subset_1(C_1676,k1_zfmisc_1(A_1675))
      | v1_xboole_0(C_1676)
      | v1_xboole_0(A_1675) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_22228])).

tff(c_29938,plain,(
    ! [A_1675] :
      ( k2_partfun1(k4_subset_1(A_1675,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1675,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1675,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1675,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1675,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1675))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1675))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1675) ) ),
    inference(resolution,[status(thm)],[c_58,c_29933])).

tff(c_29946,plain,(
    ! [A_1675] :
      ( k2_partfun1(k4_subset_1(A_1675,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1675,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1675,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1675,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1675,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1675))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1675))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1675) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_15440,c_29938])).

tff(c_30721,plain,(
    ! [A_1689] :
      ( k2_partfun1(k4_subset_1(A_1689,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1689,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1689,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1689,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1689,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1689))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1689))
      | v1_xboole_0(A_1689) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_29946])).

tff(c_2293,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1675])).

tff(c_2615,plain,(
    ! [C_487,A_488,B_489] :
      ( v1_partfun1(C_487,A_488)
      | ~ v1_funct_2(C_487,A_488,B_489)
      | ~ v1_funct_1(C_487)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k2_zfmisc_1(A_488,B_489)))
      | v1_xboole_0(B_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2618,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2615])).

tff(c_2624,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2618])).

tff(c_2626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2293,c_2624])).

tff(c_2627,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1675])).

tff(c_2635,plain,(
    ! [B_14] :
      ( k7_relat_1('#skF_5',B_14) = k1_xboole_0
      | ~ r1_xboole_0(B_14,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2627,c_12])).

tff(c_2661,plain,(
    ! [B_491] :
      ( k7_relat_1('#skF_5',B_491) = k1_xboole_0
      | ~ r1_xboole_0(B_491,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_2635])).

tff(c_2665,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_5',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_3')
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_2661])).

tff(c_2825,plain,(
    ! [A_501] :
      ( k7_relat_1('#skF_5',A_501) = k1_xboole_0
      | ~ r1_subset_1(A_501,'#skF_3')
      | v1_xboole_0(A_501) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2665])).

tff(c_2828,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1607,c_2825])).

tff(c_2831,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2828])).

tff(c_2690,plain,(
    ! [C_493,A_494,B_495] :
      ( k7_relat_1(k7_relat_1(C_493,A_494),B_495) = k7_relat_1(C_493,k3_xboole_0(A_494,B_495))
      | ~ v1_relat_1(C_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2708,plain,(
    ! [B_495] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_495)) = k7_relat_1('#skF_5',B_495)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1554,c_2690])).

tff(c_2717,plain,(
    ! [B_495] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',B_495)) = k7_relat_1('#skF_5',B_495) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_2708])).

tff(c_2872,plain,(
    ! [A_506,B_507,C_508,D_509] :
      ( k2_partfun1(A_506,B_507,C_508,D_509) = k7_relat_1(C_508,D_509)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_506,B_507)))
      | ~ v1_funct_1(C_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2874,plain,(
    ! [D_509] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_509) = k7_relat_1('#skF_5',D_509)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_2872])).

tff(c_2879,plain,(
    ! [D_509] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_509) = k7_relat_1('#skF_5',D_509) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2874])).

tff(c_2883,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) = k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2879,c_1626])).

tff(c_2884,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2831,c_2717,c_2883])).

tff(c_2876,plain,(
    ! [D_509] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_509) = k7_relat_1('#skF_6',D_509)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_2872])).

tff(c_2882,plain,(
    ! [D_509] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_509) = k7_relat_1('#skF_6',D_509) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2876])).

tff(c_2906,plain,(
    k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2884,c_2882])).

tff(c_2648,plain,(
    ! [B_490] :
      ( k7_relat_1('#skF_6',B_490) = k1_xboole_0
      | ~ r1_xboole_0(B_490,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_2283])).

tff(c_2652,plain,(
    ! [A_17] :
      ( k7_relat_1('#skF_6',A_17) = k1_xboole_0
      | ~ r1_subset_1(A_17,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_2648])).

tff(c_2754,plain,(
    ! [A_498] :
      ( k7_relat_1('#skF_6',A_498) = k1_xboole_0
      | ~ r1_subset_1(A_498,'#skF_4')
      | v1_xboole_0(A_498) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2652])).

tff(c_2757,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2754])).

tff(c_2760,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2757])).

tff(c_2764,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2760,c_10])).

tff(c_2774,plain,(
    ! [B_10] : k7_relat_1('#skF_6',k3_xboole_0('#skF_3',B_10)) = k7_relat_1(k1_xboole_0,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_2764])).

tff(c_2916,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2906,c_2774])).

tff(c_3073,plain,(
    ! [E_528,B_527,D_525,F_529,A_526,C_530] :
      ( v1_funct_1(k1_tmap_1(A_526,B_527,C_530,D_525,E_528,F_529))
      | ~ m1_subset_1(F_529,k1_zfmisc_1(k2_zfmisc_1(D_525,B_527)))
      | ~ v1_funct_2(F_529,D_525,B_527)
      | ~ v1_funct_1(F_529)
      | ~ m1_subset_1(E_528,k1_zfmisc_1(k2_zfmisc_1(C_530,B_527)))
      | ~ v1_funct_2(E_528,C_530,B_527)
      | ~ v1_funct_1(E_528)
      | ~ m1_subset_1(D_525,k1_zfmisc_1(A_526))
      | v1_xboole_0(D_525)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(A_526))
      | v1_xboole_0(C_530)
      | v1_xboole_0(B_527)
      | v1_xboole_0(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_3077,plain,(
    ! [A_526,C_530,E_528] :
      ( v1_funct_1(k1_tmap_1(A_526,'#skF_2',C_530,'#skF_4',E_528,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_528,k1_zfmisc_1(k2_zfmisc_1(C_530,'#skF_2')))
      | ~ v1_funct_2(E_528,C_530,'#skF_2')
      | ~ v1_funct_1(E_528)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_526))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_530,k1_zfmisc_1(A_526))
      | v1_xboole_0(C_530)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_526) ) ),
    inference(resolution,[status(thm)],[c_52,c_3073])).

tff(c_3084,plain,(
    ! [A_526,C_530,E_528] :
      ( v1_funct_1(k1_tmap_1(A_526,'#skF_2',C_530,'#skF_4',E_528,'#skF_6'))
      | ~ m1_subset_1(E_528,k1_zfmisc_1(k2_zfmisc_1(C_530,'#skF_2')))
      | ~ v1_funct_2(E_528,C_530,'#skF_2')
      | ~ v1_funct_1(E_528)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_526))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_530,k1_zfmisc_1(A_526))
      | v1_xboole_0(C_530)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_526) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3077])).

tff(c_3566,plain,(
    ! [A_578,C_579,E_580] :
      ( v1_funct_1(k1_tmap_1(A_578,'#skF_2',C_579,'#skF_4',E_580,'#skF_6'))
      | ~ m1_subset_1(E_580,k1_zfmisc_1(k2_zfmisc_1(C_579,'#skF_2')))
      | ~ v1_funct_2(E_580,C_579,'#skF_2')
      | ~ v1_funct_1(E_580)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_578))
      | ~ m1_subset_1(C_579,k1_zfmisc_1(A_578))
      | v1_xboole_0(C_579)
      | v1_xboole_0(A_578) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_3084])).

tff(c_3571,plain,(
    ! [A_578] :
      ( v1_funct_1(k1_tmap_1(A_578,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_578))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_578))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_578) ) ),
    inference(resolution,[status(thm)],[c_58,c_3566])).

tff(c_3579,plain,(
    ! [A_578] :
      ( v1_funct_1(k1_tmap_1(A_578,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_578))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_578))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_3571])).

tff(c_3716,plain,(
    ! [A_599] :
      ( v1_funct_1(k1_tmap_1(A_599,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_599))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_599))
      | v1_xboole_0(A_599) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3579])).

tff(c_3719,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_3716])).

tff(c_3722,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3719])).

tff(c_3723,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3722])).

tff(c_3352,plain,(
    ! [A_555,B_558,D_560,F_557,E_559,C_556] :
      ( k2_partfun1(k4_subset_1(A_555,C_556,D_560),B_558,k1_tmap_1(A_555,B_558,C_556,D_560,E_559,F_557),D_560) = F_557
      | ~ m1_subset_1(k1_tmap_1(A_555,B_558,C_556,D_560,E_559,F_557),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_555,C_556,D_560),B_558)))
      | ~ v1_funct_2(k1_tmap_1(A_555,B_558,C_556,D_560,E_559,F_557),k4_subset_1(A_555,C_556,D_560),B_558)
      | ~ v1_funct_1(k1_tmap_1(A_555,B_558,C_556,D_560,E_559,F_557))
      | k2_partfun1(D_560,B_558,F_557,k9_subset_1(A_555,C_556,D_560)) != k2_partfun1(C_556,B_558,E_559,k9_subset_1(A_555,C_556,D_560))
      | ~ m1_subset_1(F_557,k1_zfmisc_1(k2_zfmisc_1(D_560,B_558)))
      | ~ v1_funct_2(F_557,D_560,B_558)
      | ~ v1_funct_1(F_557)
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(C_556,B_558)))
      | ~ v1_funct_2(E_559,C_556,B_558)
      | ~ v1_funct_1(E_559)
      | ~ m1_subset_1(D_560,k1_zfmisc_1(A_555))
      | v1_xboole_0(D_560)
      | ~ m1_subset_1(C_556,k1_zfmisc_1(A_555))
      | v1_xboole_0(C_556)
      | v1_xboole_0(B_558)
      | v1_xboole_0(A_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_5113,plain,(
    ! [B_747,D_745,A_746,F_749,E_748,C_750] :
      ( k2_partfun1(k4_subset_1(A_746,C_750,D_745),B_747,k1_tmap_1(A_746,B_747,C_750,D_745,E_748,F_749),D_745) = F_749
      | ~ v1_funct_2(k1_tmap_1(A_746,B_747,C_750,D_745,E_748,F_749),k4_subset_1(A_746,C_750,D_745),B_747)
      | ~ v1_funct_1(k1_tmap_1(A_746,B_747,C_750,D_745,E_748,F_749))
      | k2_partfun1(D_745,B_747,F_749,k9_subset_1(A_746,C_750,D_745)) != k2_partfun1(C_750,B_747,E_748,k9_subset_1(A_746,C_750,D_745))
      | ~ m1_subset_1(F_749,k1_zfmisc_1(k2_zfmisc_1(D_745,B_747)))
      | ~ v1_funct_2(F_749,D_745,B_747)
      | ~ v1_funct_1(F_749)
      | ~ m1_subset_1(E_748,k1_zfmisc_1(k2_zfmisc_1(C_750,B_747)))
      | ~ v1_funct_2(E_748,C_750,B_747)
      | ~ v1_funct_1(E_748)
      | ~ m1_subset_1(D_745,k1_zfmisc_1(A_746))
      | v1_xboole_0(D_745)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(A_746))
      | v1_xboole_0(C_750)
      | v1_xboole_0(B_747)
      | v1_xboole_0(A_746) ) ),
    inference(resolution,[status(thm)],[c_44,c_3352])).

tff(c_9734,plain,(
    ! [D_966,C_971,F_970,B_968,E_969,A_967] :
      ( k2_partfun1(k4_subset_1(A_967,C_971,D_966),B_968,k1_tmap_1(A_967,B_968,C_971,D_966,E_969,F_970),D_966) = F_970
      | ~ v1_funct_1(k1_tmap_1(A_967,B_968,C_971,D_966,E_969,F_970))
      | k2_partfun1(D_966,B_968,F_970,k9_subset_1(A_967,C_971,D_966)) != k2_partfun1(C_971,B_968,E_969,k9_subset_1(A_967,C_971,D_966))
      | ~ m1_subset_1(F_970,k1_zfmisc_1(k2_zfmisc_1(D_966,B_968)))
      | ~ v1_funct_2(F_970,D_966,B_968)
      | ~ v1_funct_1(F_970)
      | ~ m1_subset_1(E_969,k1_zfmisc_1(k2_zfmisc_1(C_971,B_968)))
      | ~ v1_funct_2(E_969,C_971,B_968)
      | ~ v1_funct_1(E_969)
      | ~ m1_subset_1(D_966,k1_zfmisc_1(A_967))
      | v1_xboole_0(D_966)
      | ~ m1_subset_1(C_971,k1_zfmisc_1(A_967))
      | v1_xboole_0(C_971)
      | v1_xboole_0(B_968)
      | v1_xboole_0(A_967) ) ),
    inference(resolution,[status(thm)],[c_46,c_5113])).

tff(c_9740,plain,(
    ! [A_967,C_971,E_969] :
      ( k2_partfun1(k4_subset_1(A_967,C_971,'#skF_4'),'#skF_2',k1_tmap_1(A_967,'#skF_2',C_971,'#skF_4',E_969,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_967,'#skF_2',C_971,'#skF_4',E_969,'#skF_6'))
      | k2_partfun1(C_971,'#skF_2',E_969,k9_subset_1(A_967,C_971,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_967,C_971,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_969,k1_zfmisc_1(k2_zfmisc_1(C_971,'#skF_2')))
      | ~ v1_funct_2(E_969,C_971,'#skF_2')
      | ~ v1_funct_1(E_969)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_967))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_971,k1_zfmisc_1(A_967))
      | v1_xboole_0(C_971)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_967) ) ),
    inference(resolution,[status(thm)],[c_52,c_9734])).

tff(c_9748,plain,(
    ! [A_967,C_971,E_969] :
      ( k2_partfun1(k4_subset_1(A_967,C_971,'#skF_4'),'#skF_2',k1_tmap_1(A_967,'#skF_2',C_971,'#skF_4',E_969,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_967,'#skF_2',C_971,'#skF_4',E_969,'#skF_6'))
      | k2_partfun1(C_971,'#skF_2',E_969,k9_subset_1(A_967,C_971,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_967,C_971,'#skF_4'))
      | ~ m1_subset_1(E_969,k1_zfmisc_1(k2_zfmisc_1(C_971,'#skF_2')))
      | ~ v1_funct_2(E_969,C_971,'#skF_2')
      | ~ v1_funct_1(E_969)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_967))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_971,k1_zfmisc_1(A_967))
      | v1_xboole_0(C_971)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_967) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2882,c_9740])).

tff(c_13607,plain,(
    ! [A_1043,C_1044,E_1045] :
      ( k2_partfun1(k4_subset_1(A_1043,C_1044,'#skF_4'),'#skF_2',k1_tmap_1(A_1043,'#skF_2',C_1044,'#skF_4',E_1045,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1043,'#skF_2',C_1044,'#skF_4',E_1045,'#skF_6'))
      | k2_partfun1(C_1044,'#skF_2',E_1045,k9_subset_1(A_1043,C_1044,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1043,C_1044,'#skF_4'))
      | ~ m1_subset_1(E_1045,k1_zfmisc_1(k2_zfmisc_1(C_1044,'#skF_2')))
      | ~ v1_funct_2(E_1045,C_1044,'#skF_2')
      | ~ v1_funct_1(E_1045)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1043))
      | ~ m1_subset_1(C_1044,k1_zfmisc_1(A_1043))
      | v1_xboole_0(C_1044)
      | v1_xboole_0(A_1043) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_9748])).

tff(c_13612,plain,(
    ! [A_1043] :
      ( k2_partfun1(k4_subset_1(A_1043,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1043,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1043,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1043,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1043,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1043))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1043))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1043) ) ),
    inference(resolution,[status(thm)],[c_58,c_13607])).

tff(c_13620,plain,(
    ! [A_1043] :
      ( k2_partfun1(k4_subset_1(A_1043,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1043,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1043,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1043,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1043,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1043))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1043))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2879,c_13612])).

tff(c_14722,plain,(
    ! [A_1053] :
      ( k2_partfun1(k4_subset_1(A_1053,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1053,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1053,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1053,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1053,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1053))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1053))
      | v1_xboole_0(A_1053) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_13620])).

tff(c_1522,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2292,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1522])).

tff(c_14733,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14722,c_2292])).

tff(c_14747,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2916,c_2831,c_2774,c_2717,c_1624,c_1624,c_3723,c_14733])).

tff(c_14749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_14747])).

tff(c_14750,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1522])).

tff(c_30730,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30721,c_14750])).

tff(c_30741,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_15477,c_15407,c_15318,c_15275,c_1624,c_1624,c_16280,c_30730])).

tff(c_30743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_30741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.29/7.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.36/7.98  
% 16.36/7.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.36/7.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.36/7.99  
% 16.36/7.99  %Foreground sorts:
% 16.36/7.99  
% 16.36/7.99  
% 16.36/7.99  %Background operators:
% 16.36/7.99  
% 16.36/7.99  
% 16.36/7.99  %Foreground operators:
% 16.36/7.99  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 16.36/7.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.36/7.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.36/7.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.36/7.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.36/7.99  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.36/7.99  tff('#skF_5', type, '#skF_5': $i).
% 16.36/7.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.36/7.99  tff('#skF_6', type, '#skF_6': $i).
% 16.36/7.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.36/7.99  tff('#skF_2', type, '#skF_2': $i).
% 16.36/7.99  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 16.36/7.99  tff('#skF_3', type, '#skF_3': $i).
% 16.36/7.99  tff('#skF_1', type, '#skF_1': $i).
% 16.36/7.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.36/7.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.36/7.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.36/7.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.36/7.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.36/7.99  tff('#skF_4', type, '#skF_4': $i).
% 16.36/7.99  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.36/7.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.36/7.99  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 16.36/7.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.36/7.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.36/7.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.36/7.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.36/7.99  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.36/7.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.36/7.99  
% 16.63/8.03  tff(f_239, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 16.63/8.03  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) => r1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 16.63/8.03  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 16.63/8.03  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.63/8.03  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.63/8.03  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 16.63/8.03  tff(f_101, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 16.63/8.03  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 16.63/8.03  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 16.63/8.03  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 16.63/8.03  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 16.63/8.03  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 16.63/8.03  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 16.63/8.03  tff(f_197, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 16.63/8.03  tff(f_163, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 16.63/8.03  tff(c_76, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_64, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_1602, plain, (![B_403, A_404]: (r1_subset_1(B_403, A_404) | ~r1_subset_1(A_404, B_403) | v1_xboole_0(B_403) | v1_xboole_0(A_404))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.63/8.03  tff(c_1604, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1602])).
% 16.63/8.03  tff(c_1607, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_1604])).
% 16.63/8.03  tff(c_18, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | ~r1_subset_1(A_17, B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.03  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_1524, plain, (![C_385, A_386, B_387]: (v1_relat_1(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.63/8.03  tff(c_1531, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1524])).
% 16.63/8.03  tff(c_74, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_1533, plain, (![C_388, A_389, B_390]: (v4_relat_1(C_388, A_389) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.63/8.03  tff(c_1540, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_1533])).
% 16.63/8.03  tff(c_1663, plain, (![B_412, A_413]: (k1_relat_1(B_412)=A_413 | ~v1_partfun1(B_412, A_413) | ~v4_relat_1(B_412, A_413) | ~v1_relat_1(B_412))), inference(cnfTransformation, [status(thm)], [f_109])).
% 16.63/8.03  tff(c_1669, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1540, c_1663])).
% 16.63/8.03  tff(c_1675, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_1669])).
% 16.63/8.03  tff(c_14752, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1675])).
% 16.63/8.03  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_15173, plain, (![C_1082, A_1083, B_1084]: (v1_partfun1(C_1082, A_1083) | ~v1_funct_2(C_1082, A_1083, B_1084) | ~v1_funct_1(C_1082) | ~m1_subset_1(C_1082, k1_zfmisc_1(k2_zfmisc_1(A_1083, B_1084))) | v1_xboole_0(B_1084))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.63/8.03  tff(c_15176, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_15173])).
% 16.63/8.03  tff(c_15182, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_15176])).
% 16.63/8.03  tff(c_15184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_14752, c_15182])).
% 16.63/8.03  tff(c_15185, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1675])).
% 16.63/8.03  tff(c_12, plain, (![A_12, B_14]: (k7_relat_1(A_12, B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, k1_relat_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.63/8.03  tff(c_15193, plain, (![B_14]: (k7_relat_1('#skF_5', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15185, c_12])).
% 16.63/8.03  tff(c_15219, plain, (![B_1086]: (k7_relat_1('#skF_5', B_1086)=k1_xboole_0 | ~r1_xboole_0(B_1086, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_15193])).
% 16.63/8.03  tff(c_15223, plain, (![A_17]: (k7_relat_1('#skF_5', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_18, c_15219])).
% 16.63/8.03  tff(c_15312, plain, (![A_1093]: (k7_relat_1('#skF_5', A_1093)=k1_xboole_0 | ~r1_subset_1(A_1093, '#skF_3') | v1_xboole_0(A_1093))), inference(negUnitSimplification, [status(thm)], [c_72, c_15223])).
% 16.63/8.03  tff(c_15315, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1607, c_15312])).
% 16.63/8.03  tff(c_15318, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_15315])).
% 16.63/8.03  tff(c_1542, plain, (![B_391, A_392]: (k7_relat_1(B_391, A_392)=B_391 | ~v4_relat_1(B_391, A_392) | ~v1_relat_1(B_391))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.63/8.03  tff(c_1548, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1540, c_1542])).
% 16.63/8.03  tff(c_1554, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_1548])).
% 16.63/8.03  tff(c_15248, plain, (![C_1088, A_1089, B_1090]: (k7_relat_1(k7_relat_1(C_1088, A_1089), B_1090)=k7_relat_1(C_1088, k3_xboole_0(A_1089, B_1090)) | ~v1_relat_1(C_1088))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.63/8.03  tff(c_15266, plain, (![B_1090]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_1090))=k7_relat_1('#skF_5', B_1090) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1554, c_15248])).
% 16.63/8.03  tff(c_15275, plain, (![B_1090]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_1090))=k7_relat_1('#skF_5', B_1090))), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_15266])).
% 16.63/8.03  tff(c_15433, plain, (![A_1100, B_1101, C_1102, D_1103]: (k2_partfun1(A_1100, B_1101, C_1102, D_1103)=k7_relat_1(C_1102, D_1103) | ~m1_subset_1(C_1102, k1_zfmisc_1(k2_zfmisc_1(A_1100, B_1101))) | ~v1_funct_1(C_1102))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.63/8.03  tff(c_15435, plain, (![D_1103]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1103)=k7_relat_1('#skF_5', D_1103) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_15433])).
% 16.63/8.03  tff(c_15440, plain, (![D_1103]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1103)=k7_relat_1('#skF_5', D_1103))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_15435])).
% 16.63/8.03  tff(c_1613, plain, (![A_405, B_406, C_407]: (k9_subset_1(A_405, B_406, C_407)=k3_xboole_0(B_406, C_407) | ~m1_subset_1(C_407, k1_zfmisc_1(A_405)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.63/8.03  tff(c_1624, plain, (![B_406]: (k9_subset_1('#skF_1', B_406, '#skF_4')=k3_xboole_0(B_406, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_1613])).
% 16.63/8.03  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_105, plain, (![C_233, A_234, B_235]: (v1_relat_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.63/8.03  tff(c_113, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_105])).
% 16.63/8.03  tff(c_124, plain, (![C_241, A_242, B_243]: (v4_relat_1(C_241, A_242) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.63/8.03  tff(c_132, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_124])).
% 16.63/8.03  tff(c_240, plain, (![B_260, A_261]: (k1_relat_1(B_260)=A_261 | ~v1_partfun1(B_260, A_261) | ~v4_relat_1(B_260, A_261) | ~v1_relat_1(B_260))), inference(cnfTransformation, [status(thm)], [f_109])).
% 16.63/8.03  tff(c_243, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_132, c_240])).
% 16.63/8.03  tff(c_249, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_243])).
% 16.63/8.03  tff(c_253, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_249])).
% 16.63/8.03  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_814, plain, (![C_311, A_312, B_313]: (v1_partfun1(C_311, A_312) | ~v1_funct_2(C_311, A_312, B_313) | ~v1_funct_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))) | v1_xboole_0(B_313))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.63/8.03  tff(c_820, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_814])).
% 16.63/8.03  tff(c_827, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_820])).
% 16.63/8.03  tff(c_829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_253, c_827])).
% 16.63/8.03  tff(c_830, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_249])).
% 16.63/8.03  tff(c_838, plain, (![B_14]: (k7_relat_1('#skF_6', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_830, c_12])).
% 16.63/8.03  tff(c_1105, plain, (![B_339]: (k7_relat_1('#skF_6', B_339)=k1_xboole_0 | ~r1_xboole_0(B_339, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_838])).
% 16.63/8.03  tff(c_1109, plain, (![A_17]: (k7_relat_1('#skF_6', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_18, c_1105])).
% 16.63/8.03  tff(c_1305, plain, (![A_355]: (k7_relat_1('#skF_6', A_355)=k1_xboole_0 | ~r1_subset_1(A_355, '#skF_4') | v1_xboole_0(A_355))), inference(negUnitSimplification, [status(thm)], [c_68, c_1109])).
% 16.63/8.03  tff(c_1308, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1305])).
% 16.63/8.03  tff(c_1311, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_1308])).
% 16.63/8.03  tff(c_10, plain, (![C_11, A_9, B_10]: (k7_relat_1(k7_relat_1(C_11, A_9), B_10)=k7_relat_1(C_11, k3_xboole_0(A_9, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.63/8.03  tff(c_1318, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1311, c_10])).
% 16.63/8.03  tff(c_1326, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1318])).
% 16.63/8.03  tff(c_1269, plain, (![A_349, B_350, C_351, D_352]: (k2_partfun1(A_349, B_350, C_351, D_352)=k7_relat_1(C_351, D_352) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_349, B_350))) | ~v1_funct_1(C_351))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.63/8.03  tff(c_1273, plain, (![D_352]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_352)=k7_relat_1('#skF_6', D_352) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_1269])).
% 16.63/8.03  tff(c_1279, plain, (![D_352]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_352)=k7_relat_1('#skF_6', D_352))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1273])).
% 16.63/8.03  tff(c_179, plain, (![B_251, A_252]: (r1_subset_1(B_251, A_252) | ~r1_subset_1(A_252, B_251) | v1_xboole_0(B_251) | v1_xboole_0(A_252))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.63/8.03  tff(c_181, plain, (r1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_179])).
% 16.63/8.03  tff(c_184, plain, (r1_subset_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_181])).
% 16.63/8.03  tff(c_112, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_105])).
% 16.63/8.03  tff(c_131, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_124])).
% 16.63/8.03  tff(c_246, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_131, c_240])).
% 16.63/8.03  tff(c_252, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_246])).
% 16.63/8.03  tff(c_847, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_252])).
% 16.63/8.03  tff(c_1063, plain, (![C_335, A_336, B_337]: (v1_partfun1(C_335, A_336) | ~v1_funct_2(C_335, A_336, B_337) | ~v1_funct_1(C_335) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_336, B_337))) | v1_xboole_0(B_337))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.63/8.03  tff(c_1066, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_1063])).
% 16.63/8.03  tff(c_1072, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1066])).
% 16.63/8.03  tff(c_1074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_847, c_1072])).
% 16.63/8.03  tff(c_1075, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_252])).
% 16.63/8.03  tff(c_1083, plain, (![B_14]: (k7_relat_1('#skF_5', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1075, c_12])).
% 16.63/8.03  tff(c_1092, plain, (![B_338]: (k7_relat_1('#skF_5', B_338)=k1_xboole_0 | ~r1_xboole_0(B_338, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1083])).
% 16.63/8.03  tff(c_1096, plain, (![A_17]: (k7_relat_1('#skF_5', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_18, c_1092])).
% 16.63/8.03  tff(c_1224, plain, (![A_347]: (k7_relat_1('#skF_5', A_347)=k1_xboole_0 | ~r1_subset_1(A_347, '#skF_3') | v1_xboole_0(A_347))), inference(negUnitSimplification, [status(thm)], [c_72, c_1096])).
% 16.63/8.03  tff(c_1227, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_184, c_1224])).
% 16.63/8.03  tff(c_1230, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_1227])).
% 16.63/8.03  tff(c_14, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.63/8.03  tff(c_135, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_131, c_14])).
% 16.63/8.03  tff(c_138, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_135])).
% 16.63/8.03  tff(c_1134, plain, (![C_341, A_342, B_343]: (k7_relat_1(k7_relat_1(C_341, A_342), B_343)=k7_relat_1(C_341, k3_xboole_0(A_342, B_343)) | ~v1_relat_1(C_341))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.63/8.03  tff(c_1155, plain, (![B_343]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_343))=k7_relat_1('#skF_5', B_343) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_1134])).
% 16.63/8.03  tff(c_1163, plain, (![B_343]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_343))=k7_relat_1('#skF_5', B_343))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1155])).
% 16.63/8.03  tff(c_1271, plain, (![D_352]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_352)=k7_relat_1('#skF_5', D_352) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_1269])).
% 16.63/8.03  tff(c_1276, plain, (![D_352]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_352)=k7_relat_1('#skF_5', D_352))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1271])).
% 16.63/8.03  tff(c_190, plain, (![A_253, B_254, C_255]: (k9_subset_1(A_253, B_254, C_255)=k3_xboole_0(B_254, C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(A_253)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.63/8.03  tff(c_201, plain, (![B_254]: (k9_subset_1('#skF_1', B_254, '#skF_4')=k3_xboole_0(B_254, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_190])).
% 16.63/8.03  tff(c_50, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 16.63/8.03  tff(c_104, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_50])).
% 16.63/8.03  tff(c_203, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_201, c_104])).
% 16.63/8.03  tff(c_1280, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1276, c_203])).
% 16.63/8.03  tff(c_1281, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_1163, c_1280])).
% 16.63/8.03  tff(c_1300, plain, (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1279, c_1281])).
% 16.63/8.03  tff(c_1329, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1300])).
% 16.63/8.03  tff(c_153, plain, (![A_244, B_245]: (r1_xboole_0(A_244, B_245) | ~r1_subset_1(A_244, B_245) | v1_xboole_0(B_245) | v1_xboole_0(A_244))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.63/8.03  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.63/8.03  tff(c_1409, plain, (![A_374, B_375]: (k3_xboole_0(A_374, B_375)=k1_xboole_0 | ~r1_subset_1(A_374, B_375) | v1_xboole_0(B_375) | v1_xboole_0(A_374))), inference(resolution, [status(thm)], [c_153, c_2])).
% 16.63/8.03  tff(c_1415, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_184, c_1409])).
% 16.63/8.03  tff(c_1422, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_72, c_1415])).
% 16.63/8.03  tff(c_141, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_132, c_14])).
% 16.63/8.03  tff(c_144, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_141])).
% 16.63/8.03  tff(c_1152, plain, (![B_343]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', B_343))=k7_relat_1('#skF_6', B_343) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_1134])).
% 16.63/8.03  tff(c_1161, plain, (![B_343]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', B_343))=k7_relat_1('#skF_6', B_343))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1152])).
% 16.63/8.03  tff(c_1438, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1422, c_1161])).
% 16.63/8.03  tff(c_1442, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1311, c_1438])).
% 16.63/8.03  tff(c_1418, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1409])).
% 16.63/8.03  tff(c_1425, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_1418])).
% 16.63/8.03  tff(c_1454, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k7_relat_1('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1425, c_1326])).
% 16.63/8.03  tff(c_1520, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_1454])).
% 16.63/8.03  tff(c_1521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1329, c_1520])).
% 16.63/8.03  tff(c_1523, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 16.63/8.03  tff(c_1626, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1624, c_1523])).
% 16.63/8.03  tff(c_15444, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))=k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15440, c_1626])).
% 16.63/8.03  tff(c_15445, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15318, c_15275, c_15444])).
% 16.63/8.03  tff(c_15437, plain, (![D_1103]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1103)=k7_relat_1('#skF_6', D_1103) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_15433])).
% 16.63/8.03  tff(c_15443, plain, (![D_1103]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1103)=k7_relat_1('#skF_6', D_1103))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_15437])).
% 16.63/8.03  tff(c_15467, plain, (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15445, c_15443])).
% 16.63/8.03  tff(c_1532, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_1524])).
% 16.63/8.03  tff(c_1541, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1533])).
% 16.63/8.03  tff(c_1666, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1541, c_1663])).
% 16.63/8.03  tff(c_1672, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1666])).
% 16.63/8.03  tff(c_1676, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1672])).
% 16.63/8.03  tff(c_2259, plain, (![C_462, A_463, B_464]: (v1_partfun1(C_462, A_463) | ~v1_funct_2(C_462, A_463, B_464) | ~v1_funct_1(C_462) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_463, B_464))) | v1_xboole_0(B_464))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.63/8.03  tff(c_2265, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2259])).
% 16.63/8.03  tff(c_2272, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2265])).
% 16.63/8.03  tff(c_2274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1676, c_2272])).
% 16.63/8.03  tff(c_2275, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1672])).
% 16.63/8.03  tff(c_2283, plain, (![B_14]: (k7_relat_1('#skF_6', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2275, c_12])).
% 16.63/8.03  tff(c_15206, plain, (![B_1085]: (k7_relat_1('#skF_6', B_1085)=k1_xboole_0 | ~r1_xboole_0(B_1085, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_2283])).
% 16.63/8.03  tff(c_15210, plain, (![A_17]: (k7_relat_1('#skF_6', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_18, c_15206])).
% 16.63/8.03  tff(c_15387, plain, (![A_1096]: (k7_relat_1('#skF_6', A_1096)=k1_xboole_0 | ~r1_subset_1(A_1096, '#skF_4') | v1_xboole_0(A_1096))), inference(negUnitSimplification, [status(thm)], [c_68, c_15210])).
% 16.63/8.03  tff(c_15390, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_15387])).
% 16.63/8.03  tff(c_15393, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_15390])).
% 16.63/8.03  tff(c_15397, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_15393, c_10])).
% 16.63/8.03  tff(c_15407, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_15397])).
% 16.63/8.03  tff(c_15477, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15467, c_15407])).
% 16.63/8.03  tff(c_15615, plain, (![A_1115, C_1119, F_1118, D_1114, B_1116, E_1117]: (v1_funct_1(k1_tmap_1(A_1115, B_1116, C_1119, D_1114, E_1117, F_1118)) | ~m1_subset_1(F_1118, k1_zfmisc_1(k2_zfmisc_1(D_1114, B_1116))) | ~v1_funct_2(F_1118, D_1114, B_1116) | ~v1_funct_1(F_1118) | ~m1_subset_1(E_1117, k1_zfmisc_1(k2_zfmisc_1(C_1119, B_1116))) | ~v1_funct_2(E_1117, C_1119, B_1116) | ~v1_funct_1(E_1117) | ~m1_subset_1(D_1114, k1_zfmisc_1(A_1115)) | v1_xboole_0(D_1114) | ~m1_subset_1(C_1119, k1_zfmisc_1(A_1115)) | v1_xboole_0(C_1119) | v1_xboole_0(B_1116) | v1_xboole_0(A_1115))), inference(cnfTransformation, [status(thm)], [f_197])).
% 16.63/8.03  tff(c_15619, plain, (![A_1115, C_1119, E_1117]: (v1_funct_1(k1_tmap_1(A_1115, '#skF_2', C_1119, '#skF_4', E_1117, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1117, k1_zfmisc_1(k2_zfmisc_1(C_1119, '#skF_2'))) | ~v1_funct_2(E_1117, C_1119, '#skF_2') | ~v1_funct_1(E_1117) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1115)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1119, k1_zfmisc_1(A_1115)) | v1_xboole_0(C_1119) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1115))), inference(resolution, [status(thm)], [c_52, c_15615])).
% 16.63/8.03  tff(c_15626, plain, (![A_1115, C_1119, E_1117]: (v1_funct_1(k1_tmap_1(A_1115, '#skF_2', C_1119, '#skF_4', E_1117, '#skF_6')) | ~m1_subset_1(E_1117, k1_zfmisc_1(k2_zfmisc_1(C_1119, '#skF_2'))) | ~v1_funct_2(E_1117, C_1119, '#skF_2') | ~v1_funct_1(E_1117) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1115)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1119, k1_zfmisc_1(A_1115)) | v1_xboole_0(C_1119) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1115))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_15619])).
% 16.63/8.03  tff(c_16088, plain, (![A_1171, C_1172, E_1173]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', C_1172, '#skF_4', E_1173, '#skF_6')) | ~m1_subset_1(E_1173, k1_zfmisc_1(k2_zfmisc_1(C_1172, '#skF_2'))) | ~v1_funct_2(E_1173, C_1172, '#skF_2') | ~v1_funct_1(E_1173) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1(C_1172, k1_zfmisc_1(A_1171)) | v1_xboole_0(C_1172) | v1_xboole_0(A_1171))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_15626])).
% 16.63/8.03  tff(c_16093, plain, (![A_1171]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1171)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1171))), inference(resolution, [status(thm)], [c_58, c_16088])).
% 16.63/8.03  tff(c_16101, plain, (![A_1171]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1171)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1171))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_16093])).
% 16.63/8.03  tff(c_16273, plain, (![A_1194]: (v1_funct_1(k1_tmap_1(A_1194, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1194)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1194)) | v1_xboole_0(A_1194))), inference(negUnitSimplification, [status(thm)], [c_72, c_16101])).
% 16.63/8.03  tff(c_16276, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_16273])).
% 16.63/8.03  tff(c_16279, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16276])).
% 16.63/8.03  tff(c_16280, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_16279])).
% 16.63/8.03  tff(c_46, plain, (![C_166, D_167, E_168, A_164, B_165, F_169]: (v1_funct_2(k1_tmap_1(A_164, B_165, C_166, D_167, E_168, F_169), k4_subset_1(A_164, C_166, D_167), B_165) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(D_167, B_165))) | ~v1_funct_2(F_169, D_167, B_165) | ~v1_funct_1(F_169) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(C_166, B_165))) | ~v1_funct_2(E_168, C_166, B_165) | ~v1_funct_1(E_168) | ~m1_subset_1(D_167, k1_zfmisc_1(A_164)) | v1_xboole_0(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(A_164)) | v1_xboole_0(C_166) | v1_xboole_0(B_165) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_197])).
% 16.63/8.03  tff(c_44, plain, (![C_166, D_167, E_168, A_164, B_165, F_169]: (m1_subset_1(k1_tmap_1(A_164, B_165, C_166, D_167, E_168, F_169), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_164, C_166, D_167), B_165))) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(D_167, B_165))) | ~v1_funct_2(F_169, D_167, B_165) | ~v1_funct_1(F_169) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(C_166, B_165))) | ~v1_funct_2(E_168, C_166, B_165) | ~v1_funct_1(E_168) | ~m1_subset_1(D_167, k1_zfmisc_1(A_164)) | v1_xboole_0(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(A_164)) | v1_xboole_0(C_166) | v1_xboole_0(B_165) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_197])).
% 16.63/8.03  tff(c_16082, plain, (![A_1165, B_1168, E_1169, C_1166, F_1167, D_1170]: (k2_partfun1(k4_subset_1(A_1165, C_1166, D_1170), B_1168, k1_tmap_1(A_1165, B_1168, C_1166, D_1170, E_1169, F_1167), C_1166)=E_1169 | ~m1_subset_1(k1_tmap_1(A_1165, B_1168, C_1166, D_1170, E_1169, F_1167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1165, C_1166, D_1170), B_1168))) | ~v1_funct_2(k1_tmap_1(A_1165, B_1168, C_1166, D_1170, E_1169, F_1167), k4_subset_1(A_1165, C_1166, D_1170), B_1168) | ~v1_funct_1(k1_tmap_1(A_1165, B_1168, C_1166, D_1170, E_1169, F_1167)) | k2_partfun1(D_1170, B_1168, F_1167, k9_subset_1(A_1165, C_1166, D_1170))!=k2_partfun1(C_1166, B_1168, E_1169, k9_subset_1(A_1165, C_1166, D_1170)) | ~m1_subset_1(F_1167, k1_zfmisc_1(k2_zfmisc_1(D_1170, B_1168))) | ~v1_funct_2(F_1167, D_1170, B_1168) | ~v1_funct_1(F_1167) | ~m1_subset_1(E_1169, k1_zfmisc_1(k2_zfmisc_1(C_1166, B_1168))) | ~v1_funct_2(E_1169, C_1166, B_1168) | ~v1_funct_1(E_1169) | ~m1_subset_1(D_1170, k1_zfmisc_1(A_1165)) | v1_xboole_0(D_1170) | ~m1_subset_1(C_1166, k1_zfmisc_1(A_1165)) | v1_xboole_0(C_1166) | v1_xboole_0(B_1168) | v1_xboole_0(A_1165))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.63/8.03  tff(c_17762, plain, (![C_1358, A_1354, B_1355, E_1356, F_1357, D_1353]: (k2_partfun1(k4_subset_1(A_1354, C_1358, D_1353), B_1355, k1_tmap_1(A_1354, B_1355, C_1358, D_1353, E_1356, F_1357), C_1358)=E_1356 | ~v1_funct_2(k1_tmap_1(A_1354, B_1355, C_1358, D_1353, E_1356, F_1357), k4_subset_1(A_1354, C_1358, D_1353), B_1355) | ~v1_funct_1(k1_tmap_1(A_1354, B_1355, C_1358, D_1353, E_1356, F_1357)) | k2_partfun1(D_1353, B_1355, F_1357, k9_subset_1(A_1354, C_1358, D_1353))!=k2_partfun1(C_1358, B_1355, E_1356, k9_subset_1(A_1354, C_1358, D_1353)) | ~m1_subset_1(F_1357, k1_zfmisc_1(k2_zfmisc_1(D_1353, B_1355))) | ~v1_funct_2(F_1357, D_1353, B_1355) | ~v1_funct_1(F_1357) | ~m1_subset_1(E_1356, k1_zfmisc_1(k2_zfmisc_1(C_1358, B_1355))) | ~v1_funct_2(E_1356, C_1358, B_1355) | ~v1_funct_1(E_1356) | ~m1_subset_1(D_1353, k1_zfmisc_1(A_1354)) | v1_xboole_0(D_1353) | ~m1_subset_1(C_1358, k1_zfmisc_1(A_1354)) | v1_xboole_0(C_1358) | v1_xboole_0(B_1355) | v1_xboole_0(A_1354))), inference(resolution, [status(thm)], [c_44, c_16082])).
% 16.63/8.03  tff(c_22214, plain, (![B_1555, D_1553, C_1558, A_1554, F_1557, E_1556]: (k2_partfun1(k4_subset_1(A_1554, C_1558, D_1553), B_1555, k1_tmap_1(A_1554, B_1555, C_1558, D_1553, E_1556, F_1557), C_1558)=E_1556 | ~v1_funct_1(k1_tmap_1(A_1554, B_1555, C_1558, D_1553, E_1556, F_1557)) | k2_partfun1(D_1553, B_1555, F_1557, k9_subset_1(A_1554, C_1558, D_1553))!=k2_partfun1(C_1558, B_1555, E_1556, k9_subset_1(A_1554, C_1558, D_1553)) | ~m1_subset_1(F_1557, k1_zfmisc_1(k2_zfmisc_1(D_1553, B_1555))) | ~v1_funct_2(F_1557, D_1553, B_1555) | ~v1_funct_1(F_1557) | ~m1_subset_1(E_1556, k1_zfmisc_1(k2_zfmisc_1(C_1558, B_1555))) | ~v1_funct_2(E_1556, C_1558, B_1555) | ~v1_funct_1(E_1556) | ~m1_subset_1(D_1553, k1_zfmisc_1(A_1554)) | v1_xboole_0(D_1553) | ~m1_subset_1(C_1558, k1_zfmisc_1(A_1554)) | v1_xboole_0(C_1558) | v1_xboole_0(B_1555) | v1_xboole_0(A_1554))), inference(resolution, [status(thm)], [c_46, c_17762])).
% 16.63/8.03  tff(c_22220, plain, (![A_1554, C_1558, E_1556]: (k2_partfun1(k4_subset_1(A_1554, C_1558, '#skF_4'), '#skF_2', k1_tmap_1(A_1554, '#skF_2', C_1558, '#skF_4', E_1556, '#skF_6'), C_1558)=E_1556 | ~v1_funct_1(k1_tmap_1(A_1554, '#skF_2', C_1558, '#skF_4', E_1556, '#skF_6')) | k2_partfun1(C_1558, '#skF_2', E_1556, k9_subset_1(A_1554, C_1558, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1554, C_1558, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1556, k1_zfmisc_1(k2_zfmisc_1(C_1558, '#skF_2'))) | ~v1_funct_2(E_1556, C_1558, '#skF_2') | ~v1_funct_1(E_1556) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1554)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1558, k1_zfmisc_1(A_1554)) | v1_xboole_0(C_1558) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1554))), inference(resolution, [status(thm)], [c_52, c_22214])).
% 16.63/8.03  tff(c_22228, plain, (![A_1554, C_1558, E_1556]: (k2_partfun1(k4_subset_1(A_1554, C_1558, '#skF_4'), '#skF_2', k1_tmap_1(A_1554, '#skF_2', C_1558, '#skF_4', E_1556, '#skF_6'), C_1558)=E_1556 | ~v1_funct_1(k1_tmap_1(A_1554, '#skF_2', C_1558, '#skF_4', E_1556, '#skF_6')) | k2_partfun1(C_1558, '#skF_2', E_1556, k9_subset_1(A_1554, C_1558, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1554, C_1558, '#skF_4')) | ~m1_subset_1(E_1556, k1_zfmisc_1(k2_zfmisc_1(C_1558, '#skF_2'))) | ~v1_funct_2(E_1556, C_1558, '#skF_2') | ~v1_funct_1(E_1556) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1554)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1558, k1_zfmisc_1(A_1554)) | v1_xboole_0(C_1558) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1554))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_15443, c_22220])).
% 16.63/8.03  tff(c_29933, plain, (![A_1675, C_1676, E_1677]: (k2_partfun1(k4_subset_1(A_1675, C_1676, '#skF_4'), '#skF_2', k1_tmap_1(A_1675, '#skF_2', C_1676, '#skF_4', E_1677, '#skF_6'), C_1676)=E_1677 | ~v1_funct_1(k1_tmap_1(A_1675, '#skF_2', C_1676, '#skF_4', E_1677, '#skF_6')) | k2_partfun1(C_1676, '#skF_2', E_1677, k9_subset_1(A_1675, C_1676, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1675, C_1676, '#skF_4')) | ~m1_subset_1(E_1677, k1_zfmisc_1(k2_zfmisc_1(C_1676, '#skF_2'))) | ~v1_funct_2(E_1677, C_1676, '#skF_2') | ~v1_funct_1(E_1677) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1675)) | ~m1_subset_1(C_1676, k1_zfmisc_1(A_1675)) | v1_xboole_0(C_1676) | v1_xboole_0(A_1675))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_22228])).
% 16.63/8.03  tff(c_29938, plain, (![A_1675]: (k2_partfun1(k4_subset_1(A_1675, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1675, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1675, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1675, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1675, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1675)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1675)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1675))), inference(resolution, [status(thm)], [c_58, c_29933])).
% 16.63/8.03  tff(c_29946, plain, (![A_1675]: (k2_partfun1(k4_subset_1(A_1675, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1675, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1675, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1675, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1675, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1675)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1675)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1675))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_15440, c_29938])).
% 16.63/8.03  tff(c_30721, plain, (![A_1689]: (k2_partfun1(k4_subset_1(A_1689, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1689, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1689, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1689, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1689, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1689)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1689)) | v1_xboole_0(A_1689))), inference(negUnitSimplification, [status(thm)], [c_72, c_29946])).
% 16.63/8.03  tff(c_2293, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1675])).
% 16.63/8.03  tff(c_2615, plain, (![C_487, A_488, B_489]: (v1_partfun1(C_487, A_488) | ~v1_funct_2(C_487, A_488, B_489) | ~v1_funct_1(C_487) | ~m1_subset_1(C_487, k1_zfmisc_1(k2_zfmisc_1(A_488, B_489))) | v1_xboole_0(B_489))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.63/8.03  tff(c_2618, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_2615])).
% 16.63/8.03  tff(c_2624, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2618])).
% 16.63/8.03  tff(c_2626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_2293, c_2624])).
% 16.63/8.03  tff(c_2627, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1675])).
% 16.63/8.03  tff(c_2635, plain, (![B_14]: (k7_relat_1('#skF_5', B_14)=k1_xboole_0 | ~r1_xboole_0(B_14, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2627, c_12])).
% 16.63/8.03  tff(c_2661, plain, (![B_491]: (k7_relat_1('#skF_5', B_491)=k1_xboole_0 | ~r1_xboole_0(B_491, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_2635])).
% 16.63/8.03  tff(c_2665, plain, (![A_17]: (k7_relat_1('#skF_5', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_18, c_2661])).
% 16.63/8.03  tff(c_2825, plain, (![A_501]: (k7_relat_1('#skF_5', A_501)=k1_xboole_0 | ~r1_subset_1(A_501, '#skF_3') | v1_xboole_0(A_501))), inference(negUnitSimplification, [status(thm)], [c_72, c_2665])).
% 16.63/8.03  tff(c_2828, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1607, c_2825])).
% 16.63/8.03  tff(c_2831, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_2828])).
% 16.63/8.03  tff(c_2690, plain, (![C_493, A_494, B_495]: (k7_relat_1(k7_relat_1(C_493, A_494), B_495)=k7_relat_1(C_493, k3_xboole_0(A_494, B_495)) | ~v1_relat_1(C_493))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.63/8.03  tff(c_2708, plain, (![B_495]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_495))=k7_relat_1('#skF_5', B_495) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1554, c_2690])).
% 16.63/8.03  tff(c_2717, plain, (![B_495]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', B_495))=k7_relat_1('#skF_5', B_495))), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_2708])).
% 16.63/8.03  tff(c_2872, plain, (![A_506, B_507, C_508, D_509]: (k2_partfun1(A_506, B_507, C_508, D_509)=k7_relat_1(C_508, D_509) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_506, B_507))) | ~v1_funct_1(C_508))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.63/8.03  tff(c_2874, plain, (![D_509]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_509)=k7_relat_1('#skF_5', D_509) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_2872])).
% 16.63/8.03  tff(c_2879, plain, (![D_509]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_509)=k7_relat_1('#skF_5', D_509))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2874])).
% 16.63/8.03  tff(c_2883, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))=k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2879, c_1626])).
% 16.63/8.03  tff(c_2884, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2831, c_2717, c_2883])).
% 16.63/8.03  tff(c_2876, plain, (![D_509]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_509)=k7_relat_1('#skF_6', D_509) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_2872])).
% 16.63/8.03  tff(c_2882, plain, (![D_509]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_509)=k7_relat_1('#skF_6', D_509))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2876])).
% 16.63/8.03  tff(c_2906, plain, (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2884, c_2882])).
% 16.63/8.03  tff(c_2648, plain, (![B_490]: (k7_relat_1('#skF_6', B_490)=k1_xboole_0 | ~r1_xboole_0(B_490, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_2283])).
% 16.63/8.03  tff(c_2652, plain, (![A_17]: (k7_relat_1('#skF_6', A_17)=k1_xboole_0 | ~r1_subset_1(A_17, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_18, c_2648])).
% 16.63/8.03  tff(c_2754, plain, (![A_498]: (k7_relat_1('#skF_6', A_498)=k1_xboole_0 | ~r1_subset_1(A_498, '#skF_4') | v1_xboole_0(A_498))), inference(negUnitSimplification, [status(thm)], [c_68, c_2652])).
% 16.63/8.03  tff(c_2757, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2754])).
% 16.63/8.03  tff(c_2760, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_2757])).
% 16.63/8.03  tff(c_2764, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2760, c_10])).
% 16.63/8.03  tff(c_2774, plain, (![B_10]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_3', B_10))=k7_relat_1(k1_xboole_0, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_2764])).
% 16.63/8.03  tff(c_2916, plain, (k7_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2906, c_2774])).
% 16.63/8.03  tff(c_3073, plain, (![E_528, B_527, D_525, F_529, A_526, C_530]: (v1_funct_1(k1_tmap_1(A_526, B_527, C_530, D_525, E_528, F_529)) | ~m1_subset_1(F_529, k1_zfmisc_1(k2_zfmisc_1(D_525, B_527))) | ~v1_funct_2(F_529, D_525, B_527) | ~v1_funct_1(F_529) | ~m1_subset_1(E_528, k1_zfmisc_1(k2_zfmisc_1(C_530, B_527))) | ~v1_funct_2(E_528, C_530, B_527) | ~v1_funct_1(E_528) | ~m1_subset_1(D_525, k1_zfmisc_1(A_526)) | v1_xboole_0(D_525) | ~m1_subset_1(C_530, k1_zfmisc_1(A_526)) | v1_xboole_0(C_530) | v1_xboole_0(B_527) | v1_xboole_0(A_526))), inference(cnfTransformation, [status(thm)], [f_197])).
% 16.63/8.03  tff(c_3077, plain, (![A_526, C_530, E_528]: (v1_funct_1(k1_tmap_1(A_526, '#skF_2', C_530, '#skF_4', E_528, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_528, k1_zfmisc_1(k2_zfmisc_1(C_530, '#skF_2'))) | ~v1_funct_2(E_528, C_530, '#skF_2') | ~v1_funct_1(E_528) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_526)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_530, k1_zfmisc_1(A_526)) | v1_xboole_0(C_530) | v1_xboole_0('#skF_2') | v1_xboole_0(A_526))), inference(resolution, [status(thm)], [c_52, c_3073])).
% 16.63/8.03  tff(c_3084, plain, (![A_526, C_530, E_528]: (v1_funct_1(k1_tmap_1(A_526, '#skF_2', C_530, '#skF_4', E_528, '#skF_6')) | ~m1_subset_1(E_528, k1_zfmisc_1(k2_zfmisc_1(C_530, '#skF_2'))) | ~v1_funct_2(E_528, C_530, '#skF_2') | ~v1_funct_1(E_528) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_526)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_530, k1_zfmisc_1(A_526)) | v1_xboole_0(C_530) | v1_xboole_0('#skF_2') | v1_xboole_0(A_526))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3077])).
% 16.63/8.03  tff(c_3566, plain, (![A_578, C_579, E_580]: (v1_funct_1(k1_tmap_1(A_578, '#skF_2', C_579, '#skF_4', E_580, '#skF_6')) | ~m1_subset_1(E_580, k1_zfmisc_1(k2_zfmisc_1(C_579, '#skF_2'))) | ~v1_funct_2(E_580, C_579, '#skF_2') | ~v1_funct_1(E_580) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_578)) | ~m1_subset_1(C_579, k1_zfmisc_1(A_578)) | v1_xboole_0(C_579) | v1_xboole_0(A_578))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_3084])).
% 16.63/8.03  tff(c_3571, plain, (![A_578]: (v1_funct_1(k1_tmap_1(A_578, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_578)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_578)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_578))), inference(resolution, [status(thm)], [c_58, c_3566])).
% 16.63/8.03  tff(c_3579, plain, (![A_578]: (v1_funct_1(k1_tmap_1(A_578, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_578)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_578)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_578))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_3571])).
% 16.63/8.03  tff(c_3716, plain, (![A_599]: (v1_funct_1(k1_tmap_1(A_599, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_599)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_599)) | v1_xboole_0(A_599))), inference(negUnitSimplification, [status(thm)], [c_72, c_3579])).
% 16.63/8.03  tff(c_3719, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_3716])).
% 16.63/8.03  tff(c_3722, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3719])).
% 16.63/8.03  tff(c_3723, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_76, c_3722])).
% 16.63/8.03  tff(c_3352, plain, (![A_555, B_558, D_560, F_557, E_559, C_556]: (k2_partfun1(k4_subset_1(A_555, C_556, D_560), B_558, k1_tmap_1(A_555, B_558, C_556, D_560, E_559, F_557), D_560)=F_557 | ~m1_subset_1(k1_tmap_1(A_555, B_558, C_556, D_560, E_559, F_557), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_555, C_556, D_560), B_558))) | ~v1_funct_2(k1_tmap_1(A_555, B_558, C_556, D_560, E_559, F_557), k4_subset_1(A_555, C_556, D_560), B_558) | ~v1_funct_1(k1_tmap_1(A_555, B_558, C_556, D_560, E_559, F_557)) | k2_partfun1(D_560, B_558, F_557, k9_subset_1(A_555, C_556, D_560))!=k2_partfun1(C_556, B_558, E_559, k9_subset_1(A_555, C_556, D_560)) | ~m1_subset_1(F_557, k1_zfmisc_1(k2_zfmisc_1(D_560, B_558))) | ~v1_funct_2(F_557, D_560, B_558) | ~v1_funct_1(F_557) | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(C_556, B_558))) | ~v1_funct_2(E_559, C_556, B_558) | ~v1_funct_1(E_559) | ~m1_subset_1(D_560, k1_zfmisc_1(A_555)) | v1_xboole_0(D_560) | ~m1_subset_1(C_556, k1_zfmisc_1(A_555)) | v1_xboole_0(C_556) | v1_xboole_0(B_558) | v1_xboole_0(A_555))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.63/8.03  tff(c_5113, plain, (![B_747, D_745, A_746, F_749, E_748, C_750]: (k2_partfun1(k4_subset_1(A_746, C_750, D_745), B_747, k1_tmap_1(A_746, B_747, C_750, D_745, E_748, F_749), D_745)=F_749 | ~v1_funct_2(k1_tmap_1(A_746, B_747, C_750, D_745, E_748, F_749), k4_subset_1(A_746, C_750, D_745), B_747) | ~v1_funct_1(k1_tmap_1(A_746, B_747, C_750, D_745, E_748, F_749)) | k2_partfun1(D_745, B_747, F_749, k9_subset_1(A_746, C_750, D_745))!=k2_partfun1(C_750, B_747, E_748, k9_subset_1(A_746, C_750, D_745)) | ~m1_subset_1(F_749, k1_zfmisc_1(k2_zfmisc_1(D_745, B_747))) | ~v1_funct_2(F_749, D_745, B_747) | ~v1_funct_1(F_749) | ~m1_subset_1(E_748, k1_zfmisc_1(k2_zfmisc_1(C_750, B_747))) | ~v1_funct_2(E_748, C_750, B_747) | ~v1_funct_1(E_748) | ~m1_subset_1(D_745, k1_zfmisc_1(A_746)) | v1_xboole_0(D_745) | ~m1_subset_1(C_750, k1_zfmisc_1(A_746)) | v1_xboole_0(C_750) | v1_xboole_0(B_747) | v1_xboole_0(A_746))), inference(resolution, [status(thm)], [c_44, c_3352])).
% 16.63/8.03  tff(c_9734, plain, (![D_966, C_971, F_970, B_968, E_969, A_967]: (k2_partfun1(k4_subset_1(A_967, C_971, D_966), B_968, k1_tmap_1(A_967, B_968, C_971, D_966, E_969, F_970), D_966)=F_970 | ~v1_funct_1(k1_tmap_1(A_967, B_968, C_971, D_966, E_969, F_970)) | k2_partfun1(D_966, B_968, F_970, k9_subset_1(A_967, C_971, D_966))!=k2_partfun1(C_971, B_968, E_969, k9_subset_1(A_967, C_971, D_966)) | ~m1_subset_1(F_970, k1_zfmisc_1(k2_zfmisc_1(D_966, B_968))) | ~v1_funct_2(F_970, D_966, B_968) | ~v1_funct_1(F_970) | ~m1_subset_1(E_969, k1_zfmisc_1(k2_zfmisc_1(C_971, B_968))) | ~v1_funct_2(E_969, C_971, B_968) | ~v1_funct_1(E_969) | ~m1_subset_1(D_966, k1_zfmisc_1(A_967)) | v1_xboole_0(D_966) | ~m1_subset_1(C_971, k1_zfmisc_1(A_967)) | v1_xboole_0(C_971) | v1_xboole_0(B_968) | v1_xboole_0(A_967))), inference(resolution, [status(thm)], [c_46, c_5113])).
% 16.63/8.03  tff(c_9740, plain, (![A_967, C_971, E_969]: (k2_partfun1(k4_subset_1(A_967, C_971, '#skF_4'), '#skF_2', k1_tmap_1(A_967, '#skF_2', C_971, '#skF_4', E_969, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_967, '#skF_2', C_971, '#skF_4', E_969, '#skF_6')) | k2_partfun1(C_971, '#skF_2', E_969, k9_subset_1(A_967, C_971, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_967, C_971, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_969, k1_zfmisc_1(k2_zfmisc_1(C_971, '#skF_2'))) | ~v1_funct_2(E_969, C_971, '#skF_2') | ~v1_funct_1(E_969) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_967)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_971, k1_zfmisc_1(A_967)) | v1_xboole_0(C_971) | v1_xboole_0('#skF_2') | v1_xboole_0(A_967))), inference(resolution, [status(thm)], [c_52, c_9734])).
% 16.63/8.03  tff(c_9748, plain, (![A_967, C_971, E_969]: (k2_partfun1(k4_subset_1(A_967, C_971, '#skF_4'), '#skF_2', k1_tmap_1(A_967, '#skF_2', C_971, '#skF_4', E_969, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_967, '#skF_2', C_971, '#skF_4', E_969, '#skF_6')) | k2_partfun1(C_971, '#skF_2', E_969, k9_subset_1(A_967, C_971, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_967, C_971, '#skF_4')) | ~m1_subset_1(E_969, k1_zfmisc_1(k2_zfmisc_1(C_971, '#skF_2'))) | ~v1_funct_2(E_969, C_971, '#skF_2') | ~v1_funct_1(E_969) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_967)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_971, k1_zfmisc_1(A_967)) | v1_xboole_0(C_971) | v1_xboole_0('#skF_2') | v1_xboole_0(A_967))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2882, c_9740])).
% 16.63/8.03  tff(c_13607, plain, (![A_1043, C_1044, E_1045]: (k2_partfun1(k4_subset_1(A_1043, C_1044, '#skF_4'), '#skF_2', k1_tmap_1(A_1043, '#skF_2', C_1044, '#skF_4', E_1045, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1043, '#skF_2', C_1044, '#skF_4', E_1045, '#skF_6')) | k2_partfun1(C_1044, '#skF_2', E_1045, k9_subset_1(A_1043, C_1044, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1043, C_1044, '#skF_4')) | ~m1_subset_1(E_1045, k1_zfmisc_1(k2_zfmisc_1(C_1044, '#skF_2'))) | ~v1_funct_2(E_1045, C_1044, '#skF_2') | ~v1_funct_1(E_1045) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1043)) | ~m1_subset_1(C_1044, k1_zfmisc_1(A_1043)) | v1_xboole_0(C_1044) | v1_xboole_0(A_1043))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_9748])).
% 16.63/8.03  tff(c_13612, plain, (![A_1043]: (k2_partfun1(k4_subset_1(A_1043, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1043, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1043, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1043, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1043, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1043)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1043)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1043))), inference(resolution, [status(thm)], [c_58, c_13607])).
% 16.63/8.03  tff(c_13620, plain, (![A_1043]: (k2_partfun1(k4_subset_1(A_1043, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1043, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1043, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1043, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1043, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1043)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1043)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1043))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2879, c_13612])).
% 16.63/8.03  tff(c_14722, plain, (![A_1053]: (k2_partfun1(k4_subset_1(A_1053, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1053, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1053, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1053, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1053, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1053)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1053)) | v1_xboole_0(A_1053))), inference(negUnitSimplification, [status(thm)], [c_72, c_13620])).
% 16.63/8.03  tff(c_1522, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 16.63/8.03  tff(c_2292, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1522])).
% 16.63/8.03  tff(c_14733, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14722, c_2292])).
% 16.63/8.03  tff(c_14747, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2916, c_2831, c_2774, c_2717, c_1624, c_1624, c_3723, c_14733])).
% 16.63/8.03  tff(c_14749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_14747])).
% 16.63/8.03  tff(c_14750, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1522])).
% 16.63/8.03  tff(c_30730, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30721, c_14750])).
% 16.63/8.03  tff(c_30741, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_15477, c_15407, c_15318, c_15275, c_1624, c_1624, c_16280, c_30730])).
% 16.63/8.03  tff(c_30743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_30741])).
% 16.63/8.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.63/8.03  
% 16.63/8.03  Inference rules
% 16.63/8.03  ----------------------
% 16.63/8.03  #Ref     : 0
% 16.63/8.03  #Sup     : 7037
% 16.63/8.03  #Fact    : 0
% 16.63/8.03  #Define  : 0
% 16.63/8.03  #Split   : 46
% 16.63/8.03  #Chain   : 0
% 16.63/8.03  #Close   : 0
% 16.63/8.03  
% 16.63/8.03  Ordering : KBO
% 16.63/8.03  
% 16.63/8.03  Simplification rules
% 16.63/8.03  ----------------------
% 16.63/8.03  #Subsume      : 1805
% 16.63/8.03  #Demod        : 8477
% 16.63/8.03  #Tautology    : 1395
% 16.63/8.03  #SimpNegUnit  : 239
% 16.63/8.03  #BackRed      : 46
% 16.63/8.03  
% 16.63/8.03  #Partial instantiations: 0
% 16.63/8.03  #Strategies tried      : 1
% 16.63/8.03  
% 16.63/8.03  Timing (in seconds)
% 16.63/8.03  ----------------------
% 16.63/8.03  Preprocessing        : 0.44
% 16.63/8.03  Parsing              : 0.22
% 16.63/8.03  CNF conversion       : 0.06
% 16.63/8.03  Main loop            : 6.71
% 16.63/8.03  Inferencing          : 1.55
% 16.63/8.03  Reduction            : 3.10
% 16.63/8.03  Demodulation         : 2.56
% 16.63/8.04  BG Simplification    : 0.21
% 16.63/8.04  Subsumption          : 1.61
% 16.63/8.04  Abstraction          : 0.31
% 16.63/8.04  MUC search           : 0.00
% 16.63/8.04  Cooper               : 0.00
% 16.63/8.04  Total                : 7.24
% 16.63/8.04  Index Insertion      : 0.00
% 16.63/8.04  Index Deletion       : 0.00
% 16.63/8.04  Index Matching       : 0.00
% 16.63/8.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
