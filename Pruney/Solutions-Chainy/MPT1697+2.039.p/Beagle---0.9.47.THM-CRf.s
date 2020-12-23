%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:15 EST 2020

% Result     : Theorem 14.50s
% Output     : CNFRefutation 14.74s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 561 expanded)
%              Number of leaves         :   44 ( 224 expanded)
%              Depth                    :   12
%              Number of atoms          :  589 (2957 expanded)
%              Number of equality atoms :  117 ( 600 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k5_relset_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_xboole_0(B,C)
       => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_69,axiom,(
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

tff(f_33,axiom,(
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

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_899,plain,(
    ! [C_377,A_378,B_379] :
      ( v1_relat_1(C_377)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_378,B_379))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_912,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_899])).

tff(c_14,plain,(
    ! [A_13] : k9_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5327,plain,(
    ! [B_1118,A_1119] :
      ( r1_xboole_0(k1_relat_1(B_1118),A_1119)
      | k9_relat_1(B_1118,A_1119) != k1_xboole_0
      | ~ v1_relat_1(B_1118) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5339,plain,(
    ! [A_1119] :
      ( r1_xboole_0(k1_xboole_0,A_1119)
      | k9_relat_1(k1_xboole_0,A_1119) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5327])).

tff(c_5344,plain,(
    ! [A_1119] : r1_xboole_0(k1_xboole_0,A_1119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_14,c_5339])).

tff(c_5511,plain,(
    ! [C_1148,A_1149,D_1150,B_1151] :
      ( k5_relset_1(C_1148,A_1149,D_1150,B_1151) = k1_xboole_0
      | ~ r1_xboole_0(B_1151,C_1148)
      | ~ m1_subset_1(D_1150,k1_zfmisc_1(k2_zfmisc_1(C_1148,A_1149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7812,plain,(
    ! [A_1512,A_1513,D_1514] :
      ( k5_relset_1(A_1512,A_1513,D_1514,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(D_1514,k1_zfmisc_1(k2_zfmisc_1(A_1512,A_1513))) ) ),
    inference(resolution,[status(thm)],[c_5344,c_5511])).

tff(c_7824,plain,(
    k5_relset_1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_7812])).

tff(c_5447,plain,(
    ! [A_1135,B_1136,C_1137,D_1138] :
      ( k5_relset_1(A_1135,B_1136,C_1137,D_1138) = k7_relat_1(C_1137,D_1138)
      | ~ m1_subset_1(C_1137,k1_zfmisc_1(k2_zfmisc_1(A_1135,B_1136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5456,plain,(
    ! [D_1138] : k5_relset_1('#skF_3','#skF_2','#skF_5',D_1138) = k7_relat_1('#skF_5',D_1138) ),
    inference(resolution,[status(thm)],[c_56,c_5447])).

tff(c_7839,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7824,c_5456])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_7823,plain,(
    k5_relset_1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_7812])).

tff(c_5455,plain,(
    ! [D_1138] : k5_relset_1('#skF_4','#skF_2','#skF_6',D_1138) = k7_relat_1('#skF_6',D_1138) ),
    inference(resolution,[status(thm)],[c_50,c_5447])).

tff(c_7829,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7823,c_5455])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_62,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_5276,plain,(
    ! [A_1103,B_1104] :
      ( r1_xboole_0(A_1103,B_1104)
      | ~ r1_subset_1(A_1103,B_1104)
      | v1_xboole_0(B_1104)
      | v1_xboole_0(A_1103) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5490,plain,(
    ! [A_1144,B_1145] :
      ( k3_xboole_0(A_1144,B_1145) = k1_xboole_0
      | ~ r1_subset_1(A_1144,B_1145)
      | v1_xboole_0(B_1145)
      | v1_xboole_0(A_1144) ) ),
    inference(resolution,[status(thm)],[c_5276,c_2])).

tff(c_5493,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_5490])).

tff(c_5496,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_5493])).

tff(c_5345,plain,(
    ! [A_1120,B_1121,C_1122] :
      ( k9_subset_1(A_1120,B_1121,C_1122) = k3_xboole_0(B_1121,C_1122)
      | ~ m1_subset_1(C_1122,k1_zfmisc_1(A_1120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5359,plain,(
    ! [B_1121] : k9_subset_1('#skF_1',B_1121,'#skF_4') = k3_xboole_0(B_1121,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_5345])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_7975,plain,(
    ! [C_1527,D_1529,A_1531,B_1528,E_1530,F_1532] :
      ( v1_funct_1(k1_tmap_1(A_1531,B_1528,C_1527,D_1529,E_1530,F_1532))
      | ~ m1_subset_1(F_1532,k1_zfmisc_1(k2_zfmisc_1(D_1529,B_1528)))
      | ~ v1_funct_2(F_1532,D_1529,B_1528)
      | ~ v1_funct_1(F_1532)
      | ~ m1_subset_1(E_1530,k1_zfmisc_1(k2_zfmisc_1(C_1527,B_1528)))
      | ~ v1_funct_2(E_1530,C_1527,B_1528)
      | ~ v1_funct_1(E_1530)
      | ~ m1_subset_1(D_1529,k1_zfmisc_1(A_1531))
      | v1_xboole_0(D_1529)
      | ~ m1_subset_1(C_1527,k1_zfmisc_1(A_1531))
      | v1_xboole_0(C_1527)
      | v1_xboole_0(B_1528)
      | v1_xboole_0(A_1531) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_7977,plain,(
    ! [A_1531,C_1527,E_1530] :
      ( v1_funct_1(k1_tmap_1(A_1531,'#skF_2',C_1527,'#skF_4',E_1530,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1530,k1_zfmisc_1(k2_zfmisc_1(C_1527,'#skF_2')))
      | ~ v1_funct_2(E_1530,C_1527,'#skF_2')
      | ~ v1_funct_1(E_1530)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1531))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1527,k1_zfmisc_1(A_1531))
      | v1_xboole_0(C_1527)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1531) ) ),
    inference(resolution,[status(thm)],[c_50,c_7975])).

tff(c_7985,plain,(
    ! [A_1531,C_1527,E_1530] :
      ( v1_funct_1(k1_tmap_1(A_1531,'#skF_2',C_1527,'#skF_4',E_1530,'#skF_6'))
      | ~ m1_subset_1(E_1530,k1_zfmisc_1(k2_zfmisc_1(C_1527,'#skF_2')))
      | ~ v1_funct_2(E_1530,C_1527,'#skF_2')
      | ~ v1_funct_1(E_1530)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1531))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1527,k1_zfmisc_1(A_1531))
      | v1_xboole_0(C_1527)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1531) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_7977])).

tff(c_8240,plain,(
    ! [A_1570,C_1571,E_1572] :
      ( v1_funct_1(k1_tmap_1(A_1570,'#skF_2',C_1571,'#skF_4',E_1572,'#skF_6'))
      | ~ m1_subset_1(E_1572,k1_zfmisc_1(k2_zfmisc_1(C_1571,'#skF_2')))
      | ~ v1_funct_2(E_1572,C_1571,'#skF_2')
      | ~ v1_funct_1(E_1572)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1570))
      | ~ m1_subset_1(C_1571,k1_zfmisc_1(A_1570))
      | v1_xboole_0(C_1571)
      | v1_xboole_0(A_1570) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_7985])).

tff(c_8247,plain,(
    ! [A_1570] :
      ( v1_funct_1(k1_tmap_1(A_1570,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1570))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1570))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1570) ) ),
    inference(resolution,[status(thm)],[c_56,c_8240])).

tff(c_8260,plain,(
    ! [A_1570] :
      ( v1_funct_1(k1_tmap_1(A_1570,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1570))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1570))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1570) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_8247])).

tff(c_8270,plain,(
    ! [A_1574] :
      ( v1_funct_1(k1_tmap_1(A_1574,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1574))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1574))
      | v1_xboole_0(A_1574) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8260])).

tff(c_8273,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_8270])).

tff(c_8276,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8273])).

tff(c_8277,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8276])).

tff(c_5524,plain,(
    ! [A_1152,B_1153,C_1154,D_1155] :
      ( k2_partfun1(A_1152,B_1153,C_1154,D_1155) = k7_relat_1(C_1154,D_1155)
      | ~ m1_subset_1(C_1154,k1_zfmisc_1(k2_zfmisc_1(A_1152,B_1153)))
      | ~ v1_funct_1(C_1154) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5528,plain,(
    ! [D_1155] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1155) = k7_relat_1('#skF_5',D_1155)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_5524])).

tff(c_5537,plain,(
    ! [D_1155] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1155) = k7_relat_1('#skF_5',D_1155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5528])).

tff(c_5526,plain,(
    ! [D_1155] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1155) = k7_relat_1('#skF_6',D_1155)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_5524])).

tff(c_5534,plain,(
    ! [D_1155] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1155) = k7_relat_1('#skF_6',D_1155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5526])).

tff(c_44,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_42,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_8328,plain,(
    ! [B_1587,E_1586,A_1585,D_1590,F_1588,C_1589] :
      ( k2_partfun1(k4_subset_1(A_1585,C_1589,D_1590),B_1587,k1_tmap_1(A_1585,B_1587,C_1589,D_1590,E_1586,F_1588),C_1589) = E_1586
      | ~ m1_subset_1(k1_tmap_1(A_1585,B_1587,C_1589,D_1590,E_1586,F_1588),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1585,C_1589,D_1590),B_1587)))
      | ~ v1_funct_2(k1_tmap_1(A_1585,B_1587,C_1589,D_1590,E_1586,F_1588),k4_subset_1(A_1585,C_1589,D_1590),B_1587)
      | ~ v1_funct_1(k1_tmap_1(A_1585,B_1587,C_1589,D_1590,E_1586,F_1588))
      | k2_partfun1(D_1590,B_1587,F_1588,k9_subset_1(A_1585,C_1589,D_1590)) != k2_partfun1(C_1589,B_1587,E_1586,k9_subset_1(A_1585,C_1589,D_1590))
      | ~ m1_subset_1(F_1588,k1_zfmisc_1(k2_zfmisc_1(D_1590,B_1587)))
      | ~ v1_funct_2(F_1588,D_1590,B_1587)
      | ~ v1_funct_1(F_1588)
      | ~ m1_subset_1(E_1586,k1_zfmisc_1(k2_zfmisc_1(C_1589,B_1587)))
      | ~ v1_funct_2(E_1586,C_1589,B_1587)
      | ~ v1_funct_1(E_1586)
      | ~ m1_subset_1(D_1590,k1_zfmisc_1(A_1585))
      | v1_xboole_0(D_1590)
      | ~ m1_subset_1(C_1589,k1_zfmisc_1(A_1585))
      | v1_xboole_0(C_1589)
      | v1_xboole_0(B_1587)
      | v1_xboole_0(A_1585) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_8903,plain,(
    ! [F_1711,C_1706,E_1709,D_1708,A_1710,B_1707] :
      ( k2_partfun1(k4_subset_1(A_1710,C_1706,D_1708),B_1707,k1_tmap_1(A_1710,B_1707,C_1706,D_1708,E_1709,F_1711),C_1706) = E_1709
      | ~ v1_funct_2(k1_tmap_1(A_1710,B_1707,C_1706,D_1708,E_1709,F_1711),k4_subset_1(A_1710,C_1706,D_1708),B_1707)
      | ~ v1_funct_1(k1_tmap_1(A_1710,B_1707,C_1706,D_1708,E_1709,F_1711))
      | k2_partfun1(D_1708,B_1707,F_1711,k9_subset_1(A_1710,C_1706,D_1708)) != k2_partfun1(C_1706,B_1707,E_1709,k9_subset_1(A_1710,C_1706,D_1708))
      | ~ m1_subset_1(F_1711,k1_zfmisc_1(k2_zfmisc_1(D_1708,B_1707)))
      | ~ v1_funct_2(F_1711,D_1708,B_1707)
      | ~ v1_funct_1(F_1711)
      | ~ m1_subset_1(E_1709,k1_zfmisc_1(k2_zfmisc_1(C_1706,B_1707)))
      | ~ v1_funct_2(E_1709,C_1706,B_1707)
      | ~ v1_funct_1(E_1709)
      | ~ m1_subset_1(D_1708,k1_zfmisc_1(A_1710))
      | v1_xboole_0(D_1708)
      | ~ m1_subset_1(C_1706,k1_zfmisc_1(A_1710))
      | v1_xboole_0(C_1706)
      | v1_xboole_0(B_1707)
      | v1_xboole_0(A_1710) ) ),
    inference(resolution,[status(thm)],[c_42,c_8328])).

tff(c_9434,plain,(
    ! [B_1777,E_1779,D_1778,C_1776,F_1781,A_1780] :
      ( k2_partfun1(k4_subset_1(A_1780,C_1776,D_1778),B_1777,k1_tmap_1(A_1780,B_1777,C_1776,D_1778,E_1779,F_1781),C_1776) = E_1779
      | ~ v1_funct_1(k1_tmap_1(A_1780,B_1777,C_1776,D_1778,E_1779,F_1781))
      | k2_partfun1(D_1778,B_1777,F_1781,k9_subset_1(A_1780,C_1776,D_1778)) != k2_partfun1(C_1776,B_1777,E_1779,k9_subset_1(A_1780,C_1776,D_1778))
      | ~ m1_subset_1(F_1781,k1_zfmisc_1(k2_zfmisc_1(D_1778,B_1777)))
      | ~ v1_funct_2(F_1781,D_1778,B_1777)
      | ~ v1_funct_1(F_1781)
      | ~ m1_subset_1(E_1779,k1_zfmisc_1(k2_zfmisc_1(C_1776,B_1777)))
      | ~ v1_funct_2(E_1779,C_1776,B_1777)
      | ~ v1_funct_1(E_1779)
      | ~ m1_subset_1(D_1778,k1_zfmisc_1(A_1780))
      | v1_xboole_0(D_1778)
      | ~ m1_subset_1(C_1776,k1_zfmisc_1(A_1780))
      | v1_xboole_0(C_1776)
      | v1_xboole_0(B_1777)
      | v1_xboole_0(A_1780) ) ),
    inference(resolution,[status(thm)],[c_44,c_8903])).

tff(c_9438,plain,(
    ! [A_1780,C_1776,E_1779] :
      ( k2_partfun1(k4_subset_1(A_1780,C_1776,'#skF_4'),'#skF_2',k1_tmap_1(A_1780,'#skF_2',C_1776,'#skF_4',E_1779,'#skF_6'),C_1776) = E_1779
      | ~ v1_funct_1(k1_tmap_1(A_1780,'#skF_2',C_1776,'#skF_4',E_1779,'#skF_6'))
      | k2_partfun1(C_1776,'#skF_2',E_1779,k9_subset_1(A_1780,C_1776,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1780,C_1776,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1779,k1_zfmisc_1(k2_zfmisc_1(C_1776,'#skF_2')))
      | ~ v1_funct_2(E_1779,C_1776,'#skF_2')
      | ~ v1_funct_1(E_1779)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1780))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1776,k1_zfmisc_1(A_1780))
      | v1_xboole_0(C_1776)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1780) ) ),
    inference(resolution,[status(thm)],[c_50,c_9434])).

tff(c_9447,plain,(
    ! [A_1780,C_1776,E_1779] :
      ( k2_partfun1(k4_subset_1(A_1780,C_1776,'#skF_4'),'#skF_2',k1_tmap_1(A_1780,'#skF_2',C_1776,'#skF_4',E_1779,'#skF_6'),C_1776) = E_1779
      | ~ v1_funct_1(k1_tmap_1(A_1780,'#skF_2',C_1776,'#skF_4',E_1779,'#skF_6'))
      | k2_partfun1(C_1776,'#skF_2',E_1779,k9_subset_1(A_1780,C_1776,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1780,C_1776,'#skF_4'))
      | ~ m1_subset_1(E_1779,k1_zfmisc_1(k2_zfmisc_1(C_1776,'#skF_2')))
      | ~ v1_funct_2(E_1779,C_1776,'#skF_2')
      | ~ v1_funct_1(E_1779)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1780))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1776,k1_zfmisc_1(A_1780))
      | v1_xboole_0(C_1776)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1780) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5534,c_9438])).

tff(c_9870,plain,(
    ! [A_1825,C_1826,E_1827] :
      ( k2_partfun1(k4_subset_1(A_1825,C_1826,'#skF_4'),'#skF_2',k1_tmap_1(A_1825,'#skF_2',C_1826,'#skF_4',E_1827,'#skF_6'),C_1826) = E_1827
      | ~ v1_funct_1(k1_tmap_1(A_1825,'#skF_2',C_1826,'#skF_4',E_1827,'#skF_6'))
      | k2_partfun1(C_1826,'#skF_2',E_1827,k9_subset_1(A_1825,C_1826,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1825,C_1826,'#skF_4'))
      | ~ m1_subset_1(E_1827,k1_zfmisc_1(k2_zfmisc_1(C_1826,'#skF_2')))
      | ~ v1_funct_2(E_1827,C_1826,'#skF_2')
      | ~ v1_funct_1(E_1827)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1825))
      | ~ m1_subset_1(C_1826,k1_zfmisc_1(A_1825))
      | v1_xboole_0(C_1826)
      | v1_xboole_0(A_1825) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_9447])).

tff(c_9877,plain,(
    ! [A_1825] :
      ( k2_partfun1(k4_subset_1(A_1825,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1825,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1825,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1825,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1825,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1825))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1825))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1825) ) ),
    inference(resolution,[status(thm)],[c_56,c_9870])).

tff(c_9890,plain,(
    ! [A_1825] :
      ( k2_partfun1(k4_subset_1(A_1825,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1825,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1825,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1825,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1825,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1825))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1825))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1825) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5537,c_9877])).

tff(c_9893,plain,(
    ! [A_1828] :
      ( k2_partfun1(k4_subset_1(A_1828,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1828,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1828,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1828,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1828,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1828))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1828))
      | v1_xboole_0(A_1828) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_9890])).

tff(c_5575,plain,(
    ! [A_1158,A_1159,D_1160] :
      ( k5_relset_1(A_1158,A_1159,D_1160,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(D_1160,k1_zfmisc_1(k2_zfmisc_1(A_1158,A_1159))) ) ),
    inference(resolution,[status(thm)],[c_5344,c_5511])).

tff(c_5586,plain,(
    k5_relset_1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_5575])).

tff(c_5592,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5586,c_5455])).

tff(c_522,plain,(
    ! [C_312,A_313,B_314] :
      ( v1_relat_1(C_312)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_535,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_522])).

tff(c_541,plain,(
    ! [B_317,A_318] :
      ( r1_xboole_0(k1_relat_1(B_317),A_318)
      | k9_relat_1(B_317,A_318) != k1_xboole_0
      | ~ v1_relat_1(B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_547,plain,(
    ! [A_318] :
      ( r1_xboole_0(k1_xboole_0,A_318)
      | k9_relat_1(k1_xboole_0,A_318) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_541])).

tff(c_550,plain,(
    ! [A_318] : r1_xboole_0(k1_xboole_0,A_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_14,c_547])).

tff(c_738,plain,(
    ! [C_356,A_357,D_358,B_359] :
      ( k5_relset_1(C_356,A_357,D_358,B_359) = k1_xboole_0
      | ~ r1_xboole_0(B_359,C_356)
      | ~ m1_subset_1(D_358,k1_zfmisc_1(k2_zfmisc_1(C_356,A_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_775,plain,(
    ! [A_364,A_365,D_366] :
      ( k5_relset_1(A_364,A_365,D_366,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(D_366,k1_zfmisc_1(k2_zfmisc_1(A_364,A_365))) ) ),
    inference(resolution,[status(thm)],[c_550,c_738])).

tff(c_787,plain,(
    k5_relset_1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_775])).

tff(c_657,plain,(
    ! [A_340,B_341,C_342,D_343] :
      ( k5_relset_1(A_340,B_341,C_342,D_343) = k7_relat_1(C_342,D_343)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_666,plain,(
    ! [D_343] : k5_relset_1('#skF_3','#skF_2','#skF_5',D_343) = k7_relat_1('#skF_5',D_343) ),
    inference(resolution,[status(thm)],[c_56,c_657])).

tff(c_807,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_666])).

tff(c_819,plain,(
    ! [A_367,B_368,C_369,D_370] :
      ( k2_partfun1(A_367,B_368,C_369,D_370) = k7_relat_1(C_369,D_370)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368)))
      | ~ v1_funct_1(C_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_823,plain,(
    ! [D_370] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_370) = k7_relat_1('#skF_5',D_370)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_819])).

tff(c_832,plain,(
    ! [D_370] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_370) = k7_relat_1('#skF_5',D_370) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_823])).

tff(c_786,plain,(
    k5_relset_1('#skF_4','#skF_2','#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_775])).

tff(c_665,plain,(
    ! [D_343] : k5_relset_1('#skF_4','#skF_2','#skF_6',D_343) = k7_relat_1('#skF_6',D_343) ),
    inference(resolution,[status(thm)],[c_50,c_657])).

tff(c_792,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_665])).

tff(c_821,plain,(
    ! [D_370] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_370) = k7_relat_1('#skF_6',D_370)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_819])).

tff(c_829,plain,(
    ! [D_370] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_370) = k7_relat_1('#skF_6',D_370) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_821])).

tff(c_536,plain,(
    ! [A_315,B_316] :
      ( r1_xboole_0(A_315,B_316)
      | ~ r1_subset_1(A_315,B_316)
      | v1_xboole_0(B_316)
      | v1_xboole_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_722,plain,(
    ! [A_352,B_353] :
      ( k3_xboole_0(A_352,B_353) = k1_xboole_0
      | ~ r1_subset_1(A_352,B_353)
      | v1_xboole_0(B_353)
      | v1_xboole_0(A_352) ) ),
    inference(resolution,[status(thm)],[c_536,c_2])).

tff(c_725,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_722])).

tff(c_728,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_725])).

tff(c_622,plain,(
    ! [A_334,B_335,C_336] :
      ( k9_subset_1(A_334,B_335,C_336) = k3_xboole_0(B_335,C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(A_334)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_636,plain,(
    ! [B_335] : k9_subset_1('#skF_1',B_335,'#skF_4') = k3_xboole_0(B_335,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_622])).

tff(c_48,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_97,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_647,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_636,c_97])).

tff(c_873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_832,c_792,c_829,c_728,c_728,c_647])).

tff(c_875,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5485,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5359,c_5359,c_875])).

tff(c_5497,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5496,c_5496,c_5485])).

tff(c_5539,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5534,c_5497])).

tff(c_5561,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5539,c_5537])).

tff(c_5599,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5592,c_5561])).

tff(c_5640,plain,(
    ! [E_1166,B_1164,F_1168,D_1165,C_1163,A_1167] :
      ( v1_funct_1(k1_tmap_1(A_1167,B_1164,C_1163,D_1165,E_1166,F_1168))
      | ~ m1_subset_1(F_1168,k1_zfmisc_1(k2_zfmisc_1(D_1165,B_1164)))
      | ~ v1_funct_2(F_1168,D_1165,B_1164)
      | ~ v1_funct_1(F_1168)
      | ~ m1_subset_1(E_1166,k1_zfmisc_1(k2_zfmisc_1(C_1163,B_1164)))
      | ~ v1_funct_2(E_1166,C_1163,B_1164)
      | ~ v1_funct_1(E_1166)
      | ~ m1_subset_1(D_1165,k1_zfmisc_1(A_1167))
      | v1_xboole_0(D_1165)
      | ~ m1_subset_1(C_1163,k1_zfmisc_1(A_1167))
      | v1_xboole_0(C_1163)
      | v1_xboole_0(B_1164)
      | v1_xboole_0(A_1167) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_5642,plain,(
    ! [A_1167,C_1163,E_1166] :
      ( v1_funct_1(k1_tmap_1(A_1167,'#skF_2',C_1163,'#skF_4',E_1166,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1166,k1_zfmisc_1(k2_zfmisc_1(C_1163,'#skF_2')))
      | ~ v1_funct_2(E_1166,C_1163,'#skF_2')
      | ~ v1_funct_1(E_1166)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1167))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1163,k1_zfmisc_1(A_1167))
      | v1_xboole_0(C_1163)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1167) ) ),
    inference(resolution,[status(thm)],[c_50,c_5640])).

tff(c_5650,plain,(
    ! [A_1167,C_1163,E_1166] :
      ( v1_funct_1(k1_tmap_1(A_1167,'#skF_2',C_1163,'#skF_4',E_1166,'#skF_6'))
      | ~ m1_subset_1(E_1166,k1_zfmisc_1(k2_zfmisc_1(C_1163,'#skF_2')))
      | ~ v1_funct_2(E_1166,C_1163,'#skF_2')
      | ~ v1_funct_1(E_1166)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1167))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1163,k1_zfmisc_1(A_1167))
      | v1_xboole_0(C_1163)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5642])).

tff(c_5681,plain,(
    ! [A_1171,C_1172,E_1173] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2',C_1172,'#skF_4',E_1173,'#skF_6'))
      | ~ m1_subset_1(E_1173,k1_zfmisc_1(k2_zfmisc_1(C_1172,'#skF_2')))
      | ~ v1_funct_2(E_1173,C_1172,'#skF_2')
      | ~ v1_funct_1(E_1173)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1(C_1172,k1_zfmisc_1(A_1171))
      | v1_xboole_0(C_1172)
      | v1_xboole_0(A_1171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_5650])).

tff(c_5685,plain,(
    ! [A_1171] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1171))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1171) ) ),
    inference(resolution,[status(thm)],[c_56,c_5681])).

tff(c_5695,plain,(
    ! [A_1171] :
      ( v1_funct_1(k1_tmap_1(A_1171,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1171))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5685])).

tff(c_5791,plain,(
    ! [A_1191] :
      ( v1_funct_1(k1_tmap_1(A_1191,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1191))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1191))
      | v1_xboole_0(A_1191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5695])).

tff(c_5794,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_5791])).

tff(c_5797,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5794])).

tff(c_5798,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5797])).

tff(c_6029,plain,(
    ! [F_1223,A_1220,B_1222,E_1221,D_1225,C_1224] :
      ( k2_partfun1(k4_subset_1(A_1220,C_1224,D_1225),B_1222,k1_tmap_1(A_1220,B_1222,C_1224,D_1225,E_1221,F_1223),D_1225) = F_1223
      | ~ m1_subset_1(k1_tmap_1(A_1220,B_1222,C_1224,D_1225,E_1221,F_1223),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1220,C_1224,D_1225),B_1222)))
      | ~ v1_funct_2(k1_tmap_1(A_1220,B_1222,C_1224,D_1225,E_1221,F_1223),k4_subset_1(A_1220,C_1224,D_1225),B_1222)
      | ~ v1_funct_1(k1_tmap_1(A_1220,B_1222,C_1224,D_1225,E_1221,F_1223))
      | k2_partfun1(D_1225,B_1222,F_1223,k9_subset_1(A_1220,C_1224,D_1225)) != k2_partfun1(C_1224,B_1222,E_1221,k9_subset_1(A_1220,C_1224,D_1225))
      | ~ m1_subset_1(F_1223,k1_zfmisc_1(k2_zfmisc_1(D_1225,B_1222)))
      | ~ v1_funct_2(F_1223,D_1225,B_1222)
      | ~ v1_funct_1(F_1223)
      | ~ m1_subset_1(E_1221,k1_zfmisc_1(k2_zfmisc_1(C_1224,B_1222)))
      | ~ v1_funct_2(E_1221,C_1224,B_1222)
      | ~ v1_funct_1(E_1221)
      | ~ m1_subset_1(D_1225,k1_zfmisc_1(A_1220))
      | v1_xboole_0(D_1225)
      | ~ m1_subset_1(C_1224,k1_zfmisc_1(A_1220))
      | v1_xboole_0(C_1224)
      | v1_xboole_0(B_1222)
      | v1_xboole_0(A_1220) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6701,plain,(
    ! [F_1366,E_1364,A_1365,B_1362,D_1363,C_1361] :
      ( k2_partfun1(k4_subset_1(A_1365,C_1361,D_1363),B_1362,k1_tmap_1(A_1365,B_1362,C_1361,D_1363,E_1364,F_1366),D_1363) = F_1366
      | ~ v1_funct_2(k1_tmap_1(A_1365,B_1362,C_1361,D_1363,E_1364,F_1366),k4_subset_1(A_1365,C_1361,D_1363),B_1362)
      | ~ v1_funct_1(k1_tmap_1(A_1365,B_1362,C_1361,D_1363,E_1364,F_1366))
      | k2_partfun1(D_1363,B_1362,F_1366,k9_subset_1(A_1365,C_1361,D_1363)) != k2_partfun1(C_1361,B_1362,E_1364,k9_subset_1(A_1365,C_1361,D_1363))
      | ~ m1_subset_1(F_1366,k1_zfmisc_1(k2_zfmisc_1(D_1363,B_1362)))
      | ~ v1_funct_2(F_1366,D_1363,B_1362)
      | ~ v1_funct_1(F_1366)
      | ~ m1_subset_1(E_1364,k1_zfmisc_1(k2_zfmisc_1(C_1361,B_1362)))
      | ~ v1_funct_2(E_1364,C_1361,B_1362)
      | ~ v1_funct_1(E_1364)
      | ~ m1_subset_1(D_1363,k1_zfmisc_1(A_1365))
      | v1_xboole_0(D_1363)
      | ~ m1_subset_1(C_1361,k1_zfmisc_1(A_1365))
      | v1_xboole_0(C_1361)
      | v1_xboole_0(B_1362)
      | v1_xboole_0(A_1365) ) ),
    inference(resolution,[status(thm)],[c_42,c_6029])).

tff(c_7520,plain,(
    ! [E_1465,D_1464,A_1466,C_1462,B_1463,F_1467] :
      ( k2_partfun1(k4_subset_1(A_1466,C_1462,D_1464),B_1463,k1_tmap_1(A_1466,B_1463,C_1462,D_1464,E_1465,F_1467),D_1464) = F_1467
      | ~ v1_funct_1(k1_tmap_1(A_1466,B_1463,C_1462,D_1464,E_1465,F_1467))
      | k2_partfun1(D_1464,B_1463,F_1467,k9_subset_1(A_1466,C_1462,D_1464)) != k2_partfun1(C_1462,B_1463,E_1465,k9_subset_1(A_1466,C_1462,D_1464))
      | ~ m1_subset_1(F_1467,k1_zfmisc_1(k2_zfmisc_1(D_1464,B_1463)))
      | ~ v1_funct_2(F_1467,D_1464,B_1463)
      | ~ v1_funct_1(F_1467)
      | ~ m1_subset_1(E_1465,k1_zfmisc_1(k2_zfmisc_1(C_1462,B_1463)))
      | ~ v1_funct_2(E_1465,C_1462,B_1463)
      | ~ v1_funct_1(E_1465)
      | ~ m1_subset_1(D_1464,k1_zfmisc_1(A_1466))
      | v1_xboole_0(D_1464)
      | ~ m1_subset_1(C_1462,k1_zfmisc_1(A_1466))
      | v1_xboole_0(C_1462)
      | v1_xboole_0(B_1463)
      | v1_xboole_0(A_1466) ) ),
    inference(resolution,[status(thm)],[c_44,c_6701])).

tff(c_7524,plain,(
    ! [A_1466,C_1462,E_1465] :
      ( k2_partfun1(k4_subset_1(A_1466,C_1462,'#skF_4'),'#skF_2',k1_tmap_1(A_1466,'#skF_2',C_1462,'#skF_4',E_1465,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1466,'#skF_2',C_1462,'#skF_4',E_1465,'#skF_6'))
      | k2_partfun1(C_1462,'#skF_2',E_1465,k9_subset_1(A_1466,C_1462,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1466,C_1462,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1465,k1_zfmisc_1(k2_zfmisc_1(C_1462,'#skF_2')))
      | ~ v1_funct_2(E_1465,C_1462,'#skF_2')
      | ~ v1_funct_1(E_1465)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1466))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1462,k1_zfmisc_1(A_1466))
      | v1_xboole_0(C_1462)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1466) ) ),
    inference(resolution,[status(thm)],[c_50,c_7520])).

tff(c_7533,plain,(
    ! [A_1466,C_1462,E_1465] :
      ( k2_partfun1(k4_subset_1(A_1466,C_1462,'#skF_4'),'#skF_2',k1_tmap_1(A_1466,'#skF_2',C_1462,'#skF_4',E_1465,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1466,'#skF_2',C_1462,'#skF_4',E_1465,'#skF_6'))
      | k2_partfun1(C_1462,'#skF_2',E_1465,k9_subset_1(A_1466,C_1462,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1466,C_1462,'#skF_4'))
      | ~ m1_subset_1(E_1465,k1_zfmisc_1(k2_zfmisc_1(C_1462,'#skF_2')))
      | ~ v1_funct_2(E_1465,C_1462,'#skF_2')
      | ~ v1_funct_1(E_1465)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1466))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1462,k1_zfmisc_1(A_1466))
      | v1_xboole_0(C_1462)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_5534,c_7524])).

tff(c_7753,plain,(
    ! [A_1508,C_1509,E_1510] :
      ( k2_partfun1(k4_subset_1(A_1508,C_1509,'#skF_4'),'#skF_2',k1_tmap_1(A_1508,'#skF_2',C_1509,'#skF_4',E_1510,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1508,'#skF_2',C_1509,'#skF_4',E_1510,'#skF_6'))
      | k2_partfun1(C_1509,'#skF_2',E_1510,k9_subset_1(A_1508,C_1509,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1508,C_1509,'#skF_4'))
      | ~ m1_subset_1(E_1510,k1_zfmisc_1(k2_zfmisc_1(C_1509,'#skF_2')))
      | ~ v1_funct_2(E_1510,C_1509,'#skF_2')
      | ~ v1_funct_1(E_1510)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1508))
      | ~ m1_subset_1(C_1509,k1_zfmisc_1(A_1508))
      | v1_xboole_0(C_1509)
      | v1_xboole_0(A_1508) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_7533])).

tff(c_7760,plain,(
    ! [A_1508] :
      ( k2_partfun1(k4_subset_1(A_1508,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1508,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1508,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1508,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1508,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1508))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1508))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1508) ) ),
    inference(resolution,[status(thm)],[c_56,c_7753])).

tff(c_7773,plain,(
    ! [A_1508] :
      ( k2_partfun1(k4_subset_1(A_1508,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1508,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1508,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1508,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1508,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1508))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1508))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5537,c_7760])).

tff(c_7776,plain,(
    ! [A_1511] :
      ( k2_partfun1(k4_subset_1(A_1511,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1511,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1511,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1511,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1511,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1511))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1511))
      | v1_xboole_0(A_1511) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_7773])).

tff(c_874,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5568,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_7787,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7776,c_5568])).

tff(c_7801,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_5599,c_5592,c_5496,c_5496,c_5359,c_5359,c_5798,c_7787])).

tff(c_7803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_7801])).

tff(c_7804,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_9902,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9893,c_7804])).

tff(c_9913,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_7839,c_7829,c_5496,c_5359,c_5496,c_5359,c_8277,c_9902])).

tff(c_9915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_9913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:16:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.50/6.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.50/6.09  
% 14.50/6.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.50/6.10  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k5_relset_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.50/6.10  
% 14.50/6.10  %Foreground sorts:
% 14.50/6.10  
% 14.50/6.10  
% 14.50/6.10  %Background operators:
% 14.50/6.10  
% 14.50/6.10  
% 14.50/6.10  %Foreground operators:
% 14.50/6.10  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 14.50/6.10  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 14.50/6.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.50/6.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.50/6.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.50/6.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.50/6.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.50/6.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.50/6.10  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.50/6.10  tff('#skF_5', type, '#skF_5': $i).
% 14.50/6.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.50/6.10  tff('#skF_6', type, '#skF_6': $i).
% 14.50/6.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.50/6.10  tff('#skF_2', type, '#skF_2': $i).
% 14.50/6.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.50/6.10  tff('#skF_3', type, '#skF_3': $i).
% 14.50/6.10  tff('#skF_1', type, '#skF_1': $i).
% 14.50/6.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.50/6.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.50/6.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.50/6.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.50/6.10  tff('#skF_4', type, '#skF_4': $i).
% 14.50/6.10  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.50/6.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.50/6.10  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 14.50/6.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.50/6.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.50/6.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.50/6.10  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.50/6.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.50/6.10  
% 14.74/6.14  tff(f_213, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 14.74/6.14  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 14.74/6.14  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.74/6.14  tff(f_50, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 14.74/6.14  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 14.74/6.14  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 14.74/6.14  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 14.74/6.14  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 14.74/6.14  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 14.74/6.14  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 14.74/6.14  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.74/6.14  tff(f_171, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 14.74/6.14  tff(f_89, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 14.74/6.14  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 14.74/6.14  tff(c_74, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.74/6.14  tff(c_899, plain, (![C_377, A_378, B_379]: (v1_relat_1(C_377) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_378, B_379))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.74/6.14  tff(c_912, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_899])).
% 14.74/6.14  tff(c_14, plain, (![A_13]: (k9_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.74/6.14  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.74/6.14  tff(c_5327, plain, (![B_1118, A_1119]: (r1_xboole_0(k1_relat_1(B_1118), A_1119) | k9_relat_1(B_1118, A_1119)!=k1_xboole_0 | ~v1_relat_1(B_1118))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.74/6.14  tff(c_5339, plain, (![A_1119]: (r1_xboole_0(k1_xboole_0, A_1119) | k9_relat_1(k1_xboole_0, A_1119)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5327])).
% 14.74/6.14  tff(c_5344, plain, (![A_1119]: (r1_xboole_0(k1_xboole_0, A_1119))), inference(demodulation, [status(thm), theory('equality')], [c_912, c_14, c_5339])).
% 14.74/6.14  tff(c_5511, plain, (![C_1148, A_1149, D_1150, B_1151]: (k5_relset_1(C_1148, A_1149, D_1150, B_1151)=k1_xboole_0 | ~r1_xboole_0(B_1151, C_1148) | ~m1_subset_1(D_1150, k1_zfmisc_1(k2_zfmisc_1(C_1148, A_1149))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.74/6.14  tff(c_7812, plain, (![A_1512, A_1513, D_1514]: (k5_relset_1(A_1512, A_1513, D_1514, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(D_1514, k1_zfmisc_1(k2_zfmisc_1(A_1512, A_1513))))), inference(resolution, [status(thm)], [c_5344, c_5511])).
% 14.74/6.14  tff(c_7824, plain, (k5_relset_1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_7812])).
% 14.74/6.14  tff(c_5447, plain, (![A_1135, B_1136, C_1137, D_1138]: (k5_relset_1(A_1135, B_1136, C_1137, D_1138)=k7_relat_1(C_1137, D_1138) | ~m1_subset_1(C_1137, k1_zfmisc_1(k2_zfmisc_1(A_1135, B_1136))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.74/6.14  tff(c_5456, plain, (![D_1138]: (k5_relset_1('#skF_3', '#skF_2', '#skF_5', D_1138)=k7_relat_1('#skF_5', D_1138))), inference(resolution, [status(thm)], [c_56, c_5447])).
% 14.74/6.14  tff(c_7839, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7824, c_5456])).
% 14.74/6.14  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_7823, plain, (k5_relset_1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_7812])).
% 14.74/6.14  tff(c_5455, plain, (![D_1138]: (k5_relset_1('#skF_4', '#skF_2', '#skF_6', D_1138)=k7_relat_1('#skF_6', D_1138))), inference(resolution, [status(thm)], [c_50, c_5447])).
% 14.74/6.14  tff(c_7829, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7823, c_5455])).
% 14.74/6.14  tff(c_70, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_62, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_5276, plain, (![A_1103, B_1104]: (r1_xboole_0(A_1103, B_1104) | ~r1_subset_1(A_1103, B_1104) | v1_xboole_0(B_1104) | v1_xboole_0(A_1103))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.74/6.14  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.74/6.14  tff(c_5490, plain, (![A_1144, B_1145]: (k3_xboole_0(A_1144, B_1145)=k1_xboole_0 | ~r1_subset_1(A_1144, B_1145) | v1_xboole_0(B_1145) | v1_xboole_0(A_1144))), inference(resolution, [status(thm)], [c_5276, c_2])).
% 14.74/6.14  tff(c_5493, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_5490])).
% 14.74/6.14  tff(c_5496, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_5493])).
% 14.74/6.14  tff(c_5345, plain, (![A_1120, B_1121, C_1122]: (k9_subset_1(A_1120, B_1121, C_1122)=k3_xboole_0(B_1121, C_1122) | ~m1_subset_1(C_1122, k1_zfmisc_1(A_1120)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.74/6.14  tff(c_5359, plain, (![B_1121]: (k9_subset_1('#skF_1', B_1121, '#skF_4')=k3_xboole_0(B_1121, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_5345])).
% 14.74/6.14  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_72, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_7975, plain, (![C_1527, D_1529, A_1531, B_1528, E_1530, F_1532]: (v1_funct_1(k1_tmap_1(A_1531, B_1528, C_1527, D_1529, E_1530, F_1532)) | ~m1_subset_1(F_1532, k1_zfmisc_1(k2_zfmisc_1(D_1529, B_1528))) | ~v1_funct_2(F_1532, D_1529, B_1528) | ~v1_funct_1(F_1532) | ~m1_subset_1(E_1530, k1_zfmisc_1(k2_zfmisc_1(C_1527, B_1528))) | ~v1_funct_2(E_1530, C_1527, B_1528) | ~v1_funct_1(E_1530) | ~m1_subset_1(D_1529, k1_zfmisc_1(A_1531)) | v1_xboole_0(D_1529) | ~m1_subset_1(C_1527, k1_zfmisc_1(A_1531)) | v1_xboole_0(C_1527) | v1_xboole_0(B_1528) | v1_xboole_0(A_1531))), inference(cnfTransformation, [status(thm)], [f_171])).
% 14.74/6.14  tff(c_7977, plain, (![A_1531, C_1527, E_1530]: (v1_funct_1(k1_tmap_1(A_1531, '#skF_2', C_1527, '#skF_4', E_1530, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1530, k1_zfmisc_1(k2_zfmisc_1(C_1527, '#skF_2'))) | ~v1_funct_2(E_1530, C_1527, '#skF_2') | ~v1_funct_1(E_1530) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1531)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1527, k1_zfmisc_1(A_1531)) | v1_xboole_0(C_1527) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1531))), inference(resolution, [status(thm)], [c_50, c_7975])).
% 14.74/6.14  tff(c_7985, plain, (![A_1531, C_1527, E_1530]: (v1_funct_1(k1_tmap_1(A_1531, '#skF_2', C_1527, '#skF_4', E_1530, '#skF_6')) | ~m1_subset_1(E_1530, k1_zfmisc_1(k2_zfmisc_1(C_1527, '#skF_2'))) | ~v1_funct_2(E_1530, C_1527, '#skF_2') | ~v1_funct_1(E_1530) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1531)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1527, k1_zfmisc_1(A_1531)) | v1_xboole_0(C_1527) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1531))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_7977])).
% 14.74/6.14  tff(c_8240, plain, (![A_1570, C_1571, E_1572]: (v1_funct_1(k1_tmap_1(A_1570, '#skF_2', C_1571, '#skF_4', E_1572, '#skF_6')) | ~m1_subset_1(E_1572, k1_zfmisc_1(k2_zfmisc_1(C_1571, '#skF_2'))) | ~v1_funct_2(E_1572, C_1571, '#skF_2') | ~v1_funct_1(E_1572) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1570)) | ~m1_subset_1(C_1571, k1_zfmisc_1(A_1570)) | v1_xboole_0(C_1571) | v1_xboole_0(A_1570))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_7985])).
% 14.74/6.14  tff(c_8247, plain, (![A_1570]: (v1_funct_1(k1_tmap_1(A_1570, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1570)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1570)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1570))), inference(resolution, [status(thm)], [c_56, c_8240])).
% 14.74/6.14  tff(c_8260, plain, (![A_1570]: (v1_funct_1(k1_tmap_1(A_1570, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1570)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1570)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1570))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_8247])).
% 14.74/6.14  tff(c_8270, plain, (![A_1574]: (v1_funct_1(k1_tmap_1(A_1574, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1574)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1574)) | v1_xboole_0(A_1574))), inference(negUnitSimplification, [status(thm)], [c_70, c_8260])).
% 14.74/6.14  tff(c_8273, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_8270])).
% 14.74/6.14  tff(c_8276, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8273])).
% 14.74/6.14  tff(c_8277, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_8276])).
% 14.74/6.14  tff(c_5524, plain, (![A_1152, B_1153, C_1154, D_1155]: (k2_partfun1(A_1152, B_1153, C_1154, D_1155)=k7_relat_1(C_1154, D_1155) | ~m1_subset_1(C_1154, k1_zfmisc_1(k2_zfmisc_1(A_1152, B_1153))) | ~v1_funct_1(C_1154))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.74/6.14  tff(c_5528, plain, (![D_1155]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1155)=k7_relat_1('#skF_5', D_1155) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_5524])).
% 14.74/6.14  tff(c_5537, plain, (![D_1155]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1155)=k7_relat_1('#skF_5', D_1155))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5528])).
% 14.74/6.14  tff(c_5526, plain, (![D_1155]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1155)=k7_relat_1('#skF_6', D_1155) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_5524])).
% 14.74/6.14  tff(c_5534, plain, (![D_1155]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1155)=k7_relat_1('#skF_6', D_1155))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5526])).
% 14.74/6.14  tff(c_44, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_171])).
% 14.74/6.14  tff(c_42, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_171])).
% 14.74/6.14  tff(c_8328, plain, (![B_1587, E_1586, A_1585, D_1590, F_1588, C_1589]: (k2_partfun1(k4_subset_1(A_1585, C_1589, D_1590), B_1587, k1_tmap_1(A_1585, B_1587, C_1589, D_1590, E_1586, F_1588), C_1589)=E_1586 | ~m1_subset_1(k1_tmap_1(A_1585, B_1587, C_1589, D_1590, E_1586, F_1588), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1585, C_1589, D_1590), B_1587))) | ~v1_funct_2(k1_tmap_1(A_1585, B_1587, C_1589, D_1590, E_1586, F_1588), k4_subset_1(A_1585, C_1589, D_1590), B_1587) | ~v1_funct_1(k1_tmap_1(A_1585, B_1587, C_1589, D_1590, E_1586, F_1588)) | k2_partfun1(D_1590, B_1587, F_1588, k9_subset_1(A_1585, C_1589, D_1590))!=k2_partfun1(C_1589, B_1587, E_1586, k9_subset_1(A_1585, C_1589, D_1590)) | ~m1_subset_1(F_1588, k1_zfmisc_1(k2_zfmisc_1(D_1590, B_1587))) | ~v1_funct_2(F_1588, D_1590, B_1587) | ~v1_funct_1(F_1588) | ~m1_subset_1(E_1586, k1_zfmisc_1(k2_zfmisc_1(C_1589, B_1587))) | ~v1_funct_2(E_1586, C_1589, B_1587) | ~v1_funct_1(E_1586) | ~m1_subset_1(D_1590, k1_zfmisc_1(A_1585)) | v1_xboole_0(D_1590) | ~m1_subset_1(C_1589, k1_zfmisc_1(A_1585)) | v1_xboole_0(C_1589) | v1_xboole_0(B_1587) | v1_xboole_0(A_1585))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.74/6.14  tff(c_8903, plain, (![F_1711, C_1706, E_1709, D_1708, A_1710, B_1707]: (k2_partfun1(k4_subset_1(A_1710, C_1706, D_1708), B_1707, k1_tmap_1(A_1710, B_1707, C_1706, D_1708, E_1709, F_1711), C_1706)=E_1709 | ~v1_funct_2(k1_tmap_1(A_1710, B_1707, C_1706, D_1708, E_1709, F_1711), k4_subset_1(A_1710, C_1706, D_1708), B_1707) | ~v1_funct_1(k1_tmap_1(A_1710, B_1707, C_1706, D_1708, E_1709, F_1711)) | k2_partfun1(D_1708, B_1707, F_1711, k9_subset_1(A_1710, C_1706, D_1708))!=k2_partfun1(C_1706, B_1707, E_1709, k9_subset_1(A_1710, C_1706, D_1708)) | ~m1_subset_1(F_1711, k1_zfmisc_1(k2_zfmisc_1(D_1708, B_1707))) | ~v1_funct_2(F_1711, D_1708, B_1707) | ~v1_funct_1(F_1711) | ~m1_subset_1(E_1709, k1_zfmisc_1(k2_zfmisc_1(C_1706, B_1707))) | ~v1_funct_2(E_1709, C_1706, B_1707) | ~v1_funct_1(E_1709) | ~m1_subset_1(D_1708, k1_zfmisc_1(A_1710)) | v1_xboole_0(D_1708) | ~m1_subset_1(C_1706, k1_zfmisc_1(A_1710)) | v1_xboole_0(C_1706) | v1_xboole_0(B_1707) | v1_xboole_0(A_1710))), inference(resolution, [status(thm)], [c_42, c_8328])).
% 14.74/6.14  tff(c_9434, plain, (![B_1777, E_1779, D_1778, C_1776, F_1781, A_1780]: (k2_partfun1(k4_subset_1(A_1780, C_1776, D_1778), B_1777, k1_tmap_1(A_1780, B_1777, C_1776, D_1778, E_1779, F_1781), C_1776)=E_1779 | ~v1_funct_1(k1_tmap_1(A_1780, B_1777, C_1776, D_1778, E_1779, F_1781)) | k2_partfun1(D_1778, B_1777, F_1781, k9_subset_1(A_1780, C_1776, D_1778))!=k2_partfun1(C_1776, B_1777, E_1779, k9_subset_1(A_1780, C_1776, D_1778)) | ~m1_subset_1(F_1781, k1_zfmisc_1(k2_zfmisc_1(D_1778, B_1777))) | ~v1_funct_2(F_1781, D_1778, B_1777) | ~v1_funct_1(F_1781) | ~m1_subset_1(E_1779, k1_zfmisc_1(k2_zfmisc_1(C_1776, B_1777))) | ~v1_funct_2(E_1779, C_1776, B_1777) | ~v1_funct_1(E_1779) | ~m1_subset_1(D_1778, k1_zfmisc_1(A_1780)) | v1_xboole_0(D_1778) | ~m1_subset_1(C_1776, k1_zfmisc_1(A_1780)) | v1_xboole_0(C_1776) | v1_xboole_0(B_1777) | v1_xboole_0(A_1780))), inference(resolution, [status(thm)], [c_44, c_8903])).
% 14.74/6.14  tff(c_9438, plain, (![A_1780, C_1776, E_1779]: (k2_partfun1(k4_subset_1(A_1780, C_1776, '#skF_4'), '#skF_2', k1_tmap_1(A_1780, '#skF_2', C_1776, '#skF_4', E_1779, '#skF_6'), C_1776)=E_1779 | ~v1_funct_1(k1_tmap_1(A_1780, '#skF_2', C_1776, '#skF_4', E_1779, '#skF_6')) | k2_partfun1(C_1776, '#skF_2', E_1779, k9_subset_1(A_1780, C_1776, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1780, C_1776, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1779, k1_zfmisc_1(k2_zfmisc_1(C_1776, '#skF_2'))) | ~v1_funct_2(E_1779, C_1776, '#skF_2') | ~v1_funct_1(E_1779) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1780)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1776, k1_zfmisc_1(A_1780)) | v1_xboole_0(C_1776) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1780))), inference(resolution, [status(thm)], [c_50, c_9434])).
% 14.74/6.14  tff(c_9447, plain, (![A_1780, C_1776, E_1779]: (k2_partfun1(k4_subset_1(A_1780, C_1776, '#skF_4'), '#skF_2', k1_tmap_1(A_1780, '#skF_2', C_1776, '#skF_4', E_1779, '#skF_6'), C_1776)=E_1779 | ~v1_funct_1(k1_tmap_1(A_1780, '#skF_2', C_1776, '#skF_4', E_1779, '#skF_6')) | k2_partfun1(C_1776, '#skF_2', E_1779, k9_subset_1(A_1780, C_1776, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1780, C_1776, '#skF_4')) | ~m1_subset_1(E_1779, k1_zfmisc_1(k2_zfmisc_1(C_1776, '#skF_2'))) | ~v1_funct_2(E_1779, C_1776, '#skF_2') | ~v1_funct_1(E_1779) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1780)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1776, k1_zfmisc_1(A_1780)) | v1_xboole_0(C_1776) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1780))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5534, c_9438])).
% 14.74/6.14  tff(c_9870, plain, (![A_1825, C_1826, E_1827]: (k2_partfun1(k4_subset_1(A_1825, C_1826, '#skF_4'), '#skF_2', k1_tmap_1(A_1825, '#skF_2', C_1826, '#skF_4', E_1827, '#skF_6'), C_1826)=E_1827 | ~v1_funct_1(k1_tmap_1(A_1825, '#skF_2', C_1826, '#skF_4', E_1827, '#skF_6')) | k2_partfun1(C_1826, '#skF_2', E_1827, k9_subset_1(A_1825, C_1826, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1825, C_1826, '#skF_4')) | ~m1_subset_1(E_1827, k1_zfmisc_1(k2_zfmisc_1(C_1826, '#skF_2'))) | ~v1_funct_2(E_1827, C_1826, '#skF_2') | ~v1_funct_1(E_1827) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1825)) | ~m1_subset_1(C_1826, k1_zfmisc_1(A_1825)) | v1_xboole_0(C_1826) | v1_xboole_0(A_1825))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_9447])).
% 14.74/6.14  tff(c_9877, plain, (![A_1825]: (k2_partfun1(k4_subset_1(A_1825, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1825, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1825, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1825, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1825, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1825)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1825)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1825))), inference(resolution, [status(thm)], [c_56, c_9870])).
% 14.74/6.14  tff(c_9890, plain, (![A_1825]: (k2_partfun1(k4_subset_1(A_1825, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1825, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1825, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1825, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1825, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1825)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1825)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1825))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5537, c_9877])).
% 14.74/6.14  tff(c_9893, plain, (![A_1828]: (k2_partfun1(k4_subset_1(A_1828, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1828, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1828, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1828, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1828, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1828)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1828)) | v1_xboole_0(A_1828))), inference(negUnitSimplification, [status(thm)], [c_70, c_9890])).
% 14.74/6.14  tff(c_5575, plain, (![A_1158, A_1159, D_1160]: (k5_relset_1(A_1158, A_1159, D_1160, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(D_1160, k1_zfmisc_1(k2_zfmisc_1(A_1158, A_1159))))), inference(resolution, [status(thm)], [c_5344, c_5511])).
% 14.74/6.14  tff(c_5586, plain, (k5_relset_1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_5575])).
% 14.74/6.14  tff(c_5592, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5586, c_5455])).
% 14.74/6.14  tff(c_522, plain, (![C_312, A_313, B_314]: (v1_relat_1(C_312) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.74/6.14  tff(c_535, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_522])).
% 14.74/6.14  tff(c_541, plain, (![B_317, A_318]: (r1_xboole_0(k1_relat_1(B_317), A_318) | k9_relat_1(B_317, A_318)!=k1_xboole_0 | ~v1_relat_1(B_317))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.74/6.14  tff(c_547, plain, (![A_318]: (r1_xboole_0(k1_xboole_0, A_318) | k9_relat_1(k1_xboole_0, A_318)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_541])).
% 14.74/6.14  tff(c_550, plain, (![A_318]: (r1_xboole_0(k1_xboole_0, A_318))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_14, c_547])).
% 14.74/6.14  tff(c_738, plain, (![C_356, A_357, D_358, B_359]: (k5_relset_1(C_356, A_357, D_358, B_359)=k1_xboole_0 | ~r1_xboole_0(B_359, C_356) | ~m1_subset_1(D_358, k1_zfmisc_1(k2_zfmisc_1(C_356, A_357))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.74/6.14  tff(c_775, plain, (![A_364, A_365, D_366]: (k5_relset_1(A_364, A_365, D_366, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(D_366, k1_zfmisc_1(k2_zfmisc_1(A_364, A_365))))), inference(resolution, [status(thm)], [c_550, c_738])).
% 14.74/6.14  tff(c_787, plain, (k5_relset_1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_775])).
% 14.74/6.14  tff(c_657, plain, (![A_340, B_341, C_342, D_343]: (k5_relset_1(A_340, B_341, C_342, D_343)=k7_relat_1(C_342, D_343) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.74/6.14  tff(c_666, plain, (![D_343]: (k5_relset_1('#skF_3', '#skF_2', '#skF_5', D_343)=k7_relat_1('#skF_5', D_343))), inference(resolution, [status(thm)], [c_56, c_657])).
% 14.74/6.14  tff(c_807, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_787, c_666])).
% 14.74/6.14  tff(c_819, plain, (![A_367, B_368, C_369, D_370]: (k2_partfun1(A_367, B_368, C_369, D_370)=k7_relat_1(C_369, D_370) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))) | ~v1_funct_1(C_369))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.74/6.14  tff(c_823, plain, (![D_370]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_370)=k7_relat_1('#skF_5', D_370) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_819])).
% 14.74/6.14  tff(c_832, plain, (![D_370]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_370)=k7_relat_1('#skF_5', D_370))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_823])).
% 14.74/6.14  tff(c_786, plain, (k5_relset_1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_775])).
% 14.74/6.14  tff(c_665, plain, (![D_343]: (k5_relset_1('#skF_4', '#skF_2', '#skF_6', D_343)=k7_relat_1('#skF_6', D_343))), inference(resolution, [status(thm)], [c_50, c_657])).
% 14.74/6.14  tff(c_792, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_786, c_665])).
% 14.74/6.14  tff(c_821, plain, (![D_370]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_370)=k7_relat_1('#skF_6', D_370) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_819])).
% 14.74/6.14  tff(c_829, plain, (![D_370]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_370)=k7_relat_1('#skF_6', D_370))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_821])).
% 14.74/6.14  tff(c_536, plain, (![A_315, B_316]: (r1_xboole_0(A_315, B_316) | ~r1_subset_1(A_315, B_316) | v1_xboole_0(B_316) | v1_xboole_0(A_315))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.74/6.14  tff(c_722, plain, (![A_352, B_353]: (k3_xboole_0(A_352, B_353)=k1_xboole_0 | ~r1_subset_1(A_352, B_353) | v1_xboole_0(B_353) | v1_xboole_0(A_352))), inference(resolution, [status(thm)], [c_536, c_2])).
% 14.74/6.14  tff(c_725, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_722])).
% 14.74/6.14  tff(c_728, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_725])).
% 14.74/6.14  tff(c_622, plain, (![A_334, B_335, C_336]: (k9_subset_1(A_334, B_335, C_336)=k3_xboole_0(B_335, C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(A_334)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.74/6.14  tff(c_636, plain, (![B_335]: (k9_subset_1('#skF_1', B_335, '#skF_4')=k3_xboole_0(B_335, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_622])).
% 14.74/6.14  tff(c_48, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 14.74/6.14  tff(c_97, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_48])).
% 14.74/6.14  tff(c_647, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_636, c_97])).
% 14.74/6.14  tff(c_873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_807, c_832, c_792, c_829, c_728, c_728, c_647])).
% 14.74/6.14  tff(c_875, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 14.74/6.14  tff(c_5485, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5359, c_5359, c_875])).
% 14.74/6.14  tff(c_5497, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5496, c_5496, c_5485])).
% 14.74/6.14  tff(c_5539, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5534, c_5497])).
% 14.74/6.14  tff(c_5561, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5539, c_5537])).
% 14.74/6.14  tff(c_5599, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5592, c_5561])).
% 14.74/6.14  tff(c_5640, plain, (![E_1166, B_1164, F_1168, D_1165, C_1163, A_1167]: (v1_funct_1(k1_tmap_1(A_1167, B_1164, C_1163, D_1165, E_1166, F_1168)) | ~m1_subset_1(F_1168, k1_zfmisc_1(k2_zfmisc_1(D_1165, B_1164))) | ~v1_funct_2(F_1168, D_1165, B_1164) | ~v1_funct_1(F_1168) | ~m1_subset_1(E_1166, k1_zfmisc_1(k2_zfmisc_1(C_1163, B_1164))) | ~v1_funct_2(E_1166, C_1163, B_1164) | ~v1_funct_1(E_1166) | ~m1_subset_1(D_1165, k1_zfmisc_1(A_1167)) | v1_xboole_0(D_1165) | ~m1_subset_1(C_1163, k1_zfmisc_1(A_1167)) | v1_xboole_0(C_1163) | v1_xboole_0(B_1164) | v1_xboole_0(A_1167))), inference(cnfTransformation, [status(thm)], [f_171])).
% 14.74/6.14  tff(c_5642, plain, (![A_1167, C_1163, E_1166]: (v1_funct_1(k1_tmap_1(A_1167, '#skF_2', C_1163, '#skF_4', E_1166, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1166, k1_zfmisc_1(k2_zfmisc_1(C_1163, '#skF_2'))) | ~v1_funct_2(E_1166, C_1163, '#skF_2') | ~v1_funct_1(E_1166) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1167)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1163, k1_zfmisc_1(A_1167)) | v1_xboole_0(C_1163) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1167))), inference(resolution, [status(thm)], [c_50, c_5640])).
% 14.74/6.14  tff(c_5650, plain, (![A_1167, C_1163, E_1166]: (v1_funct_1(k1_tmap_1(A_1167, '#skF_2', C_1163, '#skF_4', E_1166, '#skF_6')) | ~m1_subset_1(E_1166, k1_zfmisc_1(k2_zfmisc_1(C_1163, '#skF_2'))) | ~v1_funct_2(E_1166, C_1163, '#skF_2') | ~v1_funct_1(E_1166) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1167)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1163, k1_zfmisc_1(A_1167)) | v1_xboole_0(C_1163) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1167))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5642])).
% 14.74/6.14  tff(c_5681, plain, (![A_1171, C_1172, E_1173]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', C_1172, '#skF_4', E_1173, '#skF_6')) | ~m1_subset_1(E_1173, k1_zfmisc_1(k2_zfmisc_1(C_1172, '#skF_2'))) | ~v1_funct_2(E_1173, C_1172, '#skF_2') | ~v1_funct_1(E_1173) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1(C_1172, k1_zfmisc_1(A_1171)) | v1_xboole_0(C_1172) | v1_xboole_0(A_1171))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_5650])).
% 14.74/6.14  tff(c_5685, plain, (![A_1171]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1171)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1171))), inference(resolution, [status(thm)], [c_56, c_5681])).
% 14.74/6.14  tff(c_5695, plain, (![A_1171]: (v1_funct_1(k1_tmap_1(A_1171, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1171)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1171))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5685])).
% 14.74/6.14  tff(c_5791, plain, (![A_1191]: (v1_funct_1(k1_tmap_1(A_1191, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1191)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1191)) | v1_xboole_0(A_1191))), inference(negUnitSimplification, [status(thm)], [c_70, c_5695])).
% 14.74/6.14  tff(c_5794, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_5791])).
% 14.74/6.14  tff(c_5797, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5794])).
% 14.74/6.14  tff(c_5798, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_5797])).
% 14.74/6.14  tff(c_6029, plain, (![F_1223, A_1220, B_1222, E_1221, D_1225, C_1224]: (k2_partfun1(k4_subset_1(A_1220, C_1224, D_1225), B_1222, k1_tmap_1(A_1220, B_1222, C_1224, D_1225, E_1221, F_1223), D_1225)=F_1223 | ~m1_subset_1(k1_tmap_1(A_1220, B_1222, C_1224, D_1225, E_1221, F_1223), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1220, C_1224, D_1225), B_1222))) | ~v1_funct_2(k1_tmap_1(A_1220, B_1222, C_1224, D_1225, E_1221, F_1223), k4_subset_1(A_1220, C_1224, D_1225), B_1222) | ~v1_funct_1(k1_tmap_1(A_1220, B_1222, C_1224, D_1225, E_1221, F_1223)) | k2_partfun1(D_1225, B_1222, F_1223, k9_subset_1(A_1220, C_1224, D_1225))!=k2_partfun1(C_1224, B_1222, E_1221, k9_subset_1(A_1220, C_1224, D_1225)) | ~m1_subset_1(F_1223, k1_zfmisc_1(k2_zfmisc_1(D_1225, B_1222))) | ~v1_funct_2(F_1223, D_1225, B_1222) | ~v1_funct_1(F_1223) | ~m1_subset_1(E_1221, k1_zfmisc_1(k2_zfmisc_1(C_1224, B_1222))) | ~v1_funct_2(E_1221, C_1224, B_1222) | ~v1_funct_1(E_1221) | ~m1_subset_1(D_1225, k1_zfmisc_1(A_1220)) | v1_xboole_0(D_1225) | ~m1_subset_1(C_1224, k1_zfmisc_1(A_1220)) | v1_xboole_0(C_1224) | v1_xboole_0(B_1222) | v1_xboole_0(A_1220))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.74/6.14  tff(c_6701, plain, (![F_1366, E_1364, A_1365, B_1362, D_1363, C_1361]: (k2_partfun1(k4_subset_1(A_1365, C_1361, D_1363), B_1362, k1_tmap_1(A_1365, B_1362, C_1361, D_1363, E_1364, F_1366), D_1363)=F_1366 | ~v1_funct_2(k1_tmap_1(A_1365, B_1362, C_1361, D_1363, E_1364, F_1366), k4_subset_1(A_1365, C_1361, D_1363), B_1362) | ~v1_funct_1(k1_tmap_1(A_1365, B_1362, C_1361, D_1363, E_1364, F_1366)) | k2_partfun1(D_1363, B_1362, F_1366, k9_subset_1(A_1365, C_1361, D_1363))!=k2_partfun1(C_1361, B_1362, E_1364, k9_subset_1(A_1365, C_1361, D_1363)) | ~m1_subset_1(F_1366, k1_zfmisc_1(k2_zfmisc_1(D_1363, B_1362))) | ~v1_funct_2(F_1366, D_1363, B_1362) | ~v1_funct_1(F_1366) | ~m1_subset_1(E_1364, k1_zfmisc_1(k2_zfmisc_1(C_1361, B_1362))) | ~v1_funct_2(E_1364, C_1361, B_1362) | ~v1_funct_1(E_1364) | ~m1_subset_1(D_1363, k1_zfmisc_1(A_1365)) | v1_xboole_0(D_1363) | ~m1_subset_1(C_1361, k1_zfmisc_1(A_1365)) | v1_xboole_0(C_1361) | v1_xboole_0(B_1362) | v1_xboole_0(A_1365))), inference(resolution, [status(thm)], [c_42, c_6029])).
% 14.74/6.14  tff(c_7520, plain, (![E_1465, D_1464, A_1466, C_1462, B_1463, F_1467]: (k2_partfun1(k4_subset_1(A_1466, C_1462, D_1464), B_1463, k1_tmap_1(A_1466, B_1463, C_1462, D_1464, E_1465, F_1467), D_1464)=F_1467 | ~v1_funct_1(k1_tmap_1(A_1466, B_1463, C_1462, D_1464, E_1465, F_1467)) | k2_partfun1(D_1464, B_1463, F_1467, k9_subset_1(A_1466, C_1462, D_1464))!=k2_partfun1(C_1462, B_1463, E_1465, k9_subset_1(A_1466, C_1462, D_1464)) | ~m1_subset_1(F_1467, k1_zfmisc_1(k2_zfmisc_1(D_1464, B_1463))) | ~v1_funct_2(F_1467, D_1464, B_1463) | ~v1_funct_1(F_1467) | ~m1_subset_1(E_1465, k1_zfmisc_1(k2_zfmisc_1(C_1462, B_1463))) | ~v1_funct_2(E_1465, C_1462, B_1463) | ~v1_funct_1(E_1465) | ~m1_subset_1(D_1464, k1_zfmisc_1(A_1466)) | v1_xboole_0(D_1464) | ~m1_subset_1(C_1462, k1_zfmisc_1(A_1466)) | v1_xboole_0(C_1462) | v1_xboole_0(B_1463) | v1_xboole_0(A_1466))), inference(resolution, [status(thm)], [c_44, c_6701])).
% 14.74/6.14  tff(c_7524, plain, (![A_1466, C_1462, E_1465]: (k2_partfun1(k4_subset_1(A_1466, C_1462, '#skF_4'), '#skF_2', k1_tmap_1(A_1466, '#skF_2', C_1462, '#skF_4', E_1465, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1466, '#skF_2', C_1462, '#skF_4', E_1465, '#skF_6')) | k2_partfun1(C_1462, '#skF_2', E_1465, k9_subset_1(A_1466, C_1462, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1466, C_1462, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1465, k1_zfmisc_1(k2_zfmisc_1(C_1462, '#skF_2'))) | ~v1_funct_2(E_1465, C_1462, '#skF_2') | ~v1_funct_1(E_1465) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1466)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1462, k1_zfmisc_1(A_1466)) | v1_xboole_0(C_1462) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1466))), inference(resolution, [status(thm)], [c_50, c_7520])).
% 14.74/6.14  tff(c_7533, plain, (![A_1466, C_1462, E_1465]: (k2_partfun1(k4_subset_1(A_1466, C_1462, '#skF_4'), '#skF_2', k1_tmap_1(A_1466, '#skF_2', C_1462, '#skF_4', E_1465, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1466, '#skF_2', C_1462, '#skF_4', E_1465, '#skF_6')) | k2_partfun1(C_1462, '#skF_2', E_1465, k9_subset_1(A_1466, C_1462, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1466, C_1462, '#skF_4')) | ~m1_subset_1(E_1465, k1_zfmisc_1(k2_zfmisc_1(C_1462, '#skF_2'))) | ~v1_funct_2(E_1465, C_1462, '#skF_2') | ~v1_funct_1(E_1465) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1466)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1462, k1_zfmisc_1(A_1466)) | v1_xboole_0(C_1462) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1466))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_5534, c_7524])).
% 14.74/6.14  tff(c_7753, plain, (![A_1508, C_1509, E_1510]: (k2_partfun1(k4_subset_1(A_1508, C_1509, '#skF_4'), '#skF_2', k1_tmap_1(A_1508, '#skF_2', C_1509, '#skF_4', E_1510, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1508, '#skF_2', C_1509, '#skF_4', E_1510, '#skF_6')) | k2_partfun1(C_1509, '#skF_2', E_1510, k9_subset_1(A_1508, C_1509, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1508, C_1509, '#skF_4')) | ~m1_subset_1(E_1510, k1_zfmisc_1(k2_zfmisc_1(C_1509, '#skF_2'))) | ~v1_funct_2(E_1510, C_1509, '#skF_2') | ~v1_funct_1(E_1510) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1508)) | ~m1_subset_1(C_1509, k1_zfmisc_1(A_1508)) | v1_xboole_0(C_1509) | v1_xboole_0(A_1508))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_7533])).
% 14.74/6.14  tff(c_7760, plain, (![A_1508]: (k2_partfun1(k4_subset_1(A_1508, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1508, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1508, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1508, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1508, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1508)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1508)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1508))), inference(resolution, [status(thm)], [c_56, c_7753])).
% 14.74/6.14  tff(c_7773, plain, (![A_1508]: (k2_partfun1(k4_subset_1(A_1508, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1508, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1508, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1508, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1508, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1508)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1508)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1508))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5537, c_7760])).
% 14.74/6.14  tff(c_7776, plain, (![A_1511]: (k2_partfun1(k4_subset_1(A_1511, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1511, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1511, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1511, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1511, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1511)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1511)) | v1_xboole_0(A_1511))), inference(negUnitSimplification, [status(thm)], [c_70, c_7773])).
% 14.74/6.14  tff(c_874, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 14.74/6.14  tff(c_5568, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_874])).
% 14.74/6.14  tff(c_7787, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7776, c_5568])).
% 14.74/6.14  tff(c_7801, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_5599, c_5592, c_5496, c_5496, c_5359, c_5359, c_5798, c_7787])).
% 14.74/6.14  tff(c_7803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_7801])).
% 14.74/6.14  tff(c_7804, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_874])).
% 14.74/6.14  tff(c_9902, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9893, c_7804])).
% 14.74/6.14  tff(c_9913, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_7839, c_7829, c_5496, c_5359, c_5496, c_5359, c_8277, c_9902])).
% 14.74/6.14  tff(c_9915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_9913])).
% 14.74/6.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.74/6.14  
% 14.74/6.14  Inference rules
% 14.74/6.14  ----------------------
% 14.74/6.14  #Ref     : 0
% 14.74/6.14  #Sup     : 2080
% 14.74/6.14  #Fact    : 0
% 14.74/6.14  #Define  : 0
% 14.74/6.14  #Split   : 33
% 14.74/6.14  #Chain   : 0
% 14.74/6.14  #Close   : 0
% 14.74/6.14  
% 14.74/6.14  Ordering : KBO
% 14.74/6.14  
% 14.74/6.14  Simplification rules
% 14.74/6.14  ----------------------
% 14.74/6.14  #Subsume      : 328
% 14.74/6.14  #Demod        : 1775
% 14.74/6.14  #Tautology    : 975
% 14.74/6.14  #SimpNegUnit  : 318
% 14.74/6.14  #BackRed      : 13
% 14.74/6.14  
% 14.74/6.14  #Partial instantiations: 0
% 14.74/6.14  #Strategies tried      : 1
% 14.74/6.14  
% 14.74/6.14  Timing (in seconds)
% 14.74/6.14  ----------------------
% 14.74/6.14  Preprocessing        : 0.66
% 14.74/6.14  Parsing              : 0.32
% 14.74/6.14  CNF conversion       : 0.10
% 14.74/6.14  Main loop            : 4.52
% 14.74/6.14  Inferencing          : 1.65
% 14.74/6.15  Reduction            : 1.57
% 14.74/6.15  Demodulation         : 1.18
% 14.74/6.15  BG Simplification    : 0.15
% 14.74/6.15  Subsumption          : 0.89
% 14.74/6.15  Abstraction          : 0.18
% 14.74/6.15  MUC search           : 0.00
% 14.74/6.15  Cooper               : 0.00
% 14.74/6.15  Total                : 5.28
% 14.74/6.15  Index Insertion      : 0.00
% 14.74/6.15  Index Deletion       : 0.00
% 14.74/6.15  Index Matching       : 0.00
% 14.74/6.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
