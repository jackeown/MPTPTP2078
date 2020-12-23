%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:20 EST 2020

% Result     : Theorem 15.17s
% Output     : CNFRefutation 15.17s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 598 expanded)
%              Number of leaves         :   46 ( 234 expanded)
%              Depth                    :   12
%              Number of atoms          :  686 (2930 expanded)
%              Number of equality atoms :  124 ( 522 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_230,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_188,axiom,(
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

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_154,axiom,(
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

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_1037,plain,(
    ! [C_423,A_424,B_425] :
      ( v1_relat_1(C_423)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1049,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_1037])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1114,plain,(
    ! [A_440,B_441] :
      ( r2_hidden('#skF_2'(A_440,B_441),A_440)
      | r1_xboole_0(A_440,B_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1119,plain,(
    ! [A_442,B_443] :
      ( ~ v1_xboole_0(A_442)
      | r1_xboole_0(A_442,B_443) ) ),
    inference(resolution,[status(thm)],[c_1114,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1133,plain,(
    ! [A_446,B_447] :
      ( k3_xboole_0(A_446,B_447) = k1_xboole_0
      | ~ v1_xboole_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_1119,c_6])).

tff(c_1136,plain,(
    ! [B_447] : k3_xboole_0(k1_xboole_0,B_447) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1133])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14532,plain,(
    ! [A_1403,B_1404,C_1405] :
      ( ~ r1_xboole_0(A_1403,B_1404)
      | ~ r2_hidden(C_1405,B_1404)
      | ~ r2_hidden(C_1405,A_1403) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14573,plain,(
    ! [C_1410,B_1411,A_1412] :
      ( ~ r2_hidden(C_1410,B_1411)
      | ~ r2_hidden(C_1410,A_1412)
      | k3_xboole_0(A_1412,B_1411) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_14532])).

tff(c_14739,plain,(
    ! [A_1440,B_1441,A_1442] :
      ( ~ r2_hidden('#skF_2'(A_1440,B_1441),A_1442)
      | k3_xboole_0(A_1442,B_1441) != k1_xboole_0
      | r1_xboole_0(A_1440,B_1441) ) ),
    inference(resolution,[status(thm)],[c_14,c_14573])).

tff(c_14753,plain,(
    ! [B_1443,A_1444] :
      ( k3_xboole_0(B_1443,B_1443) != k1_xboole_0
      | r1_xboole_0(A_1444,B_1443) ) ),
    inference(resolution,[status(thm)],[c_14,c_14739])).

tff(c_14760,plain,(
    ! [A_1444] : r1_xboole_0(A_1444,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_14753])).

tff(c_22,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14508,plain,(
    ! [B_1399,A_1400] :
      ( v4_relat_1(B_1399,A_1400)
      | ~ r1_tarski(k1_relat_1(B_1399),A_1400)
      | ~ v1_relat_1(B_1399) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14518,plain,(
    ! [B_1401] :
      ( v4_relat_1(B_1401,k1_relat_1(B_1401))
      | ~ v1_relat_1(B_1401) ) ),
    inference(resolution,[status(thm)],[c_22,c_14508])).

tff(c_36,plain,(
    ! [B_25,A_24] :
      ( k7_relat_1(B_25,A_24) = B_25
      | ~ v4_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14522,plain,(
    ! [B_1401] :
      ( k7_relat_1(B_1401,k1_relat_1(B_1401)) = B_1401
      | ~ v1_relat_1(B_1401) ) ),
    inference(resolution,[status(thm)],[c_14518,c_36])).

tff(c_14685,plain,(
    ! [C_1431,A_1432,B_1433] :
      ( k7_relat_1(k7_relat_1(C_1431,A_1432),B_1433) = k1_xboole_0
      | ~ r1_xboole_0(A_1432,B_1433)
      | ~ v1_relat_1(C_1431) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_15024,plain,(
    ! [B_1490,B_1491] :
      ( k7_relat_1(B_1490,B_1491) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_1490),B_1491)
      | ~ v1_relat_1(B_1490)
      | ~ v1_relat_1(B_1490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14522,c_14685])).

tff(c_15055,plain,(
    ! [B_1492] :
      ( k7_relat_1(B_1492,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_1492) ) ),
    inference(resolution,[status(thm)],[c_14760,c_15024])).

tff(c_15067,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1049,c_15055])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_1050,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_1037])).

tff(c_15066,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1050,c_15055])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_72,plain,(
    r1_subset_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_14561,plain,(
    ! [A_1408,B_1409] :
      ( r1_xboole_0(A_1408,B_1409)
      | ~ r1_subset_1(A_1408,B_1409)
      | v1_xboole_0(B_1409)
      | v1_xboole_0(A_1408) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14712,plain,(
    ! [A_1436,B_1437] :
      ( k3_xboole_0(A_1436,B_1437) = k1_xboole_0
      | ~ r1_subset_1(A_1436,B_1437)
      | v1_xboole_0(B_1437)
      | v1_xboole_0(A_1436) ) ),
    inference(resolution,[status(thm)],[c_14561,c_6])).

tff(c_14718,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_14712])).

tff(c_14722,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_76,c_14718])).

tff(c_14600,plain,(
    ! [A_1419,B_1420,C_1421] :
      ( k9_subset_1(A_1419,B_1420,C_1421) = k3_xboole_0(B_1420,C_1421)
      | ~ m1_subset_1(C_1421,k1_zfmisc_1(A_1419)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14615,plain,(
    ! [B_1420] : k9_subset_1('#skF_3',B_1420,'#skF_6') = k3_xboole_0(B_1420,'#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_14600])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_14905,plain,(
    ! [C_1463,D_1460,B_1458,A_1461,F_1459,E_1462] :
      ( v1_funct_1(k1_tmap_1(A_1461,B_1458,C_1463,D_1460,E_1462,F_1459))
      | ~ m1_subset_1(F_1459,k1_zfmisc_1(k2_zfmisc_1(D_1460,B_1458)))
      | ~ v1_funct_2(F_1459,D_1460,B_1458)
      | ~ v1_funct_1(F_1459)
      | ~ m1_subset_1(E_1462,k1_zfmisc_1(k2_zfmisc_1(C_1463,B_1458)))
      | ~ v1_funct_2(E_1462,C_1463,B_1458)
      | ~ v1_funct_1(E_1462)
      | ~ m1_subset_1(D_1460,k1_zfmisc_1(A_1461))
      | v1_xboole_0(D_1460)
      | ~ m1_subset_1(C_1463,k1_zfmisc_1(A_1461))
      | v1_xboole_0(C_1463)
      | v1_xboole_0(B_1458)
      | v1_xboole_0(A_1461) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_14910,plain,(
    ! [A_1461,C_1463,E_1462] :
      ( v1_funct_1(k1_tmap_1(A_1461,'#skF_4',C_1463,'#skF_6',E_1462,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1462,k1_zfmisc_1(k2_zfmisc_1(C_1463,'#skF_4')))
      | ~ v1_funct_2(E_1462,C_1463,'#skF_4')
      | ~ v1_funct_1(E_1462)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1461))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1463,k1_zfmisc_1(A_1461))
      | v1_xboole_0(C_1463)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1461) ) ),
    inference(resolution,[status(thm)],[c_60,c_14905])).

tff(c_14916,plain,(
    ! [A_1461,C_1463,E_1462] :
      ( v1_funct_1(k1_tmap_1(A_1461,'#skF_4',C_1463,'#skF_6',E_1462,'#skF_8'))
      | ~ m1_subset_1(E_1462,k1_zfmisc_1(k2_zfmisc_1(C_1463,'#skF_4')))
      | ~ v1_funct_2(E_1462,C_1463,'#skF_4')
      | ~ v1_funct_1(E_1462)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1461))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1463,k1_zfmisc_1(A_1461))
      | v1_xboole_0(C_1463)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_14910])).

tff(c_15203,plain,(
    ! [A_1513,C_1514,E_1515] :
      ( v1_funct_1(k1_tmap_1(A_1513,'#skF_4',C_1514,'#skF_6',E_1515,'#skF_8'))
      | ~ m1_subset_1(E_1515,k1_zfmisc_1(k2_zfmisc_1(C_1514,'#skF_4')))
      | ~ v1_funct_2(E_1515,C_1514,'#skF_4')
      | ~ v1_funct_1(E_1515)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1513))
      | ~ m1_subset_1(C_1514,k1_zfmisc_1(A_1513))
      | v1_xboole_0(C_1514)
      | v1_xboole_0(A_1513) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_14916])).

tff(c_15213,plain,(
    ! [A_1513] :
      ( v1_funct_1(k1_tmap_1(A_1513,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1513))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1513))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1513) ) ),
    inference(resolution,[status(thm)],[c_66,c_15203])).

tff(c_15224,plain,(
    ! [A_1513] :
      ( v1_funct_1(k1_tmap_1(A_1513,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1513))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1513))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_15213])).

tff(c_15393,plain,(
    ! [A_1560] :
      ( v1_funct_1(k1_tmap_1(A_1560,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1560))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1560))
      | v1_xboole_0(A_1560) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_15224])).

tff(c_15400,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_15393])).

tff(c_15404,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_15400])).

tff(c_15405,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_15404])).

tff(c_14803,plain,(
    ! [A_1450,B_1451,C_1452,D_1453] :
      ( k2_partfun1(A_1450,B_1451,C_1452,D_1453) = k7_relat_1(C_1452,D_1453)
      | ~ m1_subset_1(C_1452,k1_zfmisc_1(k2_zfmisc_1(A_1450,B_1451)))
      | ~ v1_funct_1(C_1452) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_14810,plain,(
    ! [D_1453] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_1453) = k7_relat_1('#skF_7',D_1453)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_14803])).

tff(c_14817,plain,(
    ! [D_1453] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_1453) = k7_relat_1('#skF_7',D_1453) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_14810])).

tff(c_14808,plain,(
    ! [D_1453] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_1453) = k7_relat_1('#skF_8',D_1453)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_60,c_14803])).

tff(c_14814,plain,(
    ! [D_1453] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_1453) = k7_relat_1('#skF_8',D_1453) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14808])).

tff(c_54,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_52,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_15173,plain,(
    ! [A_1504,C_1508,D_1507,E_1505,B_1506,F_1503] :
      ( k2_partfun1(k4_subset_1(A_1504,C_1508,D_1507),B_1506,k1_tmap_1(A_1504,B_1506,C_1508,D_1507,E_1505,F_1503),C_1508) = E_1505
      | ~ m1_subset_1(k1_tmap_1(A_1504,B_1506,C_1508,D_1507,E_1505,F_1503),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1504,C_1508,D_1507),B_1506)))
      | ~ v1_funct_2(k1_tmap_1(A_1504,B_1506,C_1508,D_1507,E_1505,F_1503),k4_subset_1(A_1504,C_1508,D_1507),B_1506)
      | ~ v1_funct_1(k1_tmap_1(A_1504,B_1506,C_1508,D_1507,E_1505,F_1503))
      | k2_partfun1(D_1507,B_1506,F_1503,k9_subset_1(A_1504,C_1508,D_1507)) != k2_partfun1(C_1508,B_1506,E_1505,k9_subset_1(A_1504,C_1508,D_1507))
      | ~ m1_subset_1(F_1503,k1_zfmisc_1(k2_zfmisc_1(D_1507,B_1506)))
      | ~ v1_funct_2(F_1503,D_1507,B_1506)
      | ~ v1_funct_1(F_1503)
      | ~ m1_subset_1(E_1505,k1_zfmisc_1(k2_zfmisc_1(C_1508,B_1506)))
      | ~ v1_funct_2(E_1505,C_1508,B_1506)
      | ~ v1_funct_1(E_1505)
      | ~ m1_subset_1(D_1507,k1_zfmisc_1(A_1504))
      | v1_xboole_0(D_1507)
      | ~ m1_subset_1(C_1508,k1_zfmisc_1(A_1504))
      | v1_xboole_0(C_1508)
      | v1_xboole_0(B_1506)
      | v1_xboole_0(A_1504) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_16798,plain,(
    ! [E_1722,B_1718,C_1723,D_1720,A_1721,F_1719] :
      ( k2_partfun1(k4_subset_1(A_1721,C_1723,D_1720),B_1718,k1_tmap_1(A_1721,B_1718,C_1723,D_1720,E_1722,F_1719),C_1723) = E_1722
      | ~ v1_funct_2(k1_tmap_1(A_1721,B_1718,C_1723,D_1720,E_1722,F_1719),k4_subset_1(A_1721,C_1723,D_1720),B_1718)
      | ~ v1_funct_1(k1_tmap_1(A_1721,B_1718,C_1723,D_1720,E_1722,F_1719))
      | k2_partfun1(D_1720,B_1718,F_1719,k9_subset_1(A_1721,C_1723,D_1720)) != k2_partfun1(C_1723,B_1718,E_1722,k9_subset_1(A_1721,C_1723,D_1720))
      | ~ m1_subset_1(F_1719,k1_zfmisc_1(k2_zfmisc_1(D_1720,B_1718)))
      | ~ v1_funct_2(F_1719,D_1720,B_1718)
      | ~ v1_funct_1(F_1719)
      | ~ m1_subset_1(E_1722,k1_zfmisc_1(k2_zfmisc_1(C_1723,B_1718)))
      | ~ v1_funct_2(E_1722,C_1723,B_1718)
      | ~ v1_funct_1(E_1722)
      | ~ m1_subset_1(D_1720,k1_zfmisc_1(A_1721))
      | v1_xboole_0(D_1720)
      | ~ m1_subset_1(C_1723,k1_zfmisc_1(A_1721))
      | v1_xboole_0(C_1723)
      | v1_xboole_0(B_1718)
      | v1_xboole_0(A_1721) ) ),
    inference(resolution,[status(thm)],[c_52,c_15173])).

tff(c_19483,plain,(
    ! [A_1942,E_1943,C_1944,B_1939,F_1940,D_1941] :
      ( k2_partfun1(k4_subset_1(A_1942,C_1944,D_1941),B_1939,k1_tmap_1(A_1942,B_1939,C_1944,D_1941,E_1943,F_1940),C_1944) = E_1943
      | ~ v1_funct_1(k1_tmap_1(A_1942,B_1939,C_1944,D_1941,E_1943,F_1940))
      | k2_partfun1(D_1941,B_1939,F_1940,k9_subset_1(A_1942,C_1944,D_1941)) != k2_partfun1(C_1944,B_1939,E_1943,k9_subset_1(A_1942,C_1944,D_1941))
      | ~ m1_subset_1(F_1940,k1_zfmisc_1(k2_zfmisc_1(D_1941,B_1939)))
      | ~ v1_funct_2(F_1940,D_1941,B_1939)
      | ~ v1_funct_1(F_1940)
      | ~ m1_subset_1(E_1943,k1_zfmisc_1(k2_zfmisc_1(C_1944,B_1939)))
      | ~ v1_funct_2(E_1943,C_1944,B_1939)
      | ~ v1_funct_1(E_1943)
      | ~ m1_subset_1(D_1941,k1_zfmisc_1(A_1942))
      | v1_xboole_0(D_1941)
      | ~ m1_subset_1(C_1944,k1_zfmisc_1(A_1942))
      | v1_xboole_0(C_1944)
      | v1_xboole_0(B_1939)
      | v1_xboole_0(A_1942) ) ),
    inference(resolution,[status(thm)],[c_54,c_16798])).

tff(c_19490,plain,(
    ! [A_1942,C_1944,E_1943] :
      ( k2_partfun1(k4_subset_1(A_1942,C_1944,'#skF_6'),'#skF_4',k1_tmap_1(A_1942,'#skF_4',C_1944,'#skF_6',E_1943,'#skF_8'),C_1944) = E_1943
      | ~ v1_funct_1(k1_tmap_1(A_1942,'#skF_4',C_1944,'#skF_6',E_1943,'#skF_8'))
      | k2_partfun1(C_1944,'#skF_4',E_1943,k9_subset_1(A_1942,C_1944,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_1942,C_1944,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1943,k1_zfmisc_1(k2_zfmisc_1(C_1944,'#skF_4')))
      | ~ v1_funct_2(E_1943,C_1944,'#skF_4')
      | ~ v1_funct_1(E_1943)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1942))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1944,k1_zfmisc_1(A_1942))
      | v1_xboole_0(C_1944)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1942) ) ),
    inference(resolution,[status(thm)],[c_60,c_19483])).

tff(c_19497,plain,(
    ! [A_1942,C_1944,E_1943] :
      ( k2_partfun1(k4_subset_1(A_1942,C_1944,'#skF_6'),'#skF_4',k1_tmap_1(A_1942,'#skF_4',C_1944,'#skF_6',E_1943,'#skF_8'),C_1944) = E_1943
      | ~ v1_funct_1(k1_tmap_1(A_1942,'#skF_4',C_1944,'#skF_6',E_1943,'#skF_8'))
      | k2_partfun1(C_1944,'#skF_4',E_1943,k9_subset_1(A_1942,C_1944,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1942,C_1944,'#skF_6'))
      | ~ m1_subset_1(E_1943,k1_zfmisc_1(k2_zfmisc_1(C_1944,'#skF_4')))
      | ~ v1_funct_2(E_1943,C_1944,'#skF_4')
      | ~ v1_funct_1(E_1943)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1942))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1944,k1_zfmisc_1(A_1942))
      | v1_xboole_0(C_1944)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1942) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_14814,c_19490])).

tff(c_25343,plain,(
    ! [A_2177,C_2178,E_2179] :
      ( k2_partfun1(k4_subset_1(A_2177,C_2178,'#skF_6'),'#skF_4',k1_tmap_1(A_2177,'#skF_4',C_2178,'#skF_6',E_2179,'#skF_8'),C_2178) = E_2179
      | ~ v1_funct_1(k1_tmap_1(A_2177,'#skF_4',C_2178,'#skF_6',E_2179,'#skF_8'))
      | k2_partfun1(C_2178,'#skF_4',E_2179,k9_subset_1(A_2177,C_2178,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2177,C_2178,'#skF_6'))
      | ~ m1_subset_1(E_2179,k1_zfmisc_1(k2_zfmisc_1(C_2178,'#skF_4')))
      | ~ v1_funct_2(E_2179,C_2178,'#skF_4')
      | ~ v1_funct_1(E_2179)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2177))
      | ~ m1_subset_1(C_2178,k1_zfmisc_1(A_2177))
      | v1_xboole_0(C_2178)
      | v1_xboole_0(A_2177) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_19497])).

tff(c_25353,plain,(
    ! [A_2177] :
      ( k2_partfun1(k4_subset_1(A_2177,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2177,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2177,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_2177,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2177,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2177))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2177))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2177) ) ),
    inference(resolution,[status(thm)],[c_66,c_25343])).

tff(c_25364,plain,(
    ! [A_2177] :
      ( k2_partfun1(k4_subset_1(A_2177,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2177,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2177,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2177,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2177,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2177))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2177))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_2177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_14817,c_25353])).

tff(c_25368,plain,(
    ! [A_2186] :
      ( k2_partfun1(k4_subset_1(A_2186,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_2186,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_2186,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2186,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_2186,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2186))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2186))
      | v1_xboole_0(A_2186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_25364])).

tff(c_1178,plain,(
    ! [A_455,B_456,C_457] :
      ( ~ r1_xboole_0(A_455,B_456)
      | ~ r2_hidden(C_457,B_456)
      | ~ r2_hidden(C_457,A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1215,plain,(
    ! [C_462,B_463,A_464] :
      ( ~ r2_hidden(C_462,B_463)
      | ~ r2_hidden(C_462,A_464)
      | k3_xboole_0(A_464,B_463) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1178])).

tff(c_1457,plain,(
    ! [A_499,B_500,A_501] :
      ( ~ r2_hidden('#skF_2'(A_499,B_500),A_501)
      | k3_xboole_0(A_501,B_500) != k1_xboole_0
      | r1_xboole_0(A_499,B_500) ) ),
    inference(resolution,[status(thm)],[c_14,c_1215])).

tff(c_1466,plain,(
    ! [B_502,A_503] :
      ( k3_xboole_0(B_502,B_502) != k1_xboole_0
      | r1_xboole_0(A_503,B_502) ) ),
    inference(resolution,[status(thm)],[c_14,c_1457])).

tff(c_1473,plain,(
    ! [A_503] : r1_xboole_0(A_503,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_1466])).

tff(c_1154,plain,(
    ! [B_451,A_452] :
      ( v4_relat_1(B_451,A_452)
      | ~ r1_tarski(k1_relat_1(B_451),A_452)
      | ~ v1_relat_1(B_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1164,plain,(
    ! [B_453] :
      ( v4_relat_1(B_453,k1_relat_1(B_453))
      | ~ v1_relat_1(B_453) ) ),
    inference(resolution,[status(thm)],[c_22,c_1154])).

tff(c_1168,plain,(
    ! [B_453] :
      ( k7_relat_1(B_453,k1_relat_1(B_453)) = B_453
      | ~ v1_relat_1(B_453) ) ),
    inference(resolution,[status(thm)],[c_1164,c_36])).

tff(c_1242,plain,(
    ! [C_471,A_472,B_473] :
      ( k7_relat_1(k7_relat_1(C_471,A_472),B_473) = k1_xboole_0
      | ~ r1_xboole_0(A_472,B_473)
      | ~ v1_relat_1(C_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1722,plain,(
    ! [B_550,B_551] :
      ( k7_relat_1(B_550,B_551) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_550),B_551)
      | ~ v1_relat_1(B_550)
      | ~ v1_relat_1(B_550) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_1242])).

tff(c_1753,plain,(
    ! [B_552] :
      ( k7_relat_1(B_552,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_552) ) ),
    inference(resolution,[status(thm)],[c_1473,c_1722])).

tff(c_1765,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1049,c_1753])).

tff(c_1764,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1050,c_1753])).

tff(c_1203,plain,(
    ! [A_460,B_461] :
      ( r1_xboole_0(A_460,B_461)
      | ~ r1_subset_1(A_460,B_461)
      | v1_xboole_0(B_461)
      | v1_xboole_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1354,plain,(
    ! [A_488,B_489] :
      ( k3_xboole_0(A_488,B_489) = k1_xboole_0
      | ~ r1_subset_1(A_488,B_489)
      | v1_xboole_0(B_489)
      | v1_xboole_0(A_488) ) ),
    inference(resolution,[status(thm)],[c_1203,c_6])).

tff(c_1360,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_1354])).

tff(c_1364,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_76,c_1360])).

tff(c_1268,plain,(
    ! [A_474,B_475,C_476] :
      ( k9_subset_1(A_474,B_475,C_476) = k3_xboole_0(B_475,C_476)
      | ~ m1_subset_1(C_476,k1_zfmisc_1(A_474)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1283,plain,(
    ! [B_475] : k9_subset_1('#skF_3',B_475,'#skF_6') = k3_xboole_0(B_475,'#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_1268])).

tff(c_1489,plain,(
    ! [D_507,B_505,C_510,E_509,A_508,F_506] :
      ( v1_funct_1(k1_tmap_1(A_508,B_505,C_510,D_507,E_509,F_506))
      | ~ m1_subset_1(F_506,k1_zfmisc_1(k2_zfmisc_1(D_507,B_505)))
      | ~ v1_funct_2(F_506,D_507,B_505)
      | ~ v1_funct_1(F_506)
      | ~ m1_subset_1(E_509,k1_zfmisc_1(k2_zfmisc_1(C_510,B_505)))
      | ~ v1_funct_2(E_509,C_510,B_505)
      | ~ v1_funct_1(E_509)
      | ~ m1_subset_1(D_507,k1_zfmisc_1(A_508))
      | v1_xboole_0(D_507)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(A_508))
      | v1_xboole_0(C_510)
      | v1_xboole_0(B_505)
      | v1_xboole_0(A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1494,plain,(
    ! [A_508,C_510,E_509] :
      ( v1_funct_1(k1_tmap_1(A_508,'#skF_4',C_510,'#skF_6',E_509,'#skF_8'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_509,k1_zfmisc_1(k2_zfmisc_1(C_510,'#skF_4')))
      | ~ v1_funct_2(E_509,C_510,'#skF_4')
      | ~ v1_funct_1(E_509)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_508))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_510,k1_zfmisc_1(A_508))
      | v1_xboole_0(C_510)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_508) ) ),
    inference(resolution,[status(thm)],[c_60,c_1489])).

tff(c_1500,plain,(
    ! [A_508,C_510,E_509] :
      ( v1_funct_1(k1_tmap_1(A_508,'#skF_4',C_510,'#skF_6',E_509,'#skF_8'))
      | ~ m1_subset_1(E_509,k1_zfmisc_1(k2_zfmisc_1(C_510,'#skF_4')))
      | ~ v1_funct_2(E_509,C_510,'#skF_4')
      | ~ v1_funct_1(E_509)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_508))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_510,k1_zfmisc_1(A_508))
      | v1_xboole_0(C_510)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1494])).

tff(c_1533,plain,(
    ! [A_515,C_516,E_517] :
      ( v1_funct_1(k1_tmap_1(A_515,'#skF_4',C_516,'#skF_6',E_517,'#skF_8'))
      | ~ m1_subset_1(E_517,k1_zfmisc_1(k2_zfmisc_1(C_516,'#skF_4')))
      | ~ v1_funct_2(E_517,C_516,'#skF_4')
      | ~ v1_funct_1(E_517)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_515))
      | ~ m1_subset_1(C_516,k1_zfmisc_1(A_515))
      | v1_xboole_0(C_516)
      | v1_xboole_0(A_515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1500])).

tff(c_1540,plain,(
    ! [A_515] :
      ( v1_funct_1(k1_tmap_1(A_515,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_515))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_515))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_515) ) ),
    inference(resolution,[status(thm)],[c_66,c_1533])).

tff(c_1548,plain,(
    ! [A_515] :
      ( v1_funct_1(k1_tmap_1(A_515,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_515))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_515))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_515) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1540])).

tff(c_1709,plain,(
    ! [A_549] :
      ( v1_funct_1(k1_tmap_1(A_549,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_549))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_549))
      | v1_xboole_0(A_549) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1548])).

tff(c_1716,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1709])).

tff(c_1720,plain,
    ( v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1716])).

tff(c_1721,plain,(
    v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1720])).

tff(c_1365,plain,(
    ! [A_490,B_491,C_492,D_493] :
      ( k2_partfun1(A_490,B_491,C_492,D_493) = k7_relat_1(C_492,D_493)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ v1_funct_1(C_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1372,plain,(
    ! [D_493] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_493) = k7_relat_1('#skF_7',D_493)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1365])).

tff(c_1379,plain,(
    ! [D_493] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_493) = k7_relat_1('#skF_7',D_493) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1372])).

tff(c_1370,plain,(
    ! [D_493] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_493) = k7_relat_1('#skF_8',D_493)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_60,c_1365])).

tff(c_1376,plain,(
    ! [D_493] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_493) = k7_relat_1('#skF_8',D_493) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1370])).

tff(c_1868,plain,(
    ! [F_568,C_573,D_572,A_569,E_570,B_571] :
      ( k2_partfun1(k4_subset_1(A_569,C_573,D_572),B_571,k1_tmap_1(A_569,B_571,C_573,D_572,E_570,F_568),D_572) = F_568
      | ~ m1_subset_1(k1_tmap_1(A_569,B_571,C_573,D_572,E_570,F_568),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_569,C_573,D_572),B_571)))
      | ~ v1_funct_2(k1_tmap_1(A_569,B_571,C_573,D_572,E_570,F_568),k4_subset_1(A_569,C_573,D_572),B_571)
      | ~ v1_funct_1(k1_tmap_1(A_569,B_571,C_573,D_572,E_570,F_568))
      | k2_partfun1(D_572,B_571,F_568,k9_subset_1(A_569,C_573,D_572)) != k2_partfun1(C_573,B_571,E_570,k9_subset_1(A_569,C_573,D_572))
      | ~ m1_subset_1(F_568,k1_zfmisc_1(k2_zfmisc_1(D_572,B_571)))
      | ~ v1_funct_2(F_568,D_572,B_571)
      | ~ v1_funct_1(F_568)
      | ~ m1_subset_1(E_570,k1_zfmisc_1(k2_zfmisc_1(C_573,B_571)))
      | ~ v1_funct_2(E_570,C_573,B_571)
      | ~ v1_funct_1(E_570)
      | ~ m1_subset_1(D_572,k1_zfmisc_1(A_569))
      | v1_xboole_0(D_572)
      | ~ m1_subset_1(C_573,k1_zfmisc_1(A_569))
      | v1_xboole_0(C_573)
      | v1_xboole_0(B_571)
      | v1_xboole_0(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3343,plain,(
    ! [D_750,C_753,A_751,F_749,B_748,E_752] :
      ( k2_partfun1(k4_subset_1(A_751,C_753,D_750),B_748,k1_tmap_1(A_751,B_748,C_753,D_750,E_752,F_749),D_750) = F_749
      | ~ v1_funct_2(k1_tmap_1(A_751,B_748,C_753,D_750,E_752,F_749),k4_subset_1(A_751,C_753,D_750),B_748)
      | ~ v1_funct_1(k1_tmap_1(A_751,B_748,C_753,D_750,E_752,F_749))
      | k2_partfun1(D_750,B_748,F_749,k9_subset_1(A_751,C_753,D_750)) != k2_partfun1(C_753,B_748,E_752,k9_subset_1(A_751,C_753,D_750))
      | ~ m1_subset_1(F_749,k1_zfmisc_1(k2_zfmisc_1(D_750,B_748)))
      | ~ v1_funct_2(F_749,D_750,B_748)
      | ~ v1_funct_1(F_749)
      | ~ m1_subset_1(E_752,k1_zfmisc_1(k2_zfmisc_1(C_753,B_748)))
      | ~ v1_funct_2(E_752,C_753,B_748)
      | ~ v1_funct_1(E_752)
      | ~ m1_subset_1(D_750,k1_zfmisc_1(A_751))
      | v1_xboole_0(D_750)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(A_751))
      | v1_xboole_0(C_753)
      | v1_xboole_0(B_748)
      | v1_xboole_0(A_751) ) ),
    inference(resolution,[status(thm)],[c_52,c_1868])).

tff(c_6147,plain,(
    ! [C_1001,A_999,D_998,B_996,E_1000,F_997] :
      ( k2_partfun1(k4_subset_1(A_999,C_1001,D_998),B_996,k1_tmap_1(A_999,B_996,C_1001,D_998,E_1000,F_997),D_998) = F_997
      | ~ v1_funct_1(k1_tmap_1(A_999,B_996,C_1001,D_998,E_1000,F_997))
      | k2_partfun1(D_998,B_996,F_997,k9_subset_1(A_999,C_1001,D_998)) != k2_partfun1(C_1001,B_996,E_1000,k9_subset_1(A_999,C_1001,D_998))
      | ~ m1_subset_1(F_997,k1_zfmisc_1(k2_zfmisc_1(D_998,B_996)))
      | ~ v1_funct_2(F_997,D_998,B_996)
      | ~ v1_funct_1(F_997)
      | ~ m1_subset_1(E_1000,k1_zfmisc_1(k2_zfmisc_1(C_1001,B_996)))
      | ~ v1_funct_2(E_1000,C_1001,B_996)
      | ~ v1_funct_1(E_1000)
      | ~ m1_subset_1(D_998,k1_zfmisc_1(A_999))
      | v1_xboole_0(D_998)
      | ~ m1_subset_1(C_1001,k1_zfmisc_1(A_999))
      | v1_xboole_0(C_1001)
      | v1_xboole_0(B_996)
      | v1_xboole_0(A_999) ) ),
    inference(resolution,[status(thm)],[c_54,c_3343])).

tff(c_6154,plain,(
    ! [A_999,C_1001,E_1000] :
      ( k2_partfun1(k4_subset_1(A_999,C_1001,'#skF_6'),'#skF_4',k1_tmap_1(A_999,'#skF_4',C_1001,'#skF_6',E_1000,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_999,'#skF_4',C_1001,'#skF_6',E_1000,'#skF_8'))
      | k2_partfun1(C_1001,'#skF_4',E_1000,k9_subset_1(A_999,C_1001,'#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1(A_999,C_1001,'#skF_6'))
      | ~ v1_funct_2('#skF_8','#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1000,k1_zfmisc_1(k2_zfmisc_1(C_1001,'#skF_4')))
      | ~ v1_funct_2(E_1000,C_1001,'#skF_4')
      | ~ v1_funct_1(E_1000)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_999))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1001,k1_zfmisc_1(A_999))
      | v1_xboole_0(C_1001)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_999) ) ),
    inference(resolution,[status(thm)],[c_60,c_6147])).

tff(c_6161,plain,(
    ! [A_999,C_1001,E_1000] :
      ( k2_partfun1(k4_subset_1(A_999,C_1001,'#skF_6'),'#skF_4',k1_tmap_1(A_999,'#skF_4',C_1001,'#skF_6',E_1000,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_999,'#skF_4',C_1001,'#skF_6',E_1000,'#skF_8'))
      | k2_partfun1(C_1001,'#skF_4',E_1000,k9_subset_1(A_999,C_1001,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_999,C_1001,'#skF_6'))
      | ~ m1_subset_1(E_1000,k1_zfmisc_1(k2_zfmisc_1(C_1001,'#skF_4')))
      | ~ v1_funct_2(E_1000,C_1001,'#skF_4')
      | ~ v1_funct_1(E_1000)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_999))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(C_1001,k1_zfmisc_1(A_999))
      | v1_xboole_0(C_1001)
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_999) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1376,c_6154])).

tff(c_11663,plain,(
    ! [A_1239,C_1240,E_1241] :
      ( k2_partfun1(k4_subset_1(A_1239,C_1240,'#skF_6'),'#skF_4',k1_tmap_1(A_1239,'#skF_4',C_1240,'#skF_6',E_1241,'#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1239,'#skF_4',C_1240,'#skF_6',E_1241,'#skF_8'))
      | k2_partfun1(C_1240,'#skF_4',E_1241,k9_subset_1(A_1239,C_1240,'#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1239,C_1240,'#skF_6'))
      | ~ m1_subset_1(E_1241,k1_zfmisc_1(k2_zfmisc_1(C_1240,'#skF_4')))
      | ~ v1_funct_2(E_1241,C_1240,'#skF_4')
      | ~ v1_funct_1(E_1241)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1239))
      | ~ m1_subset_1(C_1240,k1_zfmisc_1(A_1239))
      | v1_xboole_0(C_1240)
      | v1_xboole_0(A_1239) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_6161])).

tff(c_11673,plain,(
    ! [A_1239] :
      ( k2_partfun1(k4_subset_1(A_1239,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1239,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1239,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1(A_1239,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1239,'#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1239))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1239))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1239) ) ),
    inference(resolution,[status(thm)],[c_66,c_11663])).

tff(c_11684,plain,(
    ! [A_1239] :
      ( k2_partfun1(k4_subset_1(A_1239,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1239,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1239,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1239,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1239,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1239))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1239))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_1239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1379,c_11673])).

tff(c_14444,plain,(
    ! [A_1398] :
      ( k2_partfun1(k4_subset_1(A_1398,'#skF_5','#skF_6'),'#skF_4',k1_tmap_1(A_1398,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') = '#skF_8'
      | ~ v1_funct_1(k1_tmap_1(A_1398,'#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1398,'#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1(A_1398,'#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1398))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1398))
      | v1_xboole_0(A_1398) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_11684])).

tff(c_194,plain,(
    ! [C_253,A_254,B_255] :
      ( v1_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_206,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_194])).

tff(c_157,plain,(
    ! [A_245,B_246] :
      ( r2_hidden('#skF_2'(A_245,B_246),B_246)
      | r1_xboole_0(A_245,B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_169,plain,(
    ! [B_248,A_249] :
      ( ~ v1_xboole_0(B_248)
      | r1_xboole_0(A_249,B_248) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_174,plain,(
    ! [A_250,B_251] :
      ( k3_xboole_0(A_250,B_251) = k1_xboole_0
      | ~ v1_xboole_0(B_251) ) ),
    inference(resolution,[status(thm)],[c_169,c_6])).

tff(c_177,plain,(
    ! [A_250] : k3_xboole_0(A_250,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_174])).

tff(c_236,plain,(
    ! [A_265,B_266,C_267] :
      ( ~ r1_xboole_0(A_265,B_266)
      | ~ r2_hidden(C_267,B_266)
      | ~ r2_hidden(C_267,A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_295,plain,(
    ! [C_276,B_277,A_278] :
      ( ~ r2_hidden(C_276,B_277)
      | ~ r2_hidden(C_276,A_278)
      | k3_xboole_0(A_278,B_277) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_236])).

tff(c_511,plain,(
    ! [A_318,B_319,A_320] :
      ( ~ r2_hidden('#skF_2'(A_318,B_319),A_320)
      | k3_xboole_0(A_320,B_319) != k1_xboole_0
      | r1_xboole_0(A_318,B_319) ) ),
    inference(resolution,[status(thm)],[c_14,c_295])).

tff(c_520,plain,(
    ! [B_321,A_322] :
      ( k3_xboole_0(B_321,B_321) != k1_xboole_0
      | r1_xboole_0(A_322,B_321) ) ),
    inference(resolution,[status(thm)],[c_14,c_511])).

tff(c_527,plain,(
    ! [A_322] : r1_xboole_0(A_322,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_520])).

tff(c_246,plain,(
    ! [B_268,A_269] :
      ( v4_relat_1(B_268,A_269)
      | ~ r1_tarski(k1_relat_1(B_268),A_269)
      | ~ v1_relat_1(B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_256,plain,(
    ! [B_270] :
      ( v4_relat_1(B_270,k1_relat_1(B_270))
      | ~ v1_relat_1(B_270) ) ),
    inference(resolution,[status(thm)],[c_22,c_246])).

tff(c_260,plain,(
    ! [B_270] :
      ( k7_relat_1(B_270,k1_relat_1(B_270)) = B_270
      | ~ v1_relat_1(B_270) ) ),
    inference(resolution,[status(thm)],[c_256,c_36])).

tff(c_306,plain,(
    ! [C_282,A_283,B_284] :
      ( k7_relat_1(k7_relat_1(C_282,A_283),B_284) = k1_xboole_0
      | ~ r1_xboole_0(A_283,B_284)
      | ~ v1_relat_1(C_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_712,plain,(
    ! [B_361,B_362] :
      ( k7_relat_1(B_361,B_362) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_361),B_362)
      | ~ v1_relat_1(B_361)
      | ~ v1_relat_1(B_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_306])).

tff(c_756,plain,(
    ! [B_364] :
      ( k7_relat_1(B_364,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_364) ) ),
    inference(resolution,[status(thm)],[c_527,c_712])).

tff(c_768,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_206,c_756])).

tff(c_207,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_194])).

tff(c_767,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_207,c_756])).

tff(c_270,plain,(
    ! [A_272,B_273] :
      ( r1_xboole_0(A_272,B_273)
      | ~ r1_subset_1(A_272,B_273)
      | v1_xboole_0(B_273)
      | v1_xboole_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_467,plain,(
    ! [A_308,B_309] :
      ( k3_xboole_0(A_308,B_309) = k1_xboole_0
      | ~ r1_subset_1(A_308,B_309)
      | v1_xboole_0(B_309)
      | v1_xboole_0(A_308) ) ),
    inference(resolution,[status(thm)],[c_270,c_6])).

tff(c_473,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_467])).

tff(c_477,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_76,c_473])).

tff(c_383,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( k2_partfun1(A_293,B_294,C_295,D_296) = k7_relat_1(C_295,D_296)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ v1_funct_1(C_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_390,plain,(
    ! [D_296] :
      ( k2_partfun1('#skF_5','#skF_4','#skF_7',D_296) = k7_relat_1('#skF_7',D_296)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_383])).

tff(c_397,plain,(
    ! [D_296] : k2_partfun1('#skF_5','#skF_4','#skF_7',D_296) = k7_relat_1('#skF_7',D_296) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_390])).

tff(c_388,plain,(
    ! [D_296] :
      ( k2_partfun1('#skF_6','#skF_4','#skF_8',D_296) = k7_relat_1('#skF_8',D_296)
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_60,c_383])).

tff(c_394,plain,(
    ! [D_296] : k2_partfun1('#skF_6','#skF_4','#skF_8',D_296) = k7_relat_1('#skF_8',D_296) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_388])).

tff(c_348,plain,(
    ! [A_288,B_289,C_290] :
      ( k9_subset_1(A_288,B_289,C_290) = k3_xboole_0(B_289,C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(A_288)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_363,plain,(
    ! [B_289] : k9_subset_1('#skF_3',B_289,'#skF_6') = k3_xboole_0(B_289,'#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_348])).

tff(c_58,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_99,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_373,plain,(
    k2_partfun1('#skF_5','#skF_4','#skF_7',k3_xboole_0('#skF_5','#skF_6')) != k2_partfun1('#skF_6','#skF_4','#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_363,c_99])).

tff(c_1012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_767,c_477,c_477,c_397,c_394,c_373])).

tff(c_1013,plain,
    ( k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1153,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_6') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1013])).

tff(c_14467,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14444,c_1153])).

tff(c_14503,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_1765,c_1764,c_1364,c_1364,c_1283,c_1283,c_1721,c_14467])).

tff(c_14505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_14503])).

tff(c_14506,plain,(
    k2_partfun1(k4_subset_1('#skF_3','#skF_5','#skF_6'),'#skF_4',k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1013])).

tff(c_25388,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_3','#skF_5','#skF_6')) != k7_relat_1('#skF_8',k9_subset_1('#skF_3','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_25368,c_14506])).

tff(c_25417,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_15067,c_15066,c_14722,c_14722,c_14615,c_14615,c_15405,c_25388])).

tff(c_25419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_25417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.17/6.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.17/6.80  
% 15.17/6.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.17/6.80  %$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 15.17/6.80  
% 15.17/6.80  %Foreground sorts:
% 15.17/6.80  
% 15.17/6.80  
% 15.17/6.80  %Background operators:
% 15.17/6.80  
% 15.17/6.80  
% 15.17/6.80  %Foreground operators:
% 15.17/6.80  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 15.17/6.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.17/6.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.17/6.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.17/6.80  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.17/6.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.17/6.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.17/6.80  tff('#skF_7', type, '#skF_7': $i).
% 15.17/6.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.17/6.80  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 15.17/6.80  tff('#skF_5', type, '#skF_5': $i).
% 15.17/6.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.17/6.80  tff('#skF_6', type, '#skF_6': $i).
% 15.17/6.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.17/6.80  tff('#skF_3', type, '#skF_3': $i).
% 15.17/6.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.17/6.80  tff('#skF_8', type, '#skF_8': $i).
% 15.17/6.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.17/6.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.17/6.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.17/6.80  tff('#skF_4', type, '#skF_4': $i).
% 15.17/6.80  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.17/6.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.17/6.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.17/6.80  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.17/6.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.17/6.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.17/6.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.17/6.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.17/6.80  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.17/6.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.17/6.80  
% 15.17/6.83  tff(f_230, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 15.17/6.83  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.17/6.83  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.17/6.83  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 15.17/6.83  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 15.17/6.83  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.17/6.83  tff(f_60, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.17/6.83  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 15.17/6.83  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 15.17/6.83  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 15.17/6.83  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 15.17/6.83  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 15.17/6.83  tff(f_188, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 15.17/6.83  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 15.17/6.83  tff(f_154, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 15.17/6.83  tff(c_84, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_1037, plain, (![C_423, A_424, B_425]: (v1_relat_1(C_423) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.17/6.83  tff(c_1049, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_1037])).
% 15.17/6.83  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.17/6.83  tff(c_1114, plain, (![A_440, B_441]: (r2_hidden('#skF_2'(A_440, B_441), A_440) | r1_xboole_0(A_440, B_441))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.17/6.83  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.17/6.83  tff(c_1119, plain, (![A_442, B_443]: (~v1_xboole_0(A_442) | r1_xboole_0(A_442, B_443))), inference(resolution, [status(thm)], [c_1114, c_2])).
% 15.17/6.83  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.17/6.83  tff(c_1133, plain, (![A_446, B_447]: (k3_xboole_0(A_446, B_447)=k1_xboole_0 | ~v1_xboole_0(A_446))), inference(resolution, [status(thm)], [c_1119, c_6])).
% 15.17/6.83  tff(c_1136, plain, (![B_447]: (k3_xboole_0(k1_xboole_0, B_447)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1133])).
% 15.17/6.83  tff(c_14, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.17/6.83  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.17/6.83  tff(c_14532, plain, (![A_1403, B_1404, C_1405]: (~r1_xboole_0(A_1403, B_1404) | ~r2_hidden(C_1405, B_1404) | ~r2_hidden(C_1405, A_1403))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.17/6.83  tff(c_14573, plain, (![C_1410, B_1411, A_1412]: (~r2_hidden(C_1410, B_1411) | ~r2_hidden(C_1410, A_1412) | k3_xboole_0(A_1412, B_1411)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_14532])).
% 15.17/6.83  tff(c_14739, plain, (![A_1440, B_1441, A_1442]: (~r2_hidden('#skF_2'(A_1440, B_1441), A_1442) | k3_xboole_0(A_1442, B_1441)!=k1_xboole_0 | r1_xboole_0(A_1440, B_1441))), inference(resolution, [status(thm)], [c_14, c_14573])).
% 15.17/6.83  tff(c_14753, plain, (![B_1443, A_1444]: (k3_xboole_0(B_1443, B_1443)!=k1_xboole_0 | r1_xboole_0(A_1444, B_1443))), inference(resolution, [status(thm)], [c_14, c_14739])).
% 15.17/6.83  tff(c_14760, plain, (![A_1444]: (r1_xboole_0(A_1444, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1136, c_14753])).
% 15.17/6.83  tff(c_22, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.17/6.83  tff(c_14508, plain, (![B_1399, A_1400]: (v4_relat_1(B_1399, A_1400) | ~r1_tarski(k1_relat_1(B_1399), A_1400) | ~v1_relat_1(B_1399))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.17/6.83  tff(c_14518, plain, (![B_1401]: (v4_relat_1(B_1401, k1_relat_1(B_1401)) | ~v1_relat_1(B_1401))), inference(resolution, [status(thm)], [c_22, c_14508])).
% 15.17/6.83  tff(c_36, plain, (![B_25, A_24]: (k7_relat_1(B_25, A_24)=B_25 | ~v4_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.17/6.83  tff(c_14522, plain, (![B_1401]: (k7_relat_1(B_1401, k1_relat_1(B_1401))=B_1401 | ~v1_relat_1(B_1401))), inference(resolution, [status(thm)], [c_14518, c_36])).
% 15.17/6.83  tff(c_14685, plain, (![C_1431, A_1432, B_1433]: (k7_relat_1(k7_relat_1(C_1431, A_1432), B_1433)=k1_xboole_0 | ~r1_xboole_0(A_1432, B_1433) | ~v1_relat_1(C_1431))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.17/6.83  tff(c_15024, plain, (![B_1490, B_1491]: (k7_relat_1(B_1490, B_1491)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_1490), B_1491) | ~v1_relat_1(B_1490) | ~v1_relat_1(B_1490))), inference(superposition, [status(thm), theory('equality')], [c_14522, c_14685])).
% 15.17/6.83  tff(c_15055, plain, (![B_1492]: (k7_relat_1(B_1492, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_1492))), inference(resolution, [status(thm)], [c_14760, c_15024])).
% 15.17/6.83  tff(c_15067, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1049, c_15055])).
% 15.17/6.83  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_1050, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_1037])).
% 15.17/6.83  tff(c_15066, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1050, c_15055])).
% 15.17/6.83  tff(c_80, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_76, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_72, plain, (r1_subset_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_14561, plain, (![A_1408, B_1409]: (r1_xboole_0(A_1408, B_1409) | ~r1_subset_1(A_1408, B_1409) | v1_xboole_0(B_1409) | v1_xboole_0(A_1408))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.17/6.83  tff(c_14712, plain, (![A_1436, B_1437]: (k3_xboole_0(A_1436, B_1437)=k1_xboole_0 | ~r1_subset_1(A_1436, B_1437) | v1_xboole_0(B_1437) | v1_xboole_0(A_1436))), inference(resolution, [status(thm)], [c_14561, c_6])).
% 15.17/6.83  tff(c_14718, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_14712])).
% 15.17/6.83  tff(c_14722, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_76, c_14718])).
% 15.17/6.83  tff(c_14600, plain, (![A_1419, B_1420, C_1421]: (k9_subset_1(A_1419, B_1420, C_1421)=k3_xboole_0(B_1420, C_1421) | ~m1_subset_1(C_1421, k1_zfmisc_1(A_1419)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.17/6.83  tff(c_14615, plain, (![B_1420]: (k9_subset_1('#skF_3', B_1420, '#skF_6')=k3_xboole_0(B_1420, '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_14600])).
% 15.17/6.83  tff(c_70, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_68, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_82, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_14905, plain, (![C_1463, D_1460, B_1458, A_1461, F_1459, E_1462]: (v1_funct_1(k1_tmap_1(A_1461, B_1458, C_1463, D_1460, E_1462, F_1459)) | ~m1_subset_1(F_1459, k1_zfmisc_1(k2_zfmisc_1(D_1460, B_1458))) | ~v1_funct_2(F_1459, D_1460, B_1458) | ~v1_funct_1(F_1459) | ~m1_subset_1(E_1462, k1_zfmisc_1(k2_zfmisc_1(C_1463, B_1458))) | ~v1_funct_2(E_1462, C_1463, B_1458) | ~v1_funct_1(E_1462) | ~m1_subset_1(D_1460, k1_zfmisc_1(A_1461)) | v1_xboole_0(D_1460) | ~m1_subset_1(C_1463, k1_zfmisc_1(A_1461)) | v1_xboole_0(C_1463) | v1_xboole_0(B_1458) | v1_xboole_0(A_1461))), inference(cnfTransformation, [status(thm)], [f_188])).
% 15.17/6.83  tff(c_14910, plain, (![A_1461, C_1463, E_1462]: (v1_funct_1(k1_tmap_1(A_1461, '#skF_4', C_1463, '#skF_6', E_1462, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1462, k1_zfmisc_1(k2_zfmisc_1(C_1463, '#skF_4'))) | ~v1_funct_2(E_1462, C_1463, '#skF_4') | ~v1_funct_1(E_1462) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1461)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1463, k1_zfmisc_1(A_1461)) | v1_xboole_0(C_1463) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1461))), inference(resolution, [status(thm)], [c_60, c_14905])).
% 15.17/6.83  tff(c_14916, plain, (![A_1461, C_1463, E_1462]: (v1_funct_1(k1_tmap_1(A_1461, '#skF_4', C_1463, '#skF_6', E_1462, '#skF_8')) | ~m1_subset_1(E_1462, k1_zfmisc_1(k2_zfmisc_1(C_1463, '#skF_4'))) | ~v1_funct_2(E_1462, C_1463, '#skF_4') | ~v1_funct_1(E_1462) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1461)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1463, k1_zfmisc_1(A_1461)) | v1_xboole_0(C_1463) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1461))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_14910])).
% 15.17/6.83  tff(c_15203, plain, (![A_1513, C_1514, E_1515]: (v1_funct_1(k1_tmap_1(A_1513, '#skF_4', C_1514, '#skF_6', E_1515, '#skF_8')) | ~m1_subset_1(E_1515, k1_zfmisc_1(k2_zfmisc_1(C_1514, '#skF_4'))) | ~v1_funct_2(E_1515, C_1514, '#skF_4') | ~v1_funct_1(E_1515) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1513)) | ~m1_subset_1(C_1514, k1_zfmisc_1(A_1513)) | v1_xboole_0(C_1514) | v1_xboole_0(A_1513))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_14916])).
% 15.17/6.83  tff(c_15213, plain, (![A_1513]: (v1_funct_1(k1_tmap_1(A_1513, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1513)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1513)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1513))), inference(resolution, [status(thm)], [c_66, c_15203])).
% 15.17/6.83  tff(c_15224, plain, (![A_1513]: (v1_funct_1(k1_tmap_1(A_1513, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1513)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1513)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1513))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_15213])).
% 15.17/6.83  tff(c_15393, plain, (![A_1560]: (v1_funct_1(k1_tmap_1(A_1560, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1560)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1560)) | v1_xboole_0(A_1560))), inference(negUnitSimplification, [status(thm)], [c_80, c_15224])).
% 15.17/6.83  tff(c_15400, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_15393])).
% 15.17/6.83  tff(c_15404, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_15400])).
% 15.17/6.83  tff(c_15405, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_15404])).
% 15.17/6.83  tff(c_14803, plain, (![A_1450, B_1451, C_1452, D_1453]: (k2_partfun1(A_1450, B_1451, C_1452, D_1453)=k7_relat_1(C_1452, D_1453) | ~m1_subset_1(C_1452, k1_zfmisc_1(k2_zfmisc_1(A_1450, B_1451))) | ~v1_funct_1(C_1452))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.17/6.83  tff(c_14810, plain, (![D_1453]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1453)=k7_relat_1('#skF_7', D_1453) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_14803])).
% 15.17/6.83  tff(c_14817, plain, (![D_1453]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_1453)=k7_relat_1('#skF_7', D_1453))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_14810])).
% 15.17/6.83  tff(c_14808, plain, (![D_1453]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1453)=k7_relat_1('#skF_8', D_1453) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_14803])).
% 15.17/6.83  tff(c_14814, plain, (![D_1453]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_1453)=k7_relat_1('#skF_8', D_1453))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_14808])).
% 15.17/6.83  tff(c_54, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (v1_funct_2(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k4_subset_1(A_162, C_164, D_165), B_163) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_188])).
% 15.17/6.83  tff(c_52, plain, (![E_166, F_167, B_163, D_165, A_162, C_164]: (m1_subset_1(k1_tmap_1(A_162, B_163, C_164, D_165, E_166, F_167), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_162, C_164, D_165), B_163))) | ~m1_subset_1(F_167, k1_zfmisc_1(k2_zfmisc_1(D_165, B_163))) | ~v1_funct_2(F_167, D_165, B_163) | ~v1_funct_1(F_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(C_164, B_163))) | ~v1_funct_2(E_166, C_164, B_163) | ~v1_funct_1(E_166) | ~m1_subset_1(D_165, k1_zfmisc_1(A_162)) | v1_xboole_0(D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(A_162)) | v1_xboole_0(C_164) | v1_xboole_0(B_163) | v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_188])).
% 15.17/6.83  tff(c_15173, plain, (![A_1504, C_1508, D_1507, E_1505, B_1506, F_1503]: (k2_partfun1(k4_subset_1(A_1504, C_1508, D_1507), B_1506, k1_tmap_1(A_1504, B_1506, C_1508, D_1507, E_1505, F_1503), C_1508)=E_1505 | ~m1_subset_1(k1_tmap_1(A_1504, B_1506, C_1508, D_1507, E_1505, F_1503), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1504, C_1508, D_1507), B_1506))) | ~v1_funct_2(k1_tmap_1(A_1504, B_1506, C_1508, D_1507, E_1505, F_1503), k4_subset_1(A_1504, C_1508, D_1507), B_1506) | ~v1_funct_1(k1_tmap_1(A_1504, B_1506, C_1508, D_1507, E_1505, F_1503)) | k2_partfun1(D_1507, B_1506, F_1503, k9_subset_1(A_1504, C_1508, D_1507))!=k2_partfun1(C_1508, B_1506, E_1505, k9_subset_1(A_1504, C_1508, D_1507)) | ~m1_subset_1(F_1503, k1_zfmisc_1(k2_zfmisc_1(D_1507, B_1506))) | ~v1_funct_2(F_1503, D_1507, B_1506) | ~v1_funct_1(F_1503) | ~m1_subset_1(E_1505, k1_zfmisc_1(k2_zfmisc_1(C_1508, B_1506))) | ~v1_funct_2(E_1505, C_1508, B_1506) | ~v1_funct_1(E_1505) | ~m1_subset_1(D_1507, k1_zfmisc_1(A_1504)) | v1_xboole_0(D_1507) | ~m1_subset_1(C_1508, k1_zfmisc_1(A_1504)) | v1_xboole_0(C_1508) | v1_xboole_0(B_1506) | v1_xboole_0(A_1504))), inference(cnfTransformation, [status(thm)], [f_154])).
% 15.17/6.83  tff(c_16798, plain, (![E_1722, B_1718, C_1723, D_1720, A_1721, F_1719]: (k2_partfun1(k4_subset_1(A_1721, C_1723, D_1720), B_1718, k1_tmap_1(A_1721, B_1718, C_1723, D_1720, E_1722, F_1719), C_1723)=E_1722 | ~v1_funct_2(k1_tmap_1(A_1721, B_1718, C_1723, D_1720, E_1722, F_1719), k4_subset_1(A_1721, C_1723, D_1720), B_1718) | ~v1_funct_1(k1_tmap_1(A_1721, B_1718, C_1723, D_1720, E_1722, F_1719)) | k2_partfun1(D_1720, B_1718, F_1719, k9_subset_1(A_1721, C_1723, D_1720))!=k2_partfun1(C_1723, B_1718, E_1722, k9_subset_1(A_1721, C_1723, D_1720)) | ~m1_subset_1(F_1719, k1_zfmisc_1(k2_zfmisc_1(D_1720, B_1718))) | ~v1_funct_2(F_1719, D_1720, B_1718) | ~v1_funct_1(F_1719) | ~m1_subset_1(E_1722, k1_zfmisc_1(k2_zfmisc_1(C_1723, B_1718))) | ~v1_funct_2(E_1722, C_1723, B_1718) | ~v1_funct_1(E_1722) | ~m1_subset_1(D_1720, k1_zfmisc_1(A_1721)) | v1_xboole_0(D_1720) | ~m1_subset_1(C_1723, k1_zfmisc_1(A_1721)) | v1_xboole_0(C_1723) | v1_xboole_0(B_1718) | v1_xboole_0(A_1721))), inference(resolution, [status(thm)], [c_52, c_15173])).
% 15.17/6.83  tff(c_19483, plain, (![A_1942, E_1943, C_1944, B_1939, F_1940, D_1941]: (k2_partfun1(k4_subset_1(A_1942, C_1944, D_1941), B_1939, k1_tmap_1(A_1942, B_1939, C_1944, D_1941, E_1943, F_1940), C_1944)=E_1943 | ~v1_funct_1(k1_tmap_1(A_1942, B_1939, C_1944, D_1941, E_1943, F_1940)) | k2_partfun1(D_1941, B_1939, F_1940, k9_subset_1(A_1942, C_1944, D_1941))!=k2_partfun1(C_1944, B_1939, E_1943, k9_subset_1(A_1942, C_1944, D_1941)) | ~m1_subset_1(F_1940, k1_zfmisc_1(k2_zfmisc_1(D_1941, B_1939))) | ~v1_funct_2(F_1940, D_1941, B_1939) | ~v1_funct_1(F_1940) | ~m1_subset_1(E_1943, k1_zfmisc_1(k2_zfmisc_1(C_1944, B_1939))) | ~v1_funct_2(E_1943, C_1944, B_1939) | ~v1_funct_1(E_1943) | ~m1_subset_1(D_1941, k1_zfmisc_1(A_1942)) | v1_xboole_0(D_1941) | ~m1_subset_1(C_1944, k1_zfmisc_1(A_1942)) | v1_xboole_0(C_1944) | v1_xboole_0(B_1939) | v1_xboole_0(A_1942))), inference(resolution, [status(thm)], [c_54, c_16798])).
% 15.17/6.83  tff(c_19490, plain, (![A_1942, C_1944, E_1943]: (k2_partfun1(k4_subset_1(A_1942, C_1944, '#skF_6'), '#skF_4', k1_tmap_1(A_1942, '#skF_4', C_1944, '#skF_6', E_1943, '#skF_8'), C_1944)=E_1943 | ~v1_funct_1(k1_tmap_1(A_1942, '#skF_4', C_1944, '#skF_6', E_1943, '#skF_8')) | k2_partfun1(C_1944, '#skF_4', E_1943, k9_subset_1(A_1942, C_1944, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_1942, C_1944, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1943, k1_zfmisc_1(k2_zfmisc_1(C_1944, '#skF_4'))) | ~v1_funct_2(E_1943, C_1944, '#skF_4') | ~v1_funct_1(E_1943) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1942)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1944, k1_zfmisc_1(A_1942)) | v1_xboole_0(C_1944) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1942))), inference(resolution, [status(thm)], [c_60, c_19483])).
% 15.17/6.83  tff(c_19497, plain, (![A_1942, C_1944, E_1943]: (k2_partfun1(k4_subset_1(A_1942, C_1944, '#skF_6'), '#skF_4', k1_tmap_1(A_1942, '#skF_4', C_1944, '#skF_6', E_1943, '#skF_8'), C_1944)=E_1943 | ~v1_funct_1(k1_tmap_1(A_1942, '#skF_4', C_1944, '#skF_6', E_1943, '#skF_8')) | k2_partfun1(C_1944, '#skF_4', E_1943, k9_subset_1(A_1942, C_1944, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1942, C_1944, '#skF_6')) | ~m1_subset_1(E_1943, k1_zfmisc_1(k2_zfmisc_1(C_1944, '#skF_4'))) | ~v1_funct_2(E_1943, C_1944, '#skF_4') | ~v1_funct_1(E_1943) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1942)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1944, k1_zfmisc_1(A_1942)) | v1_xboole_0(C_1944) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1942))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_14814, c_19490])).
% 15.17/6.83  tff(c_25343, plain, (![A_2177, C_2178, E_2179]: (k2_partfun1(k4_subset_1(A_2177, C_2178, '#skF_6'), '#skF_4', k1_tmap_1(A_2177, '#skF_4', C_2178, '#skF_6', E_2179, '#skF_8'), C_2178)=E_2179 | ~v1_funct_1(k1_tmap_1(A_2177, '#skF_4', C_2178, '#skF_6', E_2179, '#skF_8')) | k2_partfun1(C_2178, '#skF_4', E_2179, k9_subset_1(A_2177, C_2178, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2177, C_2178, '#skF_6')) | ~m1_subset_1(E_2179, k1_zfmisc_1(k2_zfmisc_1(C_2178, '#skF_4'))) | ~v1_funct_2(E_2179, C_2178, '#skF_4') | ~v1_funct_1(E_2179) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2177)) | ~m1_subset_1(C_2178, k1_zfmisc_1(A_2177)) | v1_xboole_0(C_2178) | v1_xboole_0(A_2177))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_19497])).
% 15.17/6.83  tff(c_25353, plain, (![A_2177]: (k2_partfun1(k4_subset_1(A_2177, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2177, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2177, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_2177, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2177, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2177)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2177)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2177))), inference(resolution, [status(thm)], [c_66, c_25343])).
% 15.17/6.83  tff(c_25364, plain, (![A_2177]: (k2_partfun1(k4_subset_1(A_2177, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2177, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2177, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_2177, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2177, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2177)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2177)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_2177))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_14817, c_25353])).
% 15.17/6.83  tff(c_25368, plain, (![A_2186]: (k2_partfun1(k4_subset_1(A_2186, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_2186, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_2186, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_2186, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_2186, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2186)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2186)) | v1_xboole_0(A_2186))), inference(negUnitSimplification, [status(thm)], [c_80, c_25364])).
% 15.17/6.83  tff(c_1178, plain, (![A_455, B_456, C_457]: (~r1_xboole_0(A_455, B_456) | ~r2_hidden(C_457, B_456) | ~r2_hidden(C_457, A_455))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.17/6.83  tff(c_1215, plain, (![C_462, B_463, A_464]: (~r2_hidden(C_462, B_463) | ~r2_hidden(C_462, A_464) | k3_xboole_0(A_464, B_463)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1178])).
% 15.17/6.83  tff(c_1457, plain, (![A_499, B_500, A_501]: (~r2_hidden('#skF_2'(A_499, B_500), A_501) | k3_xboole_0(A_501, B_500)!=k1_xboole_0 | r1_xboole_0(A_499, B_500))), inference(resolution, [status(thm)], [c_14, c_1215])).
% 15.17/6.83  tff(c_1466, plain, (![B_502, A_503]: (k3_xboole_0(B_502, B_502)!=k1_xboole_0 | r1_xboole_0(A_503, B_502))), inference(resolution, [status(thm)], [c_14, c_1457])).
% 15.17/6.83  tff(c_1473, plain, (![A_503]: (r1_xboole_0(A_503, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1136, c_1466])).
% 15.17/6.83  tff(c_1154, plain, (![B_451, A_452]: (v4_relat_1(B_451, A_452) | ~r1_tarski(k1_relat_1(B_451), A_452) | ~v1_relat_1(B_451))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.17/6.83  tff(c_1164, plain, (![B_453]: (v4_relat_1(B_453, k1_relat_1(B_453)) | ~v1_relat_1(B_453))), inference(resolution, [status(thm)], [c_22, c_1154])).
% 15.17/6.83  tff(c_1168, plain, (![B_453]: (k7_relat_1(B_453, k1_relat_1(B_453))=B_453 | ~v1_relat_1(B_453))), inference(resolution, [status(thm)], [c_1164, c_36])).
% 15.17/6.83  tff(c_1242, plain, (![C_471, A_472, B_473]: (k7_relat_1(k7_relat_1(C_471, A_472), B_473)=k1_xboole_0 | ~r1_xboole_0(A_472, B_473) | ~v1_relat_1(C_471))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.17/6.83  tff(c_1722, plain, (![B_550, B_551]: (k7_relat_1(B_550, B_551)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_550), B_551) | ~v1_relat_1(B_550) | ~v1_relat_1(B_550))), inference(superposition, [status(thm), theory('equality')], [c_1168, c_1242])).
% 15.17/6.83  tff(c_1753, plain, (![B_552]: (k7_relat_1(B_552, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_552))), inference(resolution, [status(thm)], [c_1473, c_1722])).
% 15.17/6.83  tff(c_1765, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1049, c_1753])).
% 15.17/6.83  tff(c_1764, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1050, c_1753])).
% 15.17/6.83  tff(c_1203, plain, (![A_460, B_461]: (r1_xboole_0(A_460, B_461) | ~r1_subset_1(A_460, B_461) | v1_xboole_0(B_461) | v1_xboole_0(A_460))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.17/6.83  tff(c_1354, plain, (![A_488, B_489]: (k3_xboole_0(A_488, B_489)=k1_xboole_0 | ~r1_subset_1(A_488, B_489) | v1_xboole_0(B_489) | v1_xboole_0(A_488))), inference(resolution, [status(thm)], [c_1203, c_6])).
% 15.17/6.83  tff(c_1360, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_1354])).
% 15.17/6.83  tff(c_1364, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_76, c_1360])).
% 15.17/6.83  tff(c_1268, plain, (![A_474, B_475, C_476]: (k9_subset_1(A_474, B_475, C_476)=k3_xboole_0(B_475, C_476) | ~m1_subset_1(C_476, k1_zfmisc_1(A_474)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.17/6.83  tff(c_1283, plain, (![B_475]: (k9_subset_1('#skF_3', B_475, '#skF_6')=k3_xboole_0(B_475, '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_1268])).
% 15.17/6.83  tff(c_1489, plain, (![D_507, B_505, C_510, E_509, A_508, F_506]: (v1_funct_1(k1_tmap_1(A_508, B_505, C_510, D_507, E_509, F_506)) | ~m1_subset_1(F_506, k1_zfmisc_1(k2_zfmisc_1(D_507, B_505))) | ~v1_funct_2(F_506, D_507, B_505) | ~v1_funct_1(F_506) | ~m1_subset_1(E_509, k1_zfmisc_1(k2_zfmisc_1(C_510, B_505))) | ~v1_funct_2(E_509, C_510, B_505) | ~v1_funct_1(E_509) | ~m1_subset_1(D_507, k1_zfmisc_1(A_508)) | v1_xboole_0(D_507) | ~m1_subset_1(C_510, k1_zfmisc_1(A_508)) | v1_xboole_0(C_510) | v1_xboole_0(B_505) | v1_xboole_0(A_508))), inference(cnfTransformation, [status(thm)], [f_188])).
% 15.17/6.83  tff(c_1494, plain, (![A_508, C_510, E_509]: (v1_funct_1(k1_tmap_1(A_508, '#skF_4', C_510, '#skF_6', E_509, '#skF_8')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_509, k1_zfmisc_1(k2_zfmisc_1(C_510, '#skF_4'))) | ~v1_funct_2(E_509, C_510, '#skF_4') | ~v1_funct_1(E_509) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_508)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_510, k1_zfmisc_1(A_508)) | v1_xboole_0(C_510) | v1_xboole_0('#skF_4') | v1_xboole_0(A_508))), inference(resolution, [status(thm)], [c_60, c_1489])).
% 15.17/6.83  tff(c_1500, plain, (![A_508, C_510, E_509]: (v1_funct_1(k1_tmap_1(A_508, '#skF_4', C_510, '#skF_6', E_509, '#skF_8')) | ~m1_subset_1(E_509, k1_zfmisc_1(k2_zfmisc_1(C_510, '#skF_4'))) | ~v1_funct_2(E_509, C_510, '#skF_4') | ~v1_funct_1(E_509) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_508)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_510, k1_zfmisc_1(A_508)) | v1_xboole_0(C_510) | v1_xboole_0('#skF_4') | v1_xboole_0(A_508))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1494])).
% 15.17/6.83  tff(c_1533, plain, (![A_515, C_516, E_517]: (v1_funct_1(k1_tmap_1(A_515, '#skF_4', C_516, '#skF_6', E_517, '#skF_8')) | ~m1_subset_1(E_517, k1_zfmisc_1(k2_zfmisc_1(C_516, '#skF_4'))) | ~v1_funct_2(E_517, C_516, '#skF_4') | ~v1_funct_1(E_517) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_515)) | ~m1_subset_1(C_516, k1_zfmisc_1(A_515)) | v1_xboole_0(C_516) | v1_xboole_0(A_515))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1500])).
% 15.17/6.83  tff(c_1540, plain, (![A_515]: (v1_funct_1(k1_tmap_1(A_515, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_515)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_515)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_515))), inference(resolution, [status(thm)], [c_66, c_1533])).
% 15.17/6.83  tff(c_1548, plain, (![A_515]: (v1_funct_1(k1_tmap_1(A_515, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_515)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_515)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_515))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1540])).
% 15.17/6.83  tff(c_1709, plain, (![A_549]: (v1_funct_1(k1_tmap_1(A_549, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_549)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_549)) | v1_xboole_0(A_549))), inference(negUnitSimplification, [status(thm)], [c_80, c_1548])).
% 15.17/6.83  tff(c_1716, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1709])).
% 15.17/6.83  tff(c_1720, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1716])).
% 15.17/6.83  tff(c_1721, plain, (v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_1720])).
% 15.17/6.83  tff(c_1365, plain, (![A_490, B_491, C_492, D_493]: (k2_partfun1(A_490, B_491, C_492, D_493)=k7_relat_1(C_492, D_493) | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~v1_funct_1(C_492))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.17/6.83  tff(c_1372, plain, (![D_493]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_493)=k7_relat_1('#skF_7', D_493) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1365])).
% 15.17/6.83  tff(c_1379, plain, (![D_493]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_493)=k7_relat_1('#skF_7', D_493))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1372])).
% 15.17/6.83  tff(c_1370, plain, (![D_493]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_493)=k7_relat_1('#skF_8', D_493) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_1365])).
% 15.17/6.83  tff(c_1376, plain, (![D_493]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_493)=k7_relat_1('#skF_8', D_493))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1370])).
% 15.17/6.83  tff(c_1868, plain, (![F_568, C_573, D_572, A_569, E_570, B_571]: (k2_partfun1(k4_subset_1(A_569, C_573, D_572), B_571, k1_tmap_1(A_569, B_571, C_573, D_572, E_570, F_568), D_572)=F_568 | ~m1_subset_1(k1_tmap_1(A_569, B_571, C_573, D_572, E_570, F_568), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_569, C_573, D_572), B_571))) | ~v1_funct_2(k1_tmap_1(A_569, B_571, C_573, D_572, E_570, F_568), k4_subset_1(A_569, C_573, D_572), B_571) | ~v1_funct_1(k1_tmap_1(A_569, B_571, C_573, D_572, E_570, F_568)) | k2_partfun1(D_572, B_571, F_568, k9_subset_1(A_569, C_573, D_572))!=k2_partfun1(C_573, B_571, E_570, k9_subset_1(A_569, C_573, D_572)) | ~m1_subset_1(F_568, k1_zfmisc_1(k2_zfmisc_1(D_572, B_571))) | ~v1_funct_2(F_568, D_572, B_571) | ~v1_funct_1(F_568) | ~m1_subset_1(E_570, k1_zfmisc_1(k2_zfmisc_1(C_573, B_571))) | ~v1_funct_2(E_570, C_573, B_571) | ~v1_funct_1(E_570) | ~m1_subset_1(D_572, k1_zfmisc_1(A_569)) | v1_xboole_0(D_572) | ~m1_subset_1(C_573, k1_zfmisc_1(A_569)) | v1_xboole_0(C_573) | v1_xboole_0(B_571) | v1_xboole_0(A_569))), inference(cnfTransformation, [status(thm)], [f_154])).
% 15.17/6.83  tff(c_3343, plain, (![D_750, C_753, A_751, F_749, B_748, E_752]: (k2_partfun1(k4_subset_1(A_751, C_753, D_750), B_748, k1_tmap_1(A_751, B_748, C_753, D_750, E_752, F_749), D_750)=F_749 | ~v1_funct_2(k1_tmap_1(A_751, B_748, C_753, D_750, E_752, F_749), k4_subset_1(A_751, C_753, D_750), B_748) | ~v1_funct_1(k1_tmap_1(A_751, B_748, C_753, D_750, E_752, F_749)) | k2_partfun1(D_750, B_748, F_749, k9_subset_1(A_751, C_753, D_750))!=k2_partfun1(C_753, B_748, E_752, k9_subset_1(A_751, C_753, D_750)) | ~m1_subset_1(F_749, k1_zfmisc_1(k2_zfmisc_1(D_750, B_748))) | ~v1_funct_2(F_749, D_750, B_748) | ~v1_funct_1(F_749) | ~m1_subset_1(E_752, k1_zfmisc_1(k2_zfmisc_1(C_753, B_748))) | ~v1_funct_2(E_752, C_753, B_748) | ~v1_funct_1(E_752) | ~m1_subset_1(D_750, k1_zfmisc_1(A_751)) | v1_xboole_0(D_750) | ~m1_subset_1(C_753, k1_zfmisc_1(A_751)) | v1_xboole_0(C_753) | v1_xboole_0(B_748) | v1_xboole_0(A_751))), inference(resolution, [status(thm)], [c_52, c_1868])).
% 15.17/6.83  tff(c_6147, plain, (![C_1001, A_999, D_998, B_996, E_1000, F_997]: (k2_partfun1(k4_subset_1(A_999, C_1001, D_998), B_996, k1_tmap_1(A_999, B_996, C_1001, D_998, E_1000, F_997), D_998)=F_997 | ~v1_funct_1(k1_tmap_1(A_999, B_996, C_1001, D_998, E_1000, F_997)) | k2_partfun1(D_998, B_996, F_997, k9_subset_1(A_999, C_1001, D_998))!=k2_partfun1(C_1001, B_996, E_1000, k9_subset_1(A_999, C_1001, D_998)) | ~m1_subset_1(F_997, k1_zfmisc_1(k2_zfmisc_1(D_998, B_996))) | ~v1_funct_2(F_997, D_998, B_996) | ~v1_funct_1(F_997) | ~m1_subset_1(E_1000, k1_zfmisc_1(k2_zfmisc_1(C_1001, B_996))) | ~v1_funct_2(E_1000, C_1001, B_996) | ~v1_funct_1(E_1000) | ~m1_subset_1(D_998, k1_zfmisc_1(A_999)) | v1_xboole_0(D_998) | ~m1_subset_1(C_1001, k1_zfmisc_1(A_999)) | v1_xboole_0(C_1001) | v1_xboole_0(B_996) | v1_xboole_0(A_999))), inference(resolution, [status(thm)], [c_54, c_3343])).
% 15.17/6.83  tff(c_6154, plain, (![A_999, C_1001, E_1000]: (k2_partfun1(k4_subset_1(A_999, C_1001, '#skF_6'), '#skF_4', k1_tmap_1(A_999, '#skF_4', C_1001, '#skF_6', E_1000, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_999, '#skF_4', C_1001, '#skF_6', E_1000, '#skF_8')) | k2_partfun1(C_1001, '#skF_4', E_1000, k9_subset_1(A_999, C_1001, '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1(A_999, C_1001, '#skF_6')) | ~v1_funct_2('#skF_8', '#skF_6', '#skF_4') | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1000, k1_zfmisc_1(k2_zfmisc_1(C_1001, '#skF_4'))) | ~v1_funct_2(E_1000, C_1001, '#skF_4') | ~v1_funct_1(E_1000) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_999)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1001, k1_zfmisc_1(A_999)) | v1_xboole_0(C_1001) | v1_xboole_0('#skF_4') | v1_xboole_0(A_999))), inference(resolution, [status(thm)], [c_60, c_6147])).
% 15.17/6.83  tff(c_6161, plain, (![A_999, C_1001, E_1000]: (k2_partfun1(k4_subset_1(A_999, C_1001, '#skF_6'), '#skF_4', k1_tmap_1(A_999, '#skF_4', C_1001, '#skF_6', E_1000, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_999, '#skF_4', C_1001, '#skF_6', E_1000, '#skF_8')) | k2_partfun1(C_1001, '#skF_4', E_1000, k9_subset_1(A_999, C_1001, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_999, C_1001, '#skF_6')) | ~m1_subset_1(E_1000, k1_zfmisc_1(k2_zfmisc_1(C_1001, '#skF_4'))) | ~v1_funct_2(E_1000, C_1001, '#skF_4') | ~v1_funct_1(E_1000) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_999)) | v1_xboole_0('#skF_6') | ~m1_subset_1(C_1001, k1_zfmisc_1(A_999)) | v1_xboole_0(C_1001) | v1_xboole_0('#skF_4') | v1_xboole_0(A_999))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1376, c_6154])).
% 15.17/6.83  tff(c_11663, plain, (![A_1239, C_1240, E_1241]: (k2_partfun1(k4_subset_1(A_1239, C_1240, '#skF_6'), '#skF_4', k1_tmap_1(A_1239, '#skF_4', C_1240, '#skF_6', E_1241, '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1239, '#skF_4', C_1240, '#skF_6', E_1241, '#skF_8')) | k2_partfun1(C_1240, '#skF_4', E_1241, k9_subset_1(A_1239, C_1240, '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1239, C_1240, '#skF_6')) | ~m1_subset_1(E_1241, k1_zfmisc_1(k2_zfmisc_1(C_1240, '#skF_4'))) | ~v1_funct_2(E_1241, C_1240, '#skF_4') | ~v1_funct_1(E_1241) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1239)) | ~m1_subset_1(C_1240, k1_zfmisc_1(A_1239)) | v1_xboole_0(C_1240) | v1_xboole_0(A_1239))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_6161])).
% 15.17/6.83  tff(c_11673, plain, (![A_1239]: (k2_partfun1(k4_subset_1(A_1239, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1239, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1239, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1(A_1239, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1239, '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_4') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1239)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1239)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1239))), inference(resolution, [status(thm)], [c_66, c_11663])).
% 15.17/6.83  tff(c_11684, plain, (![A_1239]: (k2_partfun1(k4_subset_1(A_1239, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1239, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1239, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1239, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1239, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1239)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1239)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_1239))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1379, c_11673])).
% 15.17/6.83  tff(c_14444, plain, (![A_1398]: (k2_partfun1(k4_subset_1(A_1398, '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1(A_1398, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')='#skF_8' | ~v1_funct_1(k1_tmap_1(A_1398, '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1(A_1398, '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1(A_1398, '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1398)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1398)) | v1_xboole_0(A_1398))), inference(negUnitSimplification, [status(thm)], [c_80, c_11684])).
% 15.17/6.83  tff(c_194, plain, (![C_253, A_254, B_255]: (v1_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.17/6.83  tff(c_206, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_194])).
% 15.17/6.83  tff(c_157, plain, (![A_245, B_246]: (r2_hidden('#skF_2'(A_245, B_246), B_246) | r1_xboole_0(A_245, B_246))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.17/6.83  tff(c_169, plain, (![B_248, A_249]: (~v1_xboole_0(B_248) | r1_xboole_0(A_249, B_248))), inference(resolution, [status(thm)], [c_157, c_2])).
% 15.17/6.83  tff(c_174, plain, (![A_250, B_251]: (k3_xboole_0(A_250, B_251)=k1_xboole_0 | ~v1_xboole_0(B_251))), inference(resolution, [status(thm)], [c_169, c_6])).
% 15.17/6.83  tff(c_177, plain, (![A_250]: (k3_xboole_0(A_250, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_174])).
% 15.17/6.83  tff(c_236, plain, (![A_265, B_266, C_267]: (~r1_xboole_0(A_265, B_266) | ~r2_hidden(C_267, B_266) | ~r2_hidden(C_267, A_265))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.17/6.83  tff(c_295, plain, (![C_276, B_277, A_278]: (~r2_hidden(C_276, B_277) | ~r2_hidden(C_276, A_278) | k3_xboole_0(A_278, B_277)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_236])).
% 15.17/6.83  tff(c_511, plain, (![A_318, B_319, A_320]: (~r2_hidden('#skF_2'(A_318, B_319), A_320) | k3_xboole_0(A_320, B_319)!=k1_xboole_0 | r1_xboole_0(A_318, B_319))), inference(resolution, [status(thm)], [c_14, c_295])).
% 15.17/6.83  tff(c_520, plain, (![B_321, A_322]: (k3_xboole_0(B_321, B_321)!=k1_xboole_0 | r1_xboole_0(A_322, B_321))), inference(resolution, [status(thm)], [c_14, c_511])).
% 15.17/6.83  tff(c_527, plain, (![A_322]: (r1_xboole_0(A_322, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_177, c_520])).
% 15.17/6.83  tff(c_246, plain, (![B_268, A_269]: (v4_relat_1(B_268, A_269) | ~r1_tarski(k1_relat_1(B_268), A_269) | ~v1_relat_1(B_268))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.17/6.83  tff(c_256, plain, (![B_270]: (v4_relat_1(B_270, k1_relat_1(B_270)) | ~v1_relat_1(B_270))), inference(resolution, [status(thm)], [c_22, c_246])).
% 15.17/6.83  tff(c_260, plain, (![B_270]: (k7_relat_1(B_270, k1_relat_1(B_270))=B_270 | ~v1_relat_1(B_270))), inference(resolution, [status(thm)], [c_256, c_36])).
% 15.17/6.83  tff(c_306, plain, (![C_282, A_283, B_284]: (k7_relat_1(k7_relat_1(C_282, A_283), B_284)=k1_xboole_0 | ~r1_xboole_0(A_283, B_284) | ~v1_relat_1(C_282))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.17/6.83  tff(c_712, plain, (![B_361, B_362]: (k7_relat_1(B_361, B_362)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_361), B_362) | ~v1_relat_1(B_361) | ~v1_relat_1(B_361))), inference(superposition, [status(thm), theory('equality')], [c_260, c_306])).
% 15.17/6.83  tff(c_756, plain, (![B_364]: (k7_relat_1(B_364, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_364))), inference(resolution, [status(thm)], [c_527, c_712])).
% 15.17/6.83  tff(c_768, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_206, c_756])).
% 15.17/6.83  tff(c_207, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_194])).
% 15.17/6.83  tff(c_767, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_207, c_756])).
% 15.17/6.83  tff(c_270, plain, (![A_272, B_273]: (r1_xboole_0(A_272, B_273) | ~r1_subset_1(A_272, B_273) | v1_xboole_0(B_273) | v1_xboole_0(A_272))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.17/6.83  tff(c_467, plain, (![A_308, B_309]: (k3_xboole_0(A_308, B_309)=k1_xboole_0 | ~r1_subset_1(A_308, B_309) | v1_xboole_0(B_309) | v1_xboole_0(A_308))), inference(resolution, [status(thm)], [c_270, c_6])).
% 15.17/6.83  tff(c_473, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_467])).
% 15.17/6.83  tff(c_477, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_76, c_473])).
% 15.17/6.83  tff(c_383, plain, (![A_293, B_294, C_295, D_296]: (k2_partfun1(A_293, B_294, C_295, D_296)=k7_relat_1(C_295, D_296) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~v1_funct_1(C_295))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.17/6.83  tff(c_390, plain, (![D_296]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_296)=k7_relat_1('#skF_7', D_296) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_383])).
% 15.17/6.83  tff(c_397, plain, (![D_296]: (k2_partfun1('#skF_5', '#skF_4', '#skF_7', D_296)=k7_relat_1('#skF_7', D_296))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_390])).
% 15.17/6.83  tff(c_388, plain, (![D_296]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_296)=k7_relat_1('#skF_8', D_296) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_383])).
% 15.17/6.83  tff(c_394, plain, (![D_296]: (k2_partfun1('#skF_6', '#skF_4', '#skF_8', D_296)=k7_relat_1('#skF_8', D_296))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_388])).
% 15.17/6.83  tff(c_348, plain, (![A_288, B_289, C_290]: (k9_subset_1(A_288, B_289, C_290)=k3_xboole_0(B_289, C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(A_288)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.17/6.83  tff(c_363, plain, (![B_289]: (k9_subset_1('#skF_3', B_289, '#skF_6')=k3_xboole_0(B_289, '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_348])).
% 15.17/6.83  tff(c_58, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 15.17/6.83  tff(c_99, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_58])).
% 15.17/6.83  tff(c_373, plain, (k2_partfun1('#skF_5', '#skF_4', '#skF_7', k3_xboole_0('#skF_5', '#skF_6'))!=k2_partfun1('#skF_6', '#skF_4', '#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_363, c_99])).
% 15.17/6.83  tff(c_1012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_768, c_767, c_477, c_477, c_397, c_394, c_373])).
% 15.17/6.83  tff(c_1013, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 15.17/6.83  tff(c_1153, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_6')!='#skF_8'), inference(splitLeft, [status(thm)], [c_1013])).
% 15.17/6.83  tff(c_14467, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14444, c_1153])).
% 15.17/6.83  tff(c_14503, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_1765, c_1764, c_1364, c_1364, c_1283, c_1283, c_1721, c_14467])).
% 15.17/6.83  tff(c_14505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_14503])).
% 15.17/6.83  tff(c_14506, plain, (k2_partfun1(k4_subset_1('#skF_3', '#skF_5', '#skF_6'), '#skF_4', k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_1013])).
% 15.17/6.83  tff(c_25388, plain, (~v1_funct_1(k1_tmap_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k7_relat_1('#skF_7', k9_subset_1('#skF_3', '#skF_5', '#skF_6'))!=k7_relat_1('#skF_8', k9_subset_1('#skF_3', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_25368, c_14506])).
% 15.17/6.83  tff(c_25417, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_15067, c_15066, c_14722, c_14722, c_14615, c_14615, c_15405, c_25388])).
% 15.17/6.83  tff(c_25419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_25417])).
% 15.17/6.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.17/6.83  
% 15.17/6.83  Inference rules
% 15.17/6.83  ----------------------
% 15.17/6.83  #Ref     : 0
% 15.17/6.83  #Sup     : 4940
% 15.17/6.83  #Fact    : 0
% 15.17/6.83  #Define  : 0
% 15.17/6.83  #Split   : 47
% 15.17/6.83  #Chain   : 0
% 15.17/6.83  #Close   : 0
% 15.17/6.83  
% 15.17/6.83  Ordering : KBO
% 15.17/6.83  
% 15.17/6.83  Simplification rules
% 15.17/6.83  ----------------------
% 15.17/6.83  #Subsume      : 1592
% 15.17/6.83  #Demod        : 4948
% 15.17/6.83  #Tautology    : 2090
% 15.17/6.83  #SimpNegUnit  : 1185
% 15.17/6.83  #BackRed      : 12
% 15.17/6.83  
% 15.17/6.83  #Partial instantiations: 0
% 15.17/6.83  #Strategies tried      : 1
% 15.17/6.83  
% 15.17/6.83  Timing (in seconds)
% 15.17/6.83  ----------------------
% 15.50/6.84  Preprocessing        : 0.44
% 15.50/6.84  Parsing              : 0.21
% 15.50/6.84  CNF conversion       : 0.07
% 15.50/6.84  Main loop            : 5.53
% 15.50/6.84  Inferencing          : 1.80
% 15.50/6.84  Reduction            : 1.97
% 15.50/6.84  Demodulation         : 1.50
% 15.50/6.84  BG Simplification    : 0.11
% 15.50/6.84  Subsumption          : 1.38
% 15.50/6.84  Abstraction          : 0.19
% 15.50/6.84  MUC search           : 0.00
% 15.50/6.84  Cooper               : 0.00
% 15.50/6.84  Total                : 6.03
% 15.50/6.84  Index Insertion      : 0.00
% 15.50/6.84  Index Deletion       : 0.00
% 15.50/6.84  Index Matching       : 0.00
% 15.50/6.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
