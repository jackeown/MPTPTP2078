%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:10 EST 2020

% Result     : Theorem 22.23s
% Output     : CNFRefutation 22.57s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 558 expanded)
%              Number of leaves         :   46 ( 222 expanded)
%              Depth                    :   12
%              Number of atoms          :  619 (2628 expanded)
%              Number of equality atoms :  125 ( 512 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_243,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_201,axiom,(
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

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_167,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_62781,plain,(
    ! [C_1578,A_1579,B_1580] :
      ( v1_relat_1(C_1578)
      | ~ m1_subset_1(C_1578,k1_zfmisc_1(k2_zfmisc_1(A_1579,B_1580))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_62794,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_62781])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [B_236,A_237] :
      ( r1_xboole_0(B_236,A_237)
      | ~ r1_xboole_0(A_237,B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,(
    ! [B_8,A_7] : r1_xboole_0(B_8,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_10,c_92])).

tff(c_8196,plain,(
    ! [A_608,B_609] :
      ( k3_xboole_0(A_608,B_609) = k1_xboole_0
      | ~ r1_xboole_0(A_608,B_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8211,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_8196])).

tff(c_8156,plain,(
    ! [A_604,B_605] :
      ( k4_xboole_0(A_604,B_605) = A_604
      | ~ r1_xboole_0(A_604,B_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8171,plain,(
    ! [B_8,A_7] : k4_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = B_8 ),
    inference(resolution,[status(thm)],[c_95,c_8156])).

tff(c_62651,plain,(
    ! [A_1571,B_1572] : k4_xboole_0(A_1571,k4_xboole_0(A_1571,B_1572)) = k3_xboole_0(A_1571,B_1572) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62685,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = k4_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8171,c_62651])).

tff(c_62702,plain,(
    ! [B_1574] : k4_xboole_0(B_1574,B_1574) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8211,c_62685])).

tff(c_62722,plain,(
    ! [B_1574] : r1_xboole_0(k1_xboole_0,B_1574) ),
    inference(superposition,[status(thm),theory(equality)],[c_62702,c_10])).

tff(c_63451,plain,(
    ! [A_1621,B_1622] :
      ( k7_relat_1(A_1621,B_1622) = k1_xboole_0
      | ~ r1_xboole_0(B_1622,k1_relat_1(A_1621))
      | ~ v1_relat_1(A_1621) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_63482,plain,(
    ! [A_1623] :
      ( k7_relat_1(A_1623,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_1623) ) ),
    inference(resolution,[status(thm)],[c_62722,c_63451])).

tff(c_63489,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62794,c_63482])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_78,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_63615,plain,(
    ! [A_1628,B_1629] :
      ( r1_xboole_0(A_1628,B_1629)
      | ~ r1_subset_1(A_1628,B_1629)
      | v1_xboole_0(B_1629)
      | v1_xboole_0(A_1628) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70393,plain,(
    ! [A_1906,B_1907] :
      ( k3_xboole_0(A_1906,B_1907) = k1_xboole_0
      | ~ r1_subset_1(A_1906,B_1907)
      | v1_xboole_0(B_1907)
      | v1_xboole_0(A_1906) ) ),
    inference(resolution,[status(thm)],[c_63615,c_2])).

tff(c_70411,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_70393])).

tff(c_70423,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_70411])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_62793,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_62781])).

tff(c_63490,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62793,c_63482])).

tff(c_65652,plain,(
    ! [A_1732,B_1733,C_1734] :
      ( k9_subset_1(A_1732,B_1733,C_1734) = k3_xboole_0(B_1733,C_1734)
      | ~ m1_subset_1(C_1734,k1_zfmisc_1(A_1732)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65667,plain,(
    ! [B_1733] : k9_subset_1('#skF_1',B_1733,'#skF_4') = k3_xboole_0(B_1733,'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_65652])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_66270,plain,(
    ! [B_1768,A_1766,E_1767,C_1765,D_1763,F_1764] :
      ( v1_funct_1(k1_tmap_1(A_1766,B_1768,C_1765,D_1763,E_1767,F_1764))
      | ~ m1_subset_1(F_1764,k1_zfmisc_1(k2_zfmisc_1(D_1763,B_1768)))
      | ~ v1_funct_2(F_1764,D_1763,B_1768)
      | ~ v1_funct_1(F_1764)
      | ~ m1_subset_1(E_1767,k1_zfmisc_1(k2_zfmisc_1(C_1765,B_1768)))
      | ~ v1_funct_2(E_1767,C_1765,B_1768)
      | ~ v1_funct_1(E_1767)
      | ~ m1_subset_1(D_1763,k1_zfmisc_1(A_1766))
      | v1_xboole_0(D_1763)
      | ~ m1_subset_1(C_1765,k1_zfmisc_1(A_1766))
      | v1_xboole_0(C_1765)
      | v1_xboole_0(B_1768)
      | v1_xboole_0(A_1766) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_66277,plain,(
    ! [A_1766,C_1765,E_1767] :
      ( v1_funct_1(k1_tmap_1(A_1766,'#skF_2',C_1765,'#skF_4',E_1767,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1767,k1_zfmisc_1(k2_zfmisc_1(C_1765,'#skF_2')))
      | ~ v1_funct_2(E_1767,C_1765,'#skF_2')
      | ~ v1_funct_1(E_1767)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1766))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1765,k1_zfmisc_1(A_1766))
      | v1_xboole_0(C_1765)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1766) ) ),
    inference(resolution,[status(thm)],[c_66,c_66270])).

tff(c_66285,plain,(
    ! [A_1766,C_1765,E_1767] :
      ( v1_funct_1(k1_tmap_1(A_1766,'#skF_2',C_1765,'#skF_4',E_1767,'#skF_6'))
      | ~ m1_subset_1(E_1767,k1_zfmisc_1(k2_zfmisc_1(C_1765,'#skF_2')))
      | ~ v1_funct_2(E_1767,C_1765,'#skF_2')
      | ~ v1_funct_1(E_1767)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1766))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1765,k1_zfmisc_1(A_1766))
      | v1_xboole_0(C_1765)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1766) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66277])).

tff(c_67352,plain,(
    ! [A_1830,C_1831,E_1832] :
      ( v1_funct_1(k1_tmap_1(A_1830,'#skF_2',C_1831,'#skF_4',E_1832,'#skF_6'))
      | ~ m1_subset_1(E_1832,k1_zfmisc_1(k2_zfmisc_1(C_1831,'#skF_2')))
      | ~ v1_funct_2(E_1832,C_1831,'#skF_2')
      | ~ v1_funct_1(E_1832)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1830))
      | ~ m1_subset_1(C_1831,k1_zfmisc_1(A_1830))
      | v1_xboole_0(C_1831)
      | v1_xboole_0(A_1830) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_66285])).

tff(c_67360,plain,(
    ! [A_1830] :
      ( v1_funct_1(k1_tmap_1(A_1830,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1830))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1830))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1830) ) ),
    inference(resolution,[status(thm)],[c_72,c_67352])).

tff(c_67369,plain,(
    ! [A_1830] :
      ( v1_funct_1(k1_tmap_1(A_1830,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1830))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1830))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1830) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_67360])).

tff(c_68996,plain,(
    ! [A_1868] :
      ( v1_funct_1(k1_tmap_1(A_1868,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1868))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1868))
      | v1_xboole_0(A_1868) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_67369])).

tff(c_69003,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_68996])).

tff(c_69007,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_69003])).

tff(c_69008,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_69007])).

tff(c_65831,plain,(
    ! [A_1742,B_1743,C_1744,D_1745] :
      ( k2_partfun1(A_1742,B_1743,C_1744,D_1745) = k7_relat_1(C_1744,D_1745)
      | ~ m1_subset_1(C_1744,k1_zfmisc_1(k2_zfmisc_1(A_1742,B_1743)))
      | ~ v1_funct_1(C_1744) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_65836,plain,(
    ! [D_1745] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1745) = k7_relat_1('#skF_5',D_1745)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_65831])).

tff(c_65842,plain,(
    ! [D_1745] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1745) = k7_relat_1('#skF_5',D_1745) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_65836])).

tff(c_65838,plain,(
    ! [D_1745] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1745) = k7_relat_1('#skF_6',D_1745)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_65831])).

tff(c_65845,plain,(
    ! [D_1745] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1745) = k7_relat_1('#skF_6',D_1745) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_65838])).

tff(c_60,plain,(
    ! [B_172,A_171,C_173,E_175,F_176,D_174] :
      ( v1_funct_2(k1_tmap_1(A_171,B_172,C_173,D_174,E_175,F_176),k4_subset_1(A_171,C_173,D_174),B_172)
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(D_174,B_172)))
      | ~ v1_funct_2(F_176,D_174,B_172)
      | ~ v1_funct_1(F_176)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(C_173,B_172)))
      | ~ v1_funct_2(E_175,C_173,B_172)
      | ~ v1_funct_1(E_175)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(A_171))
      | v1_xboole_0(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | v1_xboole_0(C_173)
      | v1_xboole_0(B_172)
      | v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    ! [B_172,A_171,C_173,E_175,F_176,D_174] :
      ( m1_subset_1(k1_tmap_1(A_171,B_172,C_173,D_174,E_175,F_176),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_171,C_173,D_174),B_172)))
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(D_174,B_172)))
      | ~ v1_funct_2(F_176,D_174,B_172)
      | ~ v1_funct_1(F_176)
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(C_173,B_172)))
      | ~ v1_funct_2(E_175,C_173,B_172)
      | ~ v1_funct_1(E_175)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(A_171))
      | v1_xboole_0(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(A_171))
      | v1_xboole_0(C_173)
      | v1_xboole_0(B_172)
      | v1_xboole_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_67318,plain,(
    ! [E_1824,B_1823,F_1822,A_1825,D_1827,C_1826] :
      ( k2_partfun1(k4_subset_1(A_1825,C_1826,D_1827),B_1823,k1_tmap_1(A_1825,B_1823,C_1826,D_1827,E_1824,F_1822),C_1826) = E_1824
      | ~ m1_subset_1(k1_tmap_1(A_1825,B_1823,C_1826,D_1827,E_1824,F_1822),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1825,C_1826,D_1827),B_1823)))
      | ~ v1_funct_2(k1_tmap_1(A_1825,B_1823,C_1826,D_1827,E_1824,F_1822),k4_subset_1(A_1825,C_1826,D_1827),B_1823)
      | ~ v1_funct_1(k1_tmap_1(A_1825,B_1823,C_1826,D_1827,E_1824,F_1822))
      | k2_partfun1(D_1827,B_1823,F_1822,k9_subset_1(A_1825,C_1826,D_1827)) != k2_partfun1(C_1826,B_1823,E_1824,k9_subset_1(A_1825,C_1826,D_1827))
      | ~ m1_subset_1(F_1822,k1_zfmisc_1(k2_zfmisc_1(D_1827,B_1823)))
      | ~ v1_funct_2(F_1822,D_1827,B_1823)
      | ~ v1_funct_1(F_1822)
      | ~ m1_subset_1(E_1824,k1_zfmisc_1(k2_zfmisc_1(C_1826,B_1823)))
      | ~ v1_funct_2(E_1824,C_1826,B_1823)
      | ~ v1_funct_1(E_1824)
      | ~ m1_subset_1(D_1827,k1_zfmisc_1(A_1825))
      | v1_xboole_0(D_1827)
      | ~ m1_subset_1(C_1826,k1_zfmisc_1(A_1825))
      | v1_xboole_0(C_1826)
      | v1_xboole_0(B_1823)
      | v1_xboole_0(A_1825) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_79053,plain,(
    ! [F_2092,B_2096,A_2094,E_2095,C_2093,D_2091] :
      ( k2_partfun1(k4_subset_1(A_2094,C_2093,D_2091),B_2096,k1_tmap_1(A_2094,B_2096,C_2093,D_2091,E_2095,F_2092),C_2093) = E_2095
      | ~ v1_funct_2(k1_tmap_1(A_2094,B_2096,C_2093,D_2091,E_2095,F_2092),k4_subset_1(A_2094,C_2093,D_2091),B_2096)
      | ~ v1_funct_1(k1_tmap_1(A_2094,B_2096,C_2093,D_2091,E_2095,F_2092))
      | k2_partfun1(D_2091,B_2096,F_2092,k9_subset_1(A_2094,C_2093,D_2091)) != k2_partfun1(C_2093,B_2096,E_2095,k9_subset_1(A_2094,C_2093,D_2091))
      | ~ m1_subset_1(F_2092,k1_zfmisc_1(k2_zfmisc_1(D_2091,B_2096)))
      | ~ v1_funct_2(F_2092,D_2091,B_2096)
      | ~ v1_funct_1(F_2092)
      | ~ m1_subset_1(E_2095,k1_zfmisc_1(k2_zfmisc_1(C_2093,B_2096)))
      | ~ v1_funct_2(E_2095,C_2093,B_2096)
      | ~ v1_funct_1(E_2095)
      | ~ m1_subset_1(D_2091,k1_zfmisc_1(A_2094))
      | v1_xboole_0(D_2091)
      | ~ m1_subset_1(C_2093,k1_zfmisc_1(A_2094))
      | v1_xboole_0(C_2093)
      | v1_xboole_0(B_2096)
      | v1_xboole_0(A_2094) ) ),
    inference(resolution,[status(thm)],[c_58,c_67318])).

tff(c_97539,plain,(
    ! [E_2338,A_2337,F_2335,B_2339,C_2336,D_2334] :
      ( k2_partfun1(k4_subset_1(A_2337,C_2336,D_2334),B_2339,k1_tmap_1(A_2337,B_2339,C_2336,D_2334,E_2338,F_2335),C_2336) = E_2338
      | ~ v1_funct_1(k1_tmap_1(A_2337,B_2339,C_2336,D_2334,E_2338,F_2335))
      | k2_partfun1(D_2334,B_2339,F_2335,k9_subset_1(A_2337,C_2336,D_2334)) != k2_partfun1(C_2336,B_2339,E_2338,k9_subset_1(A_2337,C_2336,D_2334))
      | ~ m1_subset_1(F_2335,k1_zfmisc_1(k2_zfmisc_1(D_2334,B_2339)))
      | ~ v1_funct_2(F_2335,D_2334,B_2339)
      | ~ v1_funct_1(F_2335)
      | ~ m1_subset_1(E_2338,k1_zfmisc_1(k2_zfmisc_1(C_2336,B_2339)))
      | ~ v1_funct_2(E_2338,C_2336,B_2339)
      | ~ v1_funct_1(E_2338)
      | ~ m1_subset_1(D_2334,k1_zfmisc_1(A_2337))
      | v1_xboole_0(D_2334)
      | ~ m1_subset_1(C_2336,k1_zfmisc_1(A_2337))
      | v1_xboole_0(C_2336)
      | v1_xboole_0(B_2339)
      | v1_xboole_0(A_2337) ) ),
    inference(resolution,[status(thm)],[c_60,c_79053])).

tff(c_97548,plain,(
    ! [A_2337,C_2336,E_2338] :
      ( k2_partfun1(k4_subset_1(A_2337,C_2336,'#skF_4'),'#skF_2',k1_tmap_1(A_2337,'#skF_2',C_2336,'#skF_4',E_2338,'#skF_6'),C_2336) = E_2338
      | ~ v1_funct_1(k1_tmap_1(A_2337,'#skF_2',C_2336,'#skF_4',E_2338,'#skF_6'))
      | k2_partfun1(C_2336,'#skF_2',E_2338,k9_subset_1(A_2337,C_2336,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_2337,C_2336,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2338,k1_zfmisc_1(k2_zfmisc_1(C_2336,'#skF_2')))
      | ~ v1_funct_2(E_2338,C_2336,'#skF_2')
      | ~ v1_funct_1(E_2338)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2337))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2336,k1_zfmisc_1(A_2337))
      | v1_xboole_0(C_2336)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2337) ) ),
    inference(resolution,[status(thm)],[c_66,c_97539])).

tff(c_97557,plain,(
    ! [A_2337,C_2336,E_2338] :
      ( k2_partfun1(k4_subset_1(A_2337,C_2336,'#skF_4'),'#skF_2',k1_tmap_1(A_2337,'#skF_2',C_2336,'#skF_4',E_2338,'#skF_6'),C_2336) = E_2338
      | ~ v1_funct_1(k1_tmap_1(A_2337,'#skF_2',C_2336,'#skF_4',E_2338,'#skF_6'))
      | k2_partfun1(C_2336,'#skF_2',E_2338,k9_subset_1(A_2337,C_2336,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2337,C_2336,'#skF_4'))
      | ~ m1_subset_1(E_2338,k1_zfmisc_1(k2_zfmisc_1(C_2336,'#skF_2')))
      | ~ v1_funct_2(E_2338,C_2336,'#skF_2')
      | ~ v1_funct_1(E_2338)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2337))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2336,k1_zfmisc_1(A_2337))
      | v1_xboole_0(C_2336)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_65845,c_97548])).

tff(c_100831,plain,(
    ! [A_2382,C_2383,E_2384] :
      ( k2_partfun1(k4_subset_1(A_2382,C_2383,'#skF_4'),'#skF_2',k1_tmap_1(A_2382,'#skF_2',C_2383,'#skF_4',E_2384,'#skF_6'),C_2383) = E_2384
      | ~ v1_funct_1(k1_tmap_1(A_2382,'#skF_2',C_2383,'#skF_4',E_2384,'#skF_6'))
      | k2_partfun1(C_2383,'#skF_2',E_2384,k9_subset_1(A_2382,C_2383,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2382,C_2383,'#skF_4'))
      | ~ m1_subset_1(E_2384,k1_zfmisc_1(k2_zfmisc_1(C_2383,'#skF_2')))
      | ~ v1_funct_2(E_2384,C_2383,'#skF_2')
      | ~ v1_funct_1(E_2384)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2382))
      | ~ m1_subset_1(C_2383,k1_zfmisc_1(A_2382))
      | v1_xboole_0(C_2383)
      | v1_xboole_0(A_2382) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_97557])).

tff(c_100839,plain,(
    ! [A_2382] :
      ( k2_partfun1(k4_subset_1(A_2382,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2382,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2382,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2382,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2382,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2382))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2382))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2382) ) ),
    inference(resolution,[status(thm)],[c_72,c_100831])).

tff(c_100848,plain,(
    ! [A_2382] :
      ( k2_partfun1(k4_subset_1(A_2382,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2382,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2382,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2382,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2382,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2382))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2382))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2382) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_65842,c_100839])).

tff(c_102447,plain,(
    ! [A_2430] :
      ( k2_partfun1(k4_subset_1(A_2430,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2430,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2430,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2430,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2430,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2430))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2430))
      | v1_xboole_0(A_2430) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_100848])).

tff(c_8423,plain,(
    ! [C_629,A_630,B_631] :
      ( v1_relat_1(C_629)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(A_630,B_631))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8436,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_8423])).

tff(c_8293,plain,(
    ! [A_622,B_623] : k4_xboole_0(A_622,k4_xboole_0(A_622,B_623)) = k3_xboole_0(A_622,B_623) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8327,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = k4_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8171,c_8293])).

tff(c_8344,plain,(
    ! [B_625] : k4_xboole_0(B_625,B_625) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8211,c_8327])).

tff(c_8364,plain,(
    ! [B_625] : r1_xboole_0(k1_xboole_0,B_625) ),
    inference(superposition,[status(thm),theory(equality)],[c_8344,c_10])).

tff(c_9012,plain,(
    ! [A_666,B_667] :
      ( k7_relat_1(A_666,B_667) = k1_xboole_0
      | ~ r1_xboole_0(B_667,k1_relat_1(A_666))
      | ~ v1_relat_1(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9043,plain,(
    ! [A_668] :
      ( k7_relat_1(A_668,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_668) ) ),
    inference(resolution,[status(thm)],[c_8364,c_9012])).

tff(c_9050,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8436,c_9043])).

tff(c_9354,plain,(
    ! [A_680,B_681] :
      ( r1_xboole_0(A_680,B_681)
      | ~ r1_subset_1(A_680,B_681)
      | v1_xboole_0(B_681)
      | v1_xboole_0(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_15539,plain,(
    ! [A_923,B_924] :
      ( k3_xboole_0(A_923,B_924) = k1_xboole_0
      | ~ r1_subset_1(A_923,B_924)
      | v1_xboole_0(B_924)
      | v1_xboole_0(A_923) ) ),
    inference(resolution,[status(thm)],[c_9354,c_2])).

tff(c_15557,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_15539])).

tff(c_15569,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_15557])).

tff(c_8435,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_8423])).

tff(c_9051,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8435,c_9043])).

tff(c_9488,plain,(
    ! [A_686,B_687,C_688] :
      ( k9_subset_1(A_686,B_687,C_688) = k3_xboole_0(B_687,C_688)
      | ~ m1_subset_1(C_688,k1_zfmisc_1(A_686)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9503,plain,(
    ! [B_687] : k9_subset_1('#skF_1',B_687,'#skF_4') = k3_xboole_0(B_687,'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_9488])).

tff(c_11601,plain,(
    ! [C_782,F_781,A_783,B_785,D_780,E_784] :
      ( v1_funct_1(k1_tmap_1(A_783,B_785,C_782,D_780,E_784,F_781))
      | ~ m1_subset_1(F_781,k1_zfmisc_1(k2_zfmisc_1(D_780,B_785)))
      | ~ v1_funct_2(F_781,D_780,B_785)
      | ~ v1_funct_1(F_781)
      | ~ m1_subset_1(E_784,k1_zfmisc_1(k2_zfmisc_1(C_782,B_785)))
      | ~ v1_funct_2(E_784,C_782,B_785)
      | ~ v1_funct_1(E_784)
      | ~ m1_subset_1(D_780,k1_zfmisc_1(A_783))
      | v1_xboole_0(D_780)
      | ~ m1_subset_1(C_782,k1_zfmisc_1(A_783))
      | v1_xboole_0(C_782)
      | v1_xboole_0(B_785)
      | v1_xboole_0(A_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_11608,plain,(
    ! [A_783,C_782,E_784] :
      ( v1_funct_1(k1_tmap_1(A_783,'#skF_2',C_782,'#skF_4',E_784,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_784,k1_zfmisc_1(k2_zfmisc_1(C_782,'#skF_2')))
      | ~ v1_funct_2(E_784,C_782,'#skF_2')
      | ~ v1_funct_1(E_784)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_783))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_782,k1_zfmisc_1(A_783))
      | v1_xboole_0(C_782)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_783) ) ),
    inference(resolution,[status(thm)],[c_66,c_11601])).

tff(c_11616,plain,(
    ! [A_783,C_782,E_784] :
      ( v1_funct_1(k1_tmap_1(A_783,'#skF_2',C_782,'#skF_4',E_784,'#skF_6'))
      | ~ m1_subset_1(E_784,k1_zfmisc_1(k2_zfmisc_1(C_782,'#skF_2')))
      | ~ v1_funct_2(E_784,C_782,'#skF_2')
      | ~ v1_funct_1(E_784)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_783))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_782,k1_zfmisc_1(A_783))
      | v1_xboole_0(C_782)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_783) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_11608])).

tff(c_11634,plain,(
    ! [A_788,C_789,E_790] :
      ( v1_funct_1(k1_tmap_1(A_788,'#skF_2',C_789,'#skF_4',E_790,'#skF_6'))
      | ~ m1_subset_1(E_790,k1_zfmisc_1(k2_zfmisc_1(C_789,'#skF_2')))
      | ~ v1_funct_2(E_790,C_789,'#skF_2')
      | ~ v1_funct_1(E_790)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_788))
      | ~ m1_subset_1(C_789,k1_zfmisc_1(A_788))
      | v1_xboole_0(C_789)
      | v1_xboole_0(A_788) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_11616])).

tff(c_11639,plain,(
    ! [A_788] :
      ( v1_funct_1(k1_tmap_1(A_788,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_788))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_788))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_788) ) ),
    inference(resolution,[status(thm)],[c_72,c_11634])).

tff(c_11645,plain,(
    ! [A_788] :
      ( v1_funct_1(k1_tmap_1(A_788,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_788))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_788))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_788) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_11639])).

tff(c_12091,plain,(
    ! [A_816] :
      ( v1_funct_1(k1_tmap_1(A_816,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_816))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_816))
      | v1_xboole_0(A_816) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_11645])).

tff(c_12098,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_12091])).

tff(c_12102,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12098])).

tff(c_12103,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_12102])).

tff(c_10937,plain,(
    ! [A_758,B_759,C_760,D_761] :
      ( k2_partfun1(A_758,B_759,C_760,D_761) = k7_relat_1(C_760,D_761)
      | ~ m1_subset_1(C_760,k1_zfmisc_1(k2_zfmisc_1(A_758,B_759)))
      | ~ v1_funct_1(C_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10942,plain,(
    ! [D_761] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_761) = k7_relat_1('#skF_5',D_761)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_10937])).

tff(c_10948,plain,(
    ! [D_761] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_761) = k7_relat_1('#skF_5',D_761) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10942])).

tff(c_10944,plain,(
    ! [D_761] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_761) = k7_relat_1('#skF_6',D_761)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_10937])).

tff(c_10951,plain,(
    ! [D_761] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_761) = k7_relat_1('#skF_6',D_761) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10944])).

tff(c_12335,plain,(
    ! [C_841,D_842,B_838,F_837,E_839,A_840] :
      ( k2_partfun1(k4_subset_1(A_840,C_841,D_842),B_838,k1_tmap_1(A_840,B_838,C_841,D_842,E_839,F_837),D_842) = F_837
      | ~ m1_subset_1(k1_tmap_1(A_840,B_838,C_841,D_842,E_839,F_837),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_840,C_841,D_842),B_838)))
      | ~ v1_funct_2(k1_tmap_1(A_840,B_838,C_841,D_842,E_839,F_837),k4_subset_1(A_840,C_841,D_842),B_838)
      | ~ v1_funct_1(k1_tmap_1(A_840,B_838,C_841,D_842,E_839,F_837))
      | k2_partfun1(D_842,B_838,F_837,k9_subset_1(A_840,C_841,D_842)) != k2_partfun1(C_841,B_838,E_839,k9_subset_1(A_840,C_841,D_842))
      | ~ m1_subset_1(F_837,k1_zfmisc_1(k2_zfmisc_1(D_842,B_838)))
      | ~ v1_funct_2(F_837,D_842,B_838)
      | ~ v1_funct_1(F_837)
      | ~ m1_subset_1(E_839,k1_zfmisc_1(k2_zfmisc_1(C_841,B_838)))
      | ~ v1_funct_2(E_839,C_841,B_838)
      | ~ v1_funct_1(E_839)
      | ~ m1_subset_1(D_842,k1_zfmisc_1(A_840))
      | v1_xboole_0(D_842)
      | ~ m1_subset_1(C_841,k1_zfmisc_1(A_840))
      | v1_xboole_0(C_841)
      | v1_xboole_0(B_838)
      | v1_xboole_0(A_840) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_24451,plain,(
    ! [F_1110,E_1113,B_1114,C_1111,A_1112,D_1109] :
      ( k2_partfun1(k4_subset_1(A_1112,C_1111,D_1109),B_1114,k1_tmap_1(A_1112,B_1114,C_1111,D_1109,E_1113,F_1110),D_1109) = F_1110
      | ~ v1_funct_2(k1_tmap_1(A_1112,B_1114,C_1111,D_1109,E_1113,F_1110),k4_subset_1(A_1112,C_1111,D_1109),B_1114)
      | ~ v1_funct_1(k1_tmap_1(A_1112,B_1114,C_1111,D_1109,E_1113,F_1110))
      | k2_partfun1(D_1109,B_1114,F_1110,k9_subset_1(A_1112,C_1111,D_1109)) != k2_partfun1(C_1111,B_1114,E_1113,k9_subset_1(A_1112,C_1111,D_1109))
      | ~ m1_subset_1(F_1110,k1_zfmisc_1(k2_zfmisc_1(D_1109,B_1114)))
      | ~ v1_funct_2(F_1110,D_1109,B_1114)
      | ~ v1_funct_1(F_1110)
      | ~ m1_subset_1(E_1113,k1_zfmisc_1(k2_zfmisc_1(C_1111,B_1114)))
      | ~ v1_funct_2(E_1113,C_1111,B_1114)
      | ~ v1_funct_1(E_1113)
      | ~ m1_subset_1(D_1109,k1_zfmisc_1(A_1112))
      | v1_xboole_0(D_1109)
      | ~ m1_subset_1(C_1111,k1_zfmisc_1(A_1112))
      | v1_xboole_0(C_1111)
      | v1_xboole_0(B_1114)
      | v1_xboole_0(A_1112) ) ),
    inference(resolution,[status(thm)],[c_58,c_12335])).

tff(c_42135,plain,(
    ! [C_1354,B_1357,D_1352,F_1353,E_1356,A_1355] :
      ( k2_partfun1(k4_subset_1(A_1355,C_1354,D_1352),B_1357,k1_tmap_1(A_1355,B_1357,C_1354,D_1352,E_1356,F_1353),D_1352) = F_1353
      | ~ v1_funct_1(k1_tmap_1(A_1355,B_1357,C_1354,D_1352,E_1356,F_1353))
      | k2_partfun1(D_1352,B_1357,F_1353,k9_subset_1(A_1355,C_1354,D_1352)) != k2_partfun1(C_1354,B_1357,E_1356,k9_subset_1(A_1355,C_1354,D_1352))
      | ~ m1_subset_1(F_1353,k1_zfmisc_1(k2_zfmisc_1(D_1352,B_1357)))
      | ~ v1_funct_2(F_1353,D_1352,B_1357)
      | ~ v1_funct_1(F_1353)
      | ~ m1_subset_1(E_1356,k1_zfmisc_1(k2_zfmisc_1(C_1354,B_1357)))
      | ~ v1_funct_2(E_1356,C_1354,B_1357)
      | ~ v1_funct_1(E_1356)
      | ~ m1_subset_1(D_1352,k1_zfmisc_1(A_1355))
      | v1_xboole_0(D_1352)
      | ~ m1_subset_1(C_1354,k1_zfmisc_1(A_1355))
      | v1_xboole_0(C_1354)
      | v1_xboole_0(B_1357)
      | v1_xboole_0(A_1355) ) ),
    inference(resolution,[status(thm)],[c_60,c_24451])).

tff(c_42144,plain,(
    ! [A_1355,C_1354,E_1356] :
      ( k2_partfun1(k4_subset_1(A_1355,C_1354,'#skF_4'),'#skF_2',k1_tmap_1(A_1355,'#skF_2',C_1354,'#skF_4',E_1356,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1355,'#skF_2',C_1354,'#skF_4',E_1356,'#skF_6'))
      | k2_partfun1(C_1354,'#skF_2',E_1356,k9_subset_1(A_1355,C_1354,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1355,C_1354,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1356,k1_zfmisc_1(k2_zfmisc_1(C_1354,'#skF_2')))
      | ~ v1_funct_2(E_1356,C_1354,'#skF_2')
      | ~ v1_funct_1(E_1356)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1355))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1354,k1_zfmisc_1(A_1355))
      | v1_xboole_0(C_1354)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1355) ) ),
    inference(resolution,[status(thm)],[c_66,c_42135])).

tff(c_42153,plain,(
    ! [A_1355,C_1354,E_1356] :
      ( k2_partfun1(k4_subset_1(A_1355,C_1354,'#skF_4'),'#skF_2',k1_tmap_1(A_1355,'#skF_2',C_1354,'#skF_4',E_1356,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1355,'#skF_2',C_1354,'#skF_4',E_1356,'#skF_6'))
      | k2_partfun1(C_1354,'#skF_2',E_1356,k9_subset_1(A_1355,C_1354,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1355,C_1354,'#skF_4'))
      | ~ m1_subset_1(E_1356,k1_zfmisc_1(k2_zfmisc_1(C_1354,'#skF_2')))
      | ~ v1_funct_2(E_1356,C_1354,'#skF_2')
      | ~ v1_funct_1(E_1356)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1355))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1354,k1_zfmisc_1(A_1355))
      | v1_xboole_0(C_1354)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_10951,c_42144])).

tff(c_62536,plain,(
    ! [A_1561,C_1562,E_1563] :
      ( k2_partfun1(k4_subset_1(A_1561,C_1562,'#skF_4'),'#skF_2',k1_tmap_1(A_1561,'#skF_2',C_1562,'#skF_4',E_1563,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1561,'#skF_2',C_1562,'#skF_4',E_1563,'#skF_6'))
      | k2_partfun1(C_1562,'#skF_2',E_1563,k9_subset_1(A_1561,C_1562,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1561,C_1562,'#skF_4'))
      | ~ m1_subset_1(E_1563,k1_zfmisc_1(k2_zfmisc_1(C_1562,'#skF_2')))
      | ~ v1_funct_2(E_1563,C_1562,'#skF_2')
      | ~ v1_funct_1(E_1563)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1561))
      | ~ m1_subset_1(C_1562,k1_zfmisc_1(A_1561))
      | v1_xboole_0(C_1562)
      | v1_xboole_0(A_1561) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_42153])).

tff(c_62544,plain,(
    ! [A_1561] :
      ( k2_partfun1(k4_subset_1(A_1561,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1561,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1561,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1561,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1561,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1561))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1561))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1561) ) ),
    inference(resolution,[status(thm)],[c_72,c_62536])).

tff(c_62553,plain,(
    ! [A_1561] :
      ( k2_partfun1(k4_subset_1(A_1561,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1561,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1561,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1561,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1561,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1561))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1561))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_10948,c_62544])).

tff(c_62559,plain,(
    ! [A_1564] :
      ( k2_partfun1(k4_subset_1(A_1564,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1564,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1564,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1564,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1564,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1564))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1564))
      | v1_xboole_0(A_1564) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_62553])).

tff(c_377,plain,(
    ! [C_273,A_274,B_275] :
      ( v1_relat_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_390,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_377])).

tff(c_181,plain,(
    ! [A_254,B_255] :
      ( k3_xboole_0(A_254,B_255) = k1_xboole_0
      | ~ r1_xboole_0(A_254,B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_196,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_181])).

tff(c_141,plain,(
    ! [A_250,B_251] :
      ( k4_xboole_0(A_250,B_251) = A_250
      | ~ r1_xboole_0(A_250,B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_156,plain,(
    ! [B_8,A_7] : k4_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = B_8 ),
    inference(resolution,[status(thm)],[c_95,c_141])).

tff(c_288,plain,(
    ! [A_268,B_269] : k4_xboole_0(A_268,k4_xboole_0(A_268,B_269)) = k3_xboole_0(A_268,B_269) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_322,plain,(
    ! [B_8,A_7] : k3_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = k4_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_288])).

tff(c_339,plain,(
    ! [B_271] : k4_xboole_0(B_271,B_271) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_322])).

tff(c_359,plain,(
    ! [B_271] : r1_xboole_0(k1_xboole_0,B_271) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_10])).

tff(c_805,plain,(
    ! [A_303,B_304] :
      ( k7_relat_1(A_303,B_304) = k1_xboole_0
      | ~ r1_xboole_0(B_304,k1_relat_1(A_303))
      | ~ v1_relat_1(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_836,plain,(
    ! [A_305] :
      ( k7_relat_1(A_305,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_305) ) ),
    inference(resolution,[status(thm)],[c_359,c_805])).

tff(c_843,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_390,c_836])).

tff(c_953,plain,(
    ! [A_311,B_312] :
      ( r1_xboole_0(A_311,B_312)
      | ~ r1_subset_1(A_311,B_312)
      | v1_xboole_0(B_312)
      | v1_xboole_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5033,plain,(
    ! [A_531,B_532] :
      ( k4_xboole_0(A_531,B_532) = A_531
      | ~ r1_subset_1(A_531,B_532)
      | v1_xboole_0(B_532)
      | v1_xboole_0(A_531) ) ),
    inference(resolution,[status(thm)],[c_953,c_12])).

tff(c_5039,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_5033])).

tff(c_5044,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_5039])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_194,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(resolution,[status(thm)],[c_14,c_181])).

tff(c_5129,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5044,c_194])).

tff(c_389,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_377])).

tff(c_844,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_389,c_836])).

tff(c_2941,plain,(
    ! [A_426,B_427,C_428,D_429] :
      ( k2_partfun1(A_426,B_427,C_428,D_429) = k7_relat_1(C_428,D_429)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427)))
      | ~ v1_funct_1(C_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2948,plain,(
    ! [D_429] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_429) = k7_relat_1('#skF_6',D_429)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_2941])).

tff(c_2955,plain,(
    ! [D_429] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_429) = k7_relat_1('#skF_6',D_429) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2948])).

tff(c_2946,plain,(
    ! [D_429] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_429) = k7_relat_1('#skF_5',D_429)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_2941])).

tff(c_2952,plain,(
    ! [D_429] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_429) = k7_relat_1('#skF_5',D_429) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2946])).

tff(c_2714,plain,(
    ! [A_412,B_413,C_414] :
      ( k9_subset_1(A_412,B_413,C_414) = k3_xboole_0(B_413,C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(A_412)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2729,plain,(
    ! [B_413] : k9_subset_1('#skF_1',B_413,'#skF_4') = k3_xboole_0(B_413,'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_2714])).

tff(c_64,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_123,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2739,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2729,c_2729,c_123])).

tff(c_8141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_5129,c_844,c_5129,c_2955,c_2952,c_2739])).

tff(c_8142,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8244,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8142])).

tff(c_62576,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_62559,c_8244])).

tff(c_62598,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_9050,c_15569,c_9051,c_15569,c_9503,c_9503,c_12103,c_62576])).

tff(c_62600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_62598])).

tff(c_62601,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8142])).

tff(c_102464,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_102447,c_62601])).

tff(c_102486,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_63489,c_70423,c_63490,c_70423,c_65667,c_65667,c_69008,c_102464])).

tff(c_102488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_102486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.23/13.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.36/13.89  
% 22.36/13.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.36/13.89  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.36/13.89  
% 22.36/13.89  %Foreground sorts:
% 22.36/13.89  
% 22.36/13.89  
% 22.36/13.89  %Background operators:
% 22.36/13.89  
% 22.36/13.89  
% 22.36/13.89  %Foreground operators:
% 22.36/13.89  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 22.36/13.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.36/13.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.36/13.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.36/13.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 22.36/13.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.36/13.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.36/13.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.36/13.89  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 22.36/13.89  tff('#skF_5', type, '#skF_5': $i).
% 22.36/13.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.36/13.89  tff('#skF_6', type, '#skF_6': $i).
% 22.36/13.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.36/13.89  tff('#skF_2', type, '#skF_2': $i).
% 22.36/13.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 22.36/13.89  tff('#skF_3', type, '#skF_3': $i).
% 22.36/13.89  tff('#skF_1', type, '#skF_1': $i).
% 22.36/13.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.36/13.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.36/13.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.36/13.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.36/13.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.36/13.89  tff('#skF_4', type, '#skF_4': $i).
% 22.36/13.89  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.36/13.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.36/13.89  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 22.36/13.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.36/13.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.36/13.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.36/13.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.36/13.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 22.36/13.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.36/13.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 22.36/13.89  
% 22.57/13.92  tff(f_243, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 22.57/13.92  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 22.57/13.92  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 22.57/13.92  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 22.57/13.92  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 22.57/13.92  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 22.57/13.92  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 22.57/13.92  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 22.57/13.92  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 22.57/13.92  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 22.57/13.92  tff(f_201, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 22.57/13.92  tff(f_119, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 22.57/13.92  tff(f_167, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 22.57/13.92  tff(c_90, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_62781, plain, (![C_1578, A_1579, B_1580]: (v1_relat_1(C_1578) | ~m1_subset_1(C_1578, k1_zfmisc_1(k2_zfmisc_1(A_1579, B_1580))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.57/13.92  tff(c_62794, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_62781])).
% 22.57/13.92  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.57/13.92  tff(c_92, plain, (![B_236, A_237]: (r1_xboole_0(B_236, A_237) | ~r1_xboole_0(A_237, B_236))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.57/13.92  tff(c_95, plain, (![B_8, A_7]: (r1_xboole_0(B_8, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_10, c_92])).
% 22.57/13.92  tff(c_8196, plain, (![A_608, B_609]: (k3_xboole_0(A_608, B_609)=k1_xboole_0 | ~r1_xboole_0(A_608, B_609))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.57/13.92  tff(c_8211, plain, (![B_8, A_7]: (k3_xboole_0(B_8, k4_xboole_0(A_7, B_8))=k1_xboole_0)), inference(resolution, [status(thm)], [c_95, c_8196])).
% 22.57/13.92  tff(c_8156, plain, (![A_604, B_605]: (k4_xboole_0(A_604, B_605)=A_604 | ~r1_xboole_0(A_604, B_605))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.57/13.92  tff(c_8171, plain, (![B_8, A_7]: (k4_xboole_0(B_8, k4_xboole_0(A_7, B_8))=B_8)), inference(resolution, [status(thm)], [c_95, c_8156])).
% 22.57/13.92  tff(c_62651, plain, (![A_1571, B_1572]: (k4_xboole_0(A_1571, k4_xboole_0(A_1571, B_1572))=k3_xboole_0(A_1571, B_1572))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.57/13.92  tff(c_62685, plain, (![B_8, A_7]: (k3_xboole_0(B_8, k4_xboole_0(A_7, B_8))=k4_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8171, c_62651])).
% 22.57/13.92  tff(c_62702, plain, (![B_1574]: (k4_xboole_0(B_1574, B_1574)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8211, c_62685])).
% 22.57/13.92  tff(c_62722, plain, (![B_1574]: (r1_xboole_0(k1_xboole_0, B_1574))), inference(superposition, [status(thm), theory('equality')], [c_62702, c_10])).
% 22.57/13.92  tff(c_63451, plain, (![A_1621, B_1622]: (k7_relat_1(A_1621, B_1622)=k1_xboole_0 | ~r1_xboole_0(B_1622, k1_relat_1(A_1621)) | ~v1_relat_1(A_1621))), inference(cnfTransformation, [status(thm)], [f_71])).
% 22.57/13.92  tff(c_63482, plain, (![A_1623]: (k7_relat_1(A_1623, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_1623))), inference(resolution, [status(thm)], [c_62722, c_63451])).
% 22.57/13.92  tff(c_63489, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_62794, c_63482])).
% 22.57/13.92  tff(c_86, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_82, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_78, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_63615, plain, (![A_1628, B_1629]: (r1_xboole_0(A_1628, B_1629) | ~r1_subset_1(A_1628, B_1629) | v1_xboole_0(B_1629) | v1_xboole_0(A_1628))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.57/13.92  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.57/13.92  tff(c_70393, plain, (![A_1906, B_1907]: (k3_xboole_0(A_1906, B_1907)=k1_xboole_0 | ~r1_subset_1(A_1906, B_1907) | v1_xboole_0(B_1907) | v1_xboole_0(A_1906))), inference(resolution, [status(thm)], [c_63615, c_2])).
% 22.57/13.92  tff(c_70411, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_70393])).
% 22.57/13.92  tff(c_70423, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_70411])).
% 22.57/13.92  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_62793, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_62781])).
% 22.57/13.92  tff(c_63490, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_62793, c_63482])).
% 22.57/13.92  tff(c_65652, plain, (![A_1732, B_1733, C_1734]: (k9_subset_1(A_1732, B_1733, C_1734)=k3_xboole_0(B_1733, C_1734) | ~m1_subset_1(C_1734, k1_zfmisc_1(A_1732)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.57/13.92  tff(c_65667, plain, (![B_1733]: (k9_subset_1('#skF_1', B_1733, '#skF_4')=k3_xboole_0(B_1733, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_65652])).
% 22.57/13.92  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_88, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_66270, plain, (![B_1768, A_1766, E_1767, C_1765, D_1763, F_1764]: (v1_funct_1(k1_tmap_1(A_1766, B_1768, C_1765, D_1763, E_1767, F_1764)) | ~m1_subset_1(F_1764, k1_zfmisc_1(k2_zfmisc_1(D_1763, B_1768))) | ~v1_funct_2(F_1764, D_1763, B_1768) | ~v1_funct_1(F_1764) | ~m1_subset_1(E_1767, k1_zfmisc_1(k2_zfmisc_1(C_1765, B_1768))) | ~v1_funct_2(E_1767, C_1765, B_1768) | ~v1_funct_1(E_1767) | ~m1_subset_1(D_1763, k1_zfmisc_1(A_1766)) | v1_xboole_0(D_1763) | ~m1_subset_1(C_1765, k1_zfmisc_1(A_1766)) | v1_xboole_0(C_1765) | v1_xboole_0(B_1768) | v1_xboole_0(A_1766))), inference(cnfTransformation, [status(thm)], [f_201])).
% 22.57/13.92  tff(c_66277, plain, (![A_1766, C_1765, E_1767]: (v1_funct_1(k1_tmap_1(A_1766, '#skF_2', C_1765, '#skF_4', E_1767, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1767, k1_zfmisc_1(k2_zfmisc_1(C_1765, '#skF_2'))) | ~v1_funct_2(E_1767, C_1765, '#skF_2') | ~v1_funct_1(E_1767) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1766)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1765, k1_zfmisc_1(A_1766)) | v1_xboole_0(C_1765) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1766))), inference(resolution, [status(thm)], [c_66, c_66270])).
% 22.57/13.92  tff(c_66285, plain, (![A_1766, C_1765, E_1767]: (v1_funct_1(k1_tmap_1(A_1766, '#skF_2', C_1765, '#skF_4', E_1767, '#skF_6')) | ~m1_subset_1(E_1767, k1_zfmisc_1(k2_zfmisc_1(C_1765, '#skF_2'))) | ~v1_funct_2(E_1767, C_1765, '#skF_2') | ~v1_funct_1(E_1767) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1766)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1765, k1_zfmisc_1(A_1766)) | v1_xboole_0(C_1765) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1766))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66277])).
% 22.57/13.92  tff(c_67352, plain, (![A_1830, C_1831, E_1832]: (v1_funct_1(k1_tmap_1(A_1830, '#skF_2', C_1831, '#skF_4', E_1832, '#skF_6')) | ~m1_subset_1(E_1832, k1_zfmisc_1(k2_zfmisc_1(C_1831, '#skF_2'))) | ~v1_funct_2(E_1832, C_1831, '#skF_2') | ~v1_funct_1(E_1832) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1830)) | ~m1_subset_1(C_1831, k1_zfmisc_1(A_1830)) | v1_xboole_0(C_1831) | v1_xboole_0(A_1830))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_66285])).
% 22.57/13.92  tff(c_67360, plain, (![A_1830]: (v1_funct_1(k1_tmap_1(A_1830, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1830)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1830)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1830))), inference(resolution, [status(thm)], [c_72, c_67352])).
% 22.57/13.92  tff(c_67369, plain, (![A_1830]: (v1_funct_1(k1_tmap_1(A_1830, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1830)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1830)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1830))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_67360])).
% 22.57/13.92  tff(c_68996, plain, (![A_1868]: (v1_funct_1(k1_tmap_1(A_1868, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1868)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1868)) | v1_xboole_0(A_1868))), inference(negUnitSimplification, [status(thm)], [c_86, c_67369])).
% 22.57/13.92  tff(c_69003, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_68996])).
% 22.57/13.92  tff(c_69007, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_69003])).
% 22.57/13.92  tff(c_69008, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_90, c_69007])).
% 22.57/13.92  tff(c_65831, plain, (![A_1742, B_1743, C_1744, D_1745]: (k2_partfun1(A_1742, B_1743, C_1744, D_1745)=k7_relat_1(C_1744, D_1745) | ~m1_subset_1(C_1744, k1_zfmisc_1(k2_zfmisc_1(A_1742, B_1743))) | ~v1_funct_1(C_1744))), inference(cnfTransformation, [status(thm)], [f_119])).
% 22.57/13.92  tff(c_65836, plain, (![D_1745]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1745)=k7_relat_1('#skF_5', D_1745) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_65831])).
% 22.57/13.92  tff(c_65842, plain, (![D_1745]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1745)=k7_relat_1('#skF_5', D_1745))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_65836])).
% 22.57/13.92  tff(c_65838, plain, (![D_1745]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1745)=k7_relat_1('#skF_6', D_1745) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_65831])).
% 22.57/13.92  tff(c_65845, plain, (![D_1745]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1745)=k7_relat_1('#skF_6', D_1745))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_65838])).
% 22.57/13.92  tff(c_60, plain, (![B_172, A_171, C_173, E_175, F_176, D_174]: (v1_funct_2(k1_tmap_1(A_171, B_172, C_173, D_174, E_175, F_176), k4_subset_1(A_171, C_173, D_174), B_172) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(D_174, B_172))) | ~v1_funct_2(F_176, D_174, B_172) | ~v1_funct_1(F_176) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(C_173, B_172))) | ~v1_funct_2(E_175, C_173, B_172) | ~v1_funct_1(E_175) | ~m1_subset_1(D_174, k1_zfmisc_1(A_171)) | v1_xboole_0(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | v1_xboole_0(C_173) | v1_xboole_0(B_172) | v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_201])).
% 22.57/13.92  tff(c_58, plain, (![B_172, A_171, C_173, E_175, F_176, D_174]: (m1_subset_1(k1_tmap_1(A_171, B_172, C_173, D_174, E_175, F_176), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_171, C_173, D_174), B_172))) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(D_174, B_172))) | ~v1_funct_2(F_176, D_174, B_172) | ~v1_funct_1(F_176) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(C_173, B_172))) | ~v1_funct_2(E_175, C_173, B_172) | ~v1_funct_1(E_175) | ~m1_subset_1(D_174, k1_zfmisc_1(A_171)) | v1_xboole_0(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(A_171)) | v1_xboole_0(C_173) | v1_xboole_0(B_172) | v1_xboole_0(A_171))), inference(cnfTransformation, [status(thm)], [f_201])).
% 22.57/13.92  tff(c_67318, plain, (![E_1824, B_1823, F_1822, A_1825, D_1827, C_1826]: (k2_partfun1(k4_subset_1(A_1825, C_1826, D_1827), B_1823, k1_tmap_1(A_1825, B_1823, C_1826, D_1827, E_1824, F_1822), C_1826)=E_1824 | ~m1_subset_1(k1_tmap_1(A_1825, B_1823, C_1826, D_1827, E_1824, F_1822), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1825, C_1826, D_1827), B_1823))) | ~v1_funct_2(k1_tmap_1(A_1825, B_1823, C_1826, D_1827, E_1824, F_1822), k4_subset_1(A_1825, C_1826, D_1827), B_1823) | ~v1_funct_1(k1_tmap_1(A_1825, B_1823, C_1826, D_1827, E_1824, F_1822)) | k2_partfun1(D_1827, B_1823, F_1822, k9_subset_1(A_1825, C_1826, D_1827))!=k2_partfun1(C_1826, B_1823, E_1824, k9_subset_1(A_1825, C_1826, D_1827)) | ~m1_subset_1(F_1822, k1_zfmisc_1(k2_zfmisc_1(D_1827, B_1823))) | ~v1_funct_2(F_1822, D_1827, B_1823) | ~v1_funct_1(F_1822) | ~m1_subset_1(E_1824, k1_zfmisc_1(k2_zfmisc_1(C_1826, B_1823))) | ~v1_funct_2(E_1824, C_1826, B_1823) | ~v1_funct_1(E_1824) | ~m1_subset_1(D_1827, k1_zfmisc_1(A_1825)) | v1_xboole_0(D_1827) | ~m1_subset_1(C_1826, k1_zfmisc_1(A_1825)) | v1_xboole_0(C_1826) | v1_xboole_0(B_1823) | v1_xboole_0(A_1825))), inference(cnfTransformation, [status(thm)], [f_167])).
% 22.57/13.92  tff(c_79053, plain, (![F_2092, B_2096, A_2094, E_2095, C_2093, D_2091]: (k2_partfun1(k4_subset_1(A_2094, C_2093, D_2091), B_2096, k1_tmap_1(A_2094, B_2096, C_2093, D_2091, E_2095, F_2092), C_2093)=E_2095 | ~v1_funct_2(k1_tmap_1(A_2094, B_2096, C_2093, D_2091, E_2095, F_2092), k4_subset_1(A_2094, C_2093, D_2091), B_2096) | ~v1_funct_1(k1_tmap_1(A_2094, B_2096, C_2093, D_2091, E_2095, F_2092)) | k2_partfun1(D_2091, B_2096, F_2092, k9_subset_1(A_2094, C_2093, D_2091))!=k2_partfun1(C_2093, B_2096, E_2095, k9_subset_1(A_2094, C_2093, D_2091)) | ~m1_subset_1(F_2092, k1_zfmisc_1(k2_zfmisc_1(D_2091, B_2096))) | ~v1_funct_2(F_2092, D_2091, B_2096) | ~v1_funct_1(F_2092) | ~m1_subset_1(E_2095, k1_zfmisc_1(k2_zfmisc_1(C_2093, B_2096))) | ~v1_funct_2(E_2095, C_2093, B_2096) | ~v1_funct_1(E_2095) | ~m1_subset_1(D_2091, k1_zfmisc_1(A_2094)) | v1_xboole_0(D_2091) | ~m1_subset_1(C_2093, k1_zfmisc_1(A_2094)) | v1_xboole_0(C_2093) | v1_xboole_0(B_2096) | v1_xboole_0(A_2094))), inference(resolution, [status(thm)], [c_58, c_67318])).
% 22.57/13.92  tff(c_97539, plain, (![E_2338, A_2337, F_2335, B_2339, C_2336, D_2334]: (k2_partfun1(k4_subset_1(A_2337, C_2336, D_2334), B_2339, k1_tmap_1(A_2337, B_2339, C_2336, D_2334, E_2338, F_2335), C_2336)=E_2338 | ~v1_funct_1(k1_tmap_1(A_2337, B_2339, C_2336, D_2334, E_2338, F_2335)) | k2_partfun1(D_2334, B_2339, F_2335, k9_subset_1(A_2337, C_2336, D_2334))!=k2_partfun1(C_2336, B_2339, E_2338, k9_subset_1(A_2337, C_2336, D_2334)) | ~m1_subset_1(F_2335, k1_zfmisc_1(k2_zfmisc_1(D_2334, B_2339))) | ~v1_funct_2(F_2335, D_2334, B_2339) | ~v1_funct_1(F_2335) | ~m1_subset_1(E_2338, k1_zfmisc_1(k2_zfmisc_1(C_2336, B_2339))) | ~v1_funct_2(E_2338, C_2336, B_2339) | ~v1_funct_1(E_2338) | ~m1_subset_1(D_2334, k1_zfmisc_1(A_2337)) | v1_xboole_0(D_2334) | ~m1_subset_1(C_2336, k1_zfmisc_1(A_2337)) | v1_xboole_0(C_2336) | v1_xboole_0(B_2339) | v1_xboole_0(A_2337))), inference(resolution, [status(thm)], [c_60, c_79053])).
% 22.57/13.92  tff(c_97548, plain, (![A_2337, C_2336, E_2338]: (k2_partfun1(k4_subset_1(A_2337, C_2336, '#skF_4'), '#skF_2', k1_tmap_1(A_2337, '#skF_2', C_2336, '#skF_4', E_2338, '#skF_6'), C_2336)=E_2338 | ~v1_funct_1(k1_tmap_1(A_2337, '#skF_2', C_2336, '#skF_4', E_2338, '#skF_6')) | k2_partfun1(C_2336, '#skF_2', E_2338, k9_subset_1(A_2337, C_2336, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_2337, C_2336, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2338, k1_zfmisc_1(k2_zfmisc_1(C_2336, '#skF_2'))) | ~v1_funct_2(E_2338, C_2336, '#skF_2') | ~v1_funct_1(E_2338) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2337)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2336, k1_zfmisc_1(A_2337)) | v1_xboole_0(C_2336) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2337))), inference(resolution, [status(thm)], [c_66, c_97539])).
% 22.57/13.92  tff(c_97557, plain, (![A_2337, C_2336, E_2338]: (k2_partfun1(k4_subset_1(A_2337, C_2336, '#skF_4'), '#skF_2', k1_tmap_1(A_2337, '#skF_2', C_2336, '#skF_4', E_2338, '#skF_6'), C_2336)=E_2338 | ~v1_funct_1(k1_tmap_1(A_2337, '#skF_2', C_2336, '#skF_4', E_2338, '#skF_6')) | k2_partfun1(C_2336, '#skF_2', E_2338, k9_subset_1(A_2337, C_2336, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2337, C_2336, '#skF_4')) | ~m1_subset_1(E_2338, k1_zfmisc_1(k2_zfmisc_1(C_2336, '#skF_2'))) | ~v1_funct_2(E_2338, C_2336, '#skF_2') | ~v1_funct_1(E_2338) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2337)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2336, k1_zfmisc_1(A_2337)) | v1_xboole_0(C_2336) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2337))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_65845, c_97548])).
% 22.57/13.92  tff(c_100831, plain, (![A_2382, C_2383, E_2384]: (k2_partfun1(k4_subset_1(A_2382, C_2383, '#skF_4'), '#skF_2', k1_tmap_1(A_2382, '#skF_2', C_2383, '#skF_4', E_2384, '#skF_6'), C_2383)=E_2384 | ~v1_funct_1(k1_tmap_1(A_2382, '#skF_2', C_2383, '#skF_4', E_2384, '#skF_6')) | k2_partfun1(C_2383, '#skF_2', E_2384, k9_subset_1(A_2382, C_2383, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2382, C_2383, '#skF_4')) | ~m1_subset_1(E_2384, k1_zfmisc_1(k2_zfmisc_1(C_2383, '#skF_2'))) | ~v1_funct_2(E_2384, C_2383, '#skF_2') | ~v1_funct_1(E_2384) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2382)) | ~m1_subset_1(C_2383, k1_zfmisc_1(A_2382)) | v1_xboole_0(C_2383) | v1_xboole_0(A_2382))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_97557])).
% 22.57/13.92  tff(c_100839, plain, (![A_2382]: (k2_partfun1(k4_subset_1(A_2382, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2382, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2382, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2382, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2382, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2382)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2382)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2382))), inference(resolution, [status(thm)], [c_72, c_100831])).
% 22.57/13.92  tff(c_100848, plain, (![A_2382]: (k2_partfun1(k4_subset_1(A_2382, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2382, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2382, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2382, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2382, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2382)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2382)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2382))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_65842, c_100839])).
% 22.57/13.92  tff(c_102447, plain, (![A_2430]: (k2_partfun1(k4_subset_1(A_2430, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2430, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2430, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2430, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2430, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2430)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2430)) | v1_xboole_0(A_2430))), inference(negUnitSimplification, [status(thm)], [c_86, c_100848])).
% 22.57/13.92  tff(c_8423, plain, (![C_629, A_630, B_631]: (v1_relat_1(C_629) | ~m1_subset_1(C_629, k1_zfmisc_1(k2_zfmisc_1(A_630, B_631))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.57/13.92  tff(c_8436, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_8423])).
% 22.57/13.92  tff(c_8293, plain, (![A_622, B_623]: (k4_xboole_0(A_622, k4_xboole_0(A_622, B_623))=k3_xboole_0(A_622, B_623))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.57/13.92  tff(c_8327, plain, (![B_8, A_7]: (k3_xboole_0(B_8, k4_xboole_0(A_7, B_8))=k4_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8171, c_8293])).
% 22.57/13.92  tff(c_8344, plain, (![B_625]: (k4_xboole_0(B_625, B_625)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8211, c_8327])).
% 22.57/13.92  tff(c_8364, plain, (![B_625]: (r1_xboole_0(k1_xboole_0, B_625))), inference(superposition, [status(thm), theory('equality')], [c_8344, c_10])).
% 22.57/13.92  tff(c_9012, plain, (![A_666, B_667]: (k7_relat_1(A_666, B_667)=k1_xboole_0 | ~r1_xboole_0(B_667, k1_relat_1(A_666)) | ~v1_relat_1(A_666))), inference(cnfTransformation, [status(thm)], [f_71])).
% 22.57/13.92  tff(c_9043, plain, (![A_668]: (k7_relat_1(A_668, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_668))), inference(resolution, [status(thm)], [c_8364, c_9012])).
% 22.57/13.92  tff(c_9050, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8436, c_9043])).
% 22.57/13.92  tff(c_9354, plain, (![A_680, B_681]: (r1_xboole_0(A_680, B_681) | ~r1_subset_1(A_680, B_681) | v1_xboole_0(B_681) | v1_xboole_0(A_680))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.57/13.92  tff(c_15539, plain, (![A_923, B_924]: (k3_xboole_0(A_923, B_924)=k1_xboole_0 | ~r1_subset_1(A_923, B_924) | v1_xboole_0(B_924) | v1_xboole_0(A_923))), inference(resolution, [status(thm)], [c_9354, c_2])).
% 22.57/13.92  tff(c_15557, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_15539])).
% 22.57/13.92  tff(c_15569, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_15557])).
% 22.57/13.92  tff(c_8435, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_8423])).
% 22.57/13.92  tff(c_9051, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8435, c_9043])).
% 22.57/13.92  tff(c_9488, plain, (![A_686, B_687, C_688]: (k9_subset_1(A_686, B_687, C_688)=k3_xboole_0(B_687, C_688) | ~m1_subset_1(C_688, k1_zfmisc_1(A_686)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.57/13.92  tff(c_9503, plain, (![B_687]: (k9_subset_1('#skF_1', B_687, '#skF_4')=k3_xboole_0(B_687, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_9488])).
% 22.57/13.92  tff(c_11601, plain, (![C_782, F_781, A_783, B_785, D_780, E_784]: (v1_funct_1(k1_tmap_1(A_783, B_785, C_782, D_780, E_784, F_781)) | ~m1_subset_1(F_781, k1_zfmisc_1(k2_zfmisc_1(D_780, B_785))) | ~v1_funct_2(F_781, D_780, B_785) | ~v1_funct_1(F_781) | ~m1_subset_1(E_784, k1_zfmisc_1(k2_zfmisc_1(C_782, B_785))) | ~v1_funct_2(E_784, C_782, B_785) | ~v1_funct_1(E_784) | ~m1_subset_1(D_780, k1_zfmisc_1(A_783)) | v1_xboole_0(D_780) | ~m1_subset_1(C_782, k1_zfmisc_1(A_783)) | v1_xboole_0(C_782) | v1_xboole_0(B_785) | v1_xboole_0(A_783))), inference(cnfTransformation, [status(thm)], [f_201])).
% 22.57/13.92  tff(c_11608, plain, (![A_783, C_782, E_784]: (v1_funct_1(k1_tmap_1(A_783, '#skF_2', C_782, '#skF_4', E_784, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_784, k1_zfmisc_1(k2_zfmisc_1(C_782, '#skF_2'))) | ~v1_funct_2(E_784, C_782, '#skF_2') | ~v1_funct_1(E_784) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_783)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_782, k1_zfmisc_1(A_783)) | v1_xboole_0(C_782) | v1_xboole_0('#skF_2') | v1_xboole_0(A_783))), inference(resolution, [status(thm)], [c_66, c_11601])).
% 22.57/13.92  tff(c_11616, plain, (![A_783, C_782, E_784]: (v1_funct_1(k1_tmap_1(A_783, '#skF_2', C_782, '#skF_4', E_784, '#skF_6')) | ~m1_subset_1(E_784, k1_zfmisc_1(k2_zfmisc_1(C_782, '#skF_2'))) | ~v1_funct_2(E_784, C_782, '#skF_2') | ~v1_funct_1(E_784) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_783)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_782, k1_zfmisc_1(A_783)) | v1_xboole_0(C_782) | v1_xboole_0('#skF_2') | v1_xboole_0(A_783))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_11608])).
% 22.57/13.92  tff(c_11634, plain, (![A_788, C_789, E_790]: (v1_funct_1(k1_tmap_1(A_788, '#skF_2', C_789, '#skF_4', E_790, '#skF_6')) | ~m1_subset_1(E_790, k1_zfmisc_1(k2_zfmisc_1(C_789, '#skF_2'))) | ~v1_funct_2(E_790, C_789, '#skF_2') | ~v1_funct_1(E_790) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_788)) | ~m1_subset_1(C_789, k1_zfmisc_1(A_788)) | v1_xboole_0(C_789) | v1_xboole_0(A_788))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_11616])).
% 22.57/13.92  tff(c_11639, plain, (![A_788]: (v1_funct_1(k1_tmap_1(A_788, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_788)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_788)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_788))), inference(resolution, [status(thm)], [c_72, c_11634])).
% 22.57/13.92  tff(c_11645, plain, (![A_788]: (v1_funct_1(k1_tmap_1(A_788, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_788)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_788)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_788))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_11639])).
% 22.57/13.92  tff(c_12091, plain, (![A_816]: (v1_funct_1(k1_tmap_1(A_816, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_816)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_816)) | v1_xboole_0(A_816))), inference(negUnitSimplification, [status(thm)], [c_86, c_11645])).
% 22.57/13.92  tff(c_12098, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_12091])).
% 22.57/13.92  tff(c_12102, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12098])).
% 22.57/13.92  tff(c_12103, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_90, c_12102])).
% 22.57/13.92  tff(c_10937, plain, (![A_758, B_759, C_760, D_761]: (k2_partfun1(A_758, B_759, C_760, D_761)=k7_relat_1(C_760, D_761) | ~m1_subset_1(C_760, k1_zfmisc_1(k2_zfmisc_1(A_758, B_759))) | ~v1_funct_1(C_760))), inference(cnfTransformation, [status(thm)], [f_119])).
% 22.57/13.92  tff(c_10942, plain, (![D_761]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_761)=k7_relat_1('#skF_5', D_761) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_10937])).
% 22.57/13.92  tff(c_10948, plain, (![D_761]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_761)=k7_relat_1('#skF_5', D_761))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10942])).
% 22.57/13.92  tff(c_10944, plain, (![D_761]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_761)=k7_relat_1('#skF_6', D_761) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_10937])).
% 22.57/13.92  tff(c_10951, plain, (![D_761]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_761)=k7_relat_1('#skF_6', D_761))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10944])).
% 22.57/13.92  tff(c_12335, plain, (![C_841, D_842, B_838, F_837, E_839, A_840]: (k2_partfun1(k4_subset_1(A_840, C_841, D_842), B_838, k1_tmap_1(A_840, B_838, C_841, D_842, E_839, F_837), D_842)=F_837 | ~m1_subset_1(k1_tmap_1(A_840, B_838, C_841, D_842, E_839, F_837), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_840, C_841, D_842), B_838))) | ~v1_funct_2(k1_tmap_1(A_840, B_838, C_841, D_842, E_839, F_837), k4_subset_1(A_840, C_841, D_842), B_838) | ~v1_funct_1(k1_tmap_1(A_840, B_838, C_841, D_842, E_839, F_837)) | k2_partfun1(D_842, B_838, F_837, k9_subset_1(A_840, C_841, D_842))!=k2_partfun1(C_841, B_838, E_839, k9_subset_1(A_840, C_841, D_842)) | ~m1_subset_1(F_837, k1_zfmisc_1(k2_zfmisc_1(D_842, B_838))) | ~v1_funct_2(F_837, D_842, B_838) | ~v1_funct_1(F_837) | ~m1_subset_1(E_839, k1_zfmisc_1(k2_zfmisc_1(C_841, B_838))) | ~v1_funct_2(E_839, C_841, B_838) | ~v1_funct_1(E_839) | ~m1_subset_1(D_842, k1_zfmisc_1(A_840)) | v1_xboole_0(D_842) | ~m1_subset_1(C_841, k1_zfmisc_1(A_840)) | v1_xboole_0(C_841) | v1_xboole_0(B_838) | v1_xboole_0(A_840))), inference(cnfTransformation, [status(thm)], [f_167])).
% 22.57/13.92  tff(c_24451, plain, (![F_1110, E_1113, B_1114, C_1111, A_1112, D_1109]: (k2_partfun1(k4_subset_1(A_1112, C_1111, D_1109), B_1114, k1_tmap_1(A_1112, B_1114, C_1111, D_1109, E_1113, F_1110), D_1109)=F_1110 | ~v1_funct_2(k1_tmap_1(A_1112, B_1114, C_1111, D_1109, E_1113, F_1110), k4_subset_1(A_1112, C_1111, D_1109), B_1114) | ~v1_funct_1(k1_tmap_1(A_1112, B_1114, C_1111, D_1109, E_1113, F_1110)) | k2_partfun1(D_1109, B_1114, F_1110, k9_subset_1(A_1112, C_1111, D_1109))!=k2_partfun1(C_1111, B_1114, E_1113, k9_subset_1(A_1112, C_1111, D_1109)) | ~m1_subset_1(F_1110, k1_zfmisc_1(k2_zfmisc_1(D_1109, B_1114))) | ~v1_funct_2(F_1110, D_1109, B_1114) | ~v1_funct_1(F_1110) | ~m1_subset_1(E_1113, k1_zfmisc_1(k2_zfmisc_1(C_1111, B_1114))) | ~v1_funct_2(E_1113, C_1111, B_1114) | ~v1_funct_1(E_1113) | ~m1_subset_1(D_1109, k1_zfmisc_1(A_1112)) | v1_xboole_0(D_1109) | ~m1_subset_1(C_1111, k1_zfmisc_1(A_1112)) | v1_xboole_0(C_1111) | v1_xboole_0(B_1114) | v1_xboole_0(A_1112))), inference(resolution, [status(thm)], [c_58, c_12335])).
% 22.57/13.92  tff(c_42135, plain, (![C_1354, B_1357, D_1352, F_1353, E_1356, A_1355]: (k2_partfun1(k4_subset_1(A_1355, C_1354, D_1352), B_1357, k1_tmap_1(A_1355, B_1357, C_1354, D_1352, E_1356, F_1353), D_1352)=F_1353 | ~v1_funct_1(k1_tmap_1(A_1355, B_1357, C_1354, D_1352, E_1356, F_1353)) | k2_partfun1(D_1352, B_1357, F_1353, k9_subset_1(A_1355, C_1354, D_1352))!=k2_partfun1(C_1354, B_1357, E_1356, k9_subset_1(A_1355, C_1354, D_1352)) | ~m1_subset_1(F_1353, k1_zfmisc_1(k2_zfmisc_1(D_1352, B_1357))) | ~v1_funct_2(F_1353, D_1352, B_1357) | ~v1_funct_1(F_1353) | ~m1_subset_1(E_1356, k1_zfmisc_1(k2_zfmisc_1(C_1354, B_1357))) | ~v1_funct_2(E_1356, C_1354, B_1357) | ~v1_funct_1(E_1356) | ~m1_subset_1(D_1352, k1_zfmisc_1(A_1355)) | v1_xboole_0(D_1352) | ~m1_subset_1(C_1354, k1_zfmisc_1(A_1355)) | v1_xboole_0(C_1354) | v1_xboole_0(B_1357) | v1_xboole_0(A_1355))), inference(resolution, [status(thm)], [c_60, c_24451])).
% 22.57/13.92  tff(c_42144, plain, (![A_1355, C_1354, E_1356]: (k2_partfun1(k4_subset_1(A_1355, C_1354, '#skF_4'), '#skF_2', k1_tmap_1(A_1355, '#skF_2', C_1354, '#skF_4', E_1356, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1355, '#skF_2', C_1354, '#skF_4', E_1356, '#skF_6')) | k2_partfun1(C_1354, '#skF_2', E_1356, k9_subset_1(A_1355, C_1354, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1355, C_1354, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1356, k1_zfmisc_1(k2_zfmisc_1(C_1354, '#skF_2'))) | ~v1_funct_2(E_1356, C_1354, '#skF_2') | ~v1_funct_1(E_1356) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1355)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1354, k1_zfmisc_1(A_1355)) | v1_xboole_0(C_1354) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1355))), inference(resolution, [status(thm)], [c_66, c_42135])).
% 22.57/13.92  tff(c_42153, plain, (![A_1355, C_1354, E_1356]: (k2_partfun1(k4_subset_1(A_1355, C_1354, '#skF_4'), '#skF_2', k1_tmap_1(A_1355, '#skF_2', C_1354, '#skF_4', E_1356, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1355, '#skF_2', C_1354, '#skF_4', E_1356, '#skF_6')) | k2_partfun1(C_1354, '#skF_2', E_1356, k9_subset_1(A_1355, C_1354, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1355, C_1354, '#skF_4')) | ~m1_subset_1(E_1356, k1_zfmisc_1(k2_zfmisc_1(C_1354, '#skF_2'))) | ~v1_funct_2(E_1356, C_1354, '#skF_2') | ~v1_funct_1(E_1356) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1355)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1354, k1_zfmisc_1(A_1355)) | v1_xboole_0(C_1354) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1355))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_10951, c_42144])).
% 22.57/13.92  tff(c_62536, plain, (![A_1561, C_1562, E_1563]: (k2_partfun1(k4_subset_1(A_1561, C_1562, '#skF_4'), '#skF_2', k1_tmap_1(A_1561, '#skF_2', C_1562, '#skF_4', E_1563, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1561, '#skF_2', C_1562, '#skF_4', E_1563, '#skF_6')) | k2_partfun1(C_1562, '#skF_2', E_1563, k9_subset_1(A_1561, C_1562, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1561, C_1562, '#skF_4')) | ~m1_subset_1(E_1563, k1_zfmisc_1(k2_zfmisc_1(C_1562, '#skF_2'))) | ~v1_funct_2(E_1563, C_1562, '#skF_2') | ~v1_funct_1(E_1563) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1561)) | ~m1_subset_1(C_1562, k1_zfmisc_1(A_1561)) | v1_xboole_0(C_1562) | v1_xboole_0(A_1561))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_42153])).
% 22.57/13.92  tff(c_62544, plain, (![A_1561]: (k2_partfun1(k4_subset_1(A_1561, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1561, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1561, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1561, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1561, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1561)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1561)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1561))), inference(resolution, [status(thm)], [c_72, c_62536])).
% 22.57/13.92  tff(c_62553, plain, (![A_1561]: (k2_partfun1(k4_subset_1(A_1561, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1561, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1561, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1561, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1561, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1561)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1561)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1561))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_10948, c_62544])).
% 22.57/13.92  tff(c_62559, plain, (![A_1564]: (k2_partfun1(k4_subset_1(A_1564, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1564, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1564, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1564, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1564, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1564)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1564)) | v1_xboole_0(A_1564))), inference(negUnitSimplification, [status(thm)], [c_86, c_62553])).
% 22.57/13.92  tff(c_377, plain, (![C_273, A_274, B_275]: (v1_relat_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.57/13.92  tff(c_390, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_377])).
% 22.57/13.92  tff(c_181, plain, (![A_254, B_255]: (k3_xboole_0(A_254, B_255)=k1_xboole_0 | ~r1_xboole_0(A_254, B_255))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.57/13.92  tff(c_196, plain, (![B_8, A_7]: (k3_xboole_0(B_8, k4_xboole_0(A_7, B_8))=k1_xboole_0)), inference(resolution, [status(thm)], [c_95, c_181])).
% 22.57/13.92  tff(c_141, plain, (![A_250, B_251]: (k4_xboole_0(A_250, B_251)=A_250 | ~r1_xboole_0(A_250, B_251))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.57/13.92  tff(c_156, plain, (![B_8, A_7]: (k4_xboole_0(B_8, k4_xboole_0(A_7, B_8))=B_8)), inference(resolution, [status(thm)], [c_95, c_141])).
% 22.57/13.92  tff(c_288, plain, (![A_268, B_269]: (k4_xboole_0(A_268, k4_xboole_0(A_268, B_269))=k3_xboole_0(A_268, B_269))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.57/13.92  tff(c_322, plain, (![B_8, A_7]: (k3_xboole_0(B_8, k4_xboole_0(A_7, B_8))=k4_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_156, c_288])).
% 22.57/13.92  tff(c_339, plain, (![B_271]: (k4_xboole_0(B_271, B_271)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_322])).
% 22.57/13.92  tff(c_359, plain, (![B_271]: (r1_xboole_0(k1_xboole_0, B_271))), inference(superposition, [status(thm), theory('equality')], [c_339, c_10])).
% 22.57/13.92  tff(c_805, plain, (![A_303, B_304]: (k7_relat_1(A_303, B_304)=k1_xboole_0 | ~r1_xboole_0(B_304, k1_relat_1(A_303)) | ~v1_relat_1(A_303))), inference(cnfTransformation, [status(thm)], [f_71])).
% 22.57/13.92  tff(c_836, plain, (![A_305]: (k7_relat_1(A_305, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_305))), inference(resolution, [status(thm)], [c_359, c_805])).
% 22.57/13.92  tff(c_843, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_390, c_836])).
% 22.57/13.92  tff(c_953, plain, (![A_311, B_312]: (r1_xboole_0(A_311, B_312) | ~r1_subset_1(A_311, B_312) | v1_xboole_0(B_312) | v1_xboole_0(A_311))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.57/13.92  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.57/13.92  tff(c_5033, plain, (![A_531, B_532]: (k4_xboole_0(A_531, B_532)=A_531 | ~r1_subset_1(A_531, B_532) | v1_xboole_0(B_532) | v1_xboole_0(A_531))), inference(resolution, [status(thm)], [c_953, c_12])).
% 22.57/13.92  tff(c_5039, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_5033])).
% 22.57/13.92  tff(c_5044, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_5039])).
% 22.57/13.92  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.57/13.92  tff(c_194, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | k4_xboole_0(A_9, B_10)!=A_9)), inference(resolution, [status(thm)], [c_14, c_181])).
% 22.57/13.92  tff(c_5129, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5044, c_194])).
% 22.57/13.92  tff(c_389, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_377])).
% 22.57/13.92  tff(c_844, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_389, c_836])).
% 22.57/13.92  tff(c_2941, plain, (![A_426, B_427, C_428, D_429]: (k2_partfun1(A_426, B_427, C_428, D_429)=k7_relat_1(C_428, D_429) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))) | ~v1_funct_1(C_428))), inference(cnfTransformation, [status(thm)], [f_119])).
% 22.57/13.92  tff(c_2948, plain, (![D_429]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_429)=k7_relat_1('#skF_6', D_429) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_2941])).
% 22.57/13.92  tff(c_2955, plain, (![D_429]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_429)=k7_relat_1('#skF_6', D_429))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2948])).
% 22.57/13.92  tff(c_2946, plain, (![D_429]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_429)=k7_relat_1('#skF_5', D_429) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_2941])).
% 22.57/13.92  tff(c_2952, plain, (![D_429]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_429)=k7_relat_1('#skF_5', D_429))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2946])).
% 22.57/13.92  tff(c_2714, plain, (![A_412, B_413, C_414]: (k9_subset_1(A_412, B_413, C_414)=k3_xboole_0(B_413, C_414) | ~m1_subset_1(C_414, k1_zfmisc_1(A_412)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.57/13.92  tff(c_2729, plain, (![B_413]: (k9_subset_1('#skF_1', B_413, '#skF_4')=k3_xboole_0(B_413, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_2714])).
% 22.57/13.92  tff(c_64, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 22.57/13.92  tff(c_123, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_64])).
% 22.57/13.92  tff(c_2739, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2729, c_2729, c_123])).
% 22.57/13.92  tff(c_8141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_843, c_5129, c_844, c_5129, c_2955, c_2952, c_2739])).
% 22.57/13.92  tff(c_8142, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 22.57/13.92  tff(c_8244, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_8142])).
% 22.57/13.92  tff(c_62576, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_62559, c_8244])).
% 22.57/13.92  tff(c_62598, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_9050, c_15569, c_9051, c_15569, c_9503, c_9503, c_12103, c_62576])).
% 22.57/13.92  tff(c_62600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_62598])).
% 22.57/13.92  tff(c_62601, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_8142])).
% 22.57/13.92  tff(c_102464, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102447, c_62601])).
% 22.57/13.92  tff(c_102486, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_63489, c_70423, c_63490, c_70423, c_65667, c_65667, c_69008, c_102464])).
% 22.57/13.92  tff(c_102488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_102486])).
% 22.57/13.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.57/13.92  
% 22.57/13.92  Inference rules
% 22.57/13.92  ----------------------
% 22.57/13.92  #Ref     : 0
% 22.57/13.92  #Sup     : 23603
% 22.57/13.92  #Fact    : 0
% 22.57/13.92  #Define  : 0
% 22.57/13.92  #Split   : 32
% 22.57/13.92  #Chain   : 0
% 22.57/13.92  #Close   : 0
% 22.57/13.92  
% 22.57/13.92  Ordering : KBO
% 22.57/13.92  
% 22.57/13.92  Simplification rules
% 22.57/13.92  ----------------------
% 22.57/13.92  #Subsume      : 7446
% 22.57/13.92  #Demod        : 26685
% 22.57/13.92  #Tautology    : 11496
% 22.57/13.92  #SimpNegUnit  : 757
% 22.57/13.92  #BackRed      : 20
% 22.57/13.92  
% 22.57/13.92  #Partial instantiations: 0
% 22.57/13.92  #Strategies tried      : 1
% 22.57/13.92  
% 22.57/13.92  Timing (in seconds)
% 22.57/13.92  ----------------------
% 22.60/13.92  Preprocessing        : 0.43
% 22.60/13.92  Parsing              : 0.21
% 22.60/13.92  CNF conversion       : 0.06
% 22.60/13.92  Main loop            : 12.65
% 22.60/13.92  Inferencing          : 2.40
% 22.60/13.92  Reduction            : 5.78
% 22.60/13.92  Demodulation         : 4.85
% 22.60/13.92  BG Simplification    : 0.23
% 22.60/13.92  Subsumption          : 3.76
% 22.60/13.92  Abstraction          : 0.43
% 22.60/13.92  MUC search           : 0.00
% 22.60/13.92  Cooper               : 0.00
% 22.60/13.92  Total                : 13.14
% 22.60/13.92  Index Insertion      : 0.00
% 22.60/13.93  Index Deletion       : 0.00
% 22.60/13.93  Index Matching       : 0.00
% 22.60/13.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
