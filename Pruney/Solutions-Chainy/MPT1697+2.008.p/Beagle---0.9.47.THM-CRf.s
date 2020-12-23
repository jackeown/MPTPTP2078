%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:09 EST 2020

% Result     : Theorem 15.06s
% Output     : CNFRefutation 15.37s
% Verified   : 
% Statistics : Number of formulae       :  243 ( 881 expanded)
%              Number of leaves         :   49 ( 325 expanded)
%              Depth                    :   14
%              Number of atoms          :  777 (4199 expanded)
%              Number of equality atoms :  147 ( 756 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_254,negated_conjecture,(
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

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_116,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_212,axiom,(
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

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_178,axiom,(
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

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_1389,plain,(
    ! [C_438,A_439,B_440] :
      ( v1_relat_1(C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1402,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_1389])).

tff(c_18,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12119,plain,(
    ! [C_1475,B_1476,A_1477] :
      ( ~ v1_xboole_0(C_1475)
      | ~ m1_subset_1(B_1476,k1_zfmisc_1(C_1475))
      | ~ r2_hidden(A_1477,B_1476) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12135,plain,(
    ! [B_1478,A_1479,A_1480] :
      ( ~ v1_xboole_0(B_1478)
      | ~ r2_hidden(A_1479,A_1480)
      | ~ r1_tarski(A_1480,B_1478) ) ),
    inference(resolution,[status(thm)],[c_26,c_12119])).

tff(c_12218,plain,(
    ! [B_1499,B_1500,A_1501] :
      ( ~ v1_xboole_0(B_1499)
      | ~ r1_tarski(B_1500,B_1499)
      | r1_xboole_0(A_1501,B_1500) ) ),
    inference(resolution,[status(thm)],[c_10,c_12135])).

tff(c_12233,plain,(
    ! [B_9,A_1501] :
      ( ~ v1_xboole_0(B_9)
      | r1_xboole_0(A_1501,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_12218])).

tff(c_12307,plain,(
    ! [B_1517,A_1518] :
      ( k7_relat_1(B_1517,A_1518) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_1517),A_1518)
      | ~ v1_relat_1(B_1517) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12332,plain,(
    ! [B_1519,B_1520] :
      ( k7_relat_1(B_1519,B_1520) = k1_xboole_0
      | ~ v1_relat_1(B_1519)
      | ~ v1_xboole_0(B_1520) ) ),
    inference(resolution,[status(thm)],[c_12233,c_12307])).

tff(c_12342,plain,(
    ! [B_1521] :
      ( k7_relat_1('#skF_6',B_1521) = k1_xboole_0
      | ~ v1_xboole_0(B_1521) ) ),
    inference(resolution,[status(thm)],[c_1402,c_12332])).

tff(c_12346,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_12342])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_80,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | ~ r1_subset_1(A_23,B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_12158,plain,(
    ! [C_1484,A_1485,B_1486] :
      ( v4_relat_1(C_1484,A_1485)
      | ~ m1_subset_1(C_1484,k1_zfmisc_1(k2_zfmisc_1(A_1485,B_1486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12171,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_12158])).

tff(c_12378,plain,(
    ! [B_1532,A_1533] :
      ( k1_relat_1(B_1532) = A_1533
      | ~ v1_partfun1(B_1532,A_1533)
      | ~ v4_relat_1(B_1532,A_1533)
      | ~ v1_relat_1(B_1532) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_12384,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12171,c_12378])).

tff(c_12393,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_12384])).

tff(c_12397,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12393])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_12841,plain,(
    ! [C_1598,A_1599,B_1600] :
      ( v1_partfun1(C_1598,A_1599)
      | ~ v1_funct_2(C_1598,A_1599,B_1600)
      | ~ v1_funct_1(C_1598)
      | ~ m1_subset_1(C_1598,k1_zfmisc_1(k2_zfmisc_1(A_1599,B_1600)))
      | v1_xboole_0(B_1600) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_12851,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_12841])).

tff(c_12859,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_12851])).

tff(c_12861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_12397,c_12859])).

tff(c_12862,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12393])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12872,plain,(
    ! [A_21] :
      ( k7_relat_1('#skF_6',A_21) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_21)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12862,c_30])).

tff(c_13224,plain,(
    ! [A_1638] :
      ( k7_relat_1('#skF_6',A_1638) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_1638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_12872])).

tff(c_13231,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_13224])).

tff(c_13366,plain,(
    ! [B_1650] :
      ( k7_relat_1('#skF_6',B_1650) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_1650)
      | v1_xboole_0(B_1650) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_13231])).

tff(c_13369,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_13366])).

tff(c_13372,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_13369])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( r1_xboole_0(k1_relat_1(B_22),A_21)
      | k7_relat_1(B_22,A_21) != k1_xboole_0
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12875,plain,(
    ! [A_21] :
      ( r1_xboole_0('#skF_4',A_21)
      | k7_relat_1('#skF_6',A_21) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12862,c_32])).

tff(c_13169,plain,(
    ! [A_1635] :
      ( r1_xboole_0('#skF_4',A_1635)
      | k7_relat_1('#skF_6',A_1635) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_12875])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_13182,plain,(
    ! [A_1635] :
      ( k3_xboole_0('#skF_4',A_1635) = k1_xboole_0
      | k7_relat_1('#skF_6',A_1635) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_13169,c_2])).

tff(c_13386,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13372,c_13182])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_1401,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_1389])).

tff(c_12351,plain,(
    ! [B_1522] :
      ( k7_relat_1('#skF_7',B_1522) = k1_xboole_0
      | ~ v1_xboole_0(B_1522) ) ),
    inference(resolution,[status(thm)],[c_1401,c_12332])).

tff(c_12355,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_12351])).

tff(c_13282,plain,(
    ! [A_1641,B_1642,C_1643] :
      ( k9_subset_1(A_1641,B_1642,C_1643) = k3_xboole_0(B_1642,C_1643)
      | ~ m1_subset_1(C_1643,k1_zfmisc_1(A_1641)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_13296,plain,(
    ! [B_1642] : k9_subset_1('#skF_2',B_1642,'#skF_5') = k3_xboole_0(B_1642,'#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_13282])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_70,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_13609,plain,(
    ! [C_1687,D_1689,A_1691,B_1690,E_1686,F_1688] :
      ( v1_funct_1(k1_tmap_1(A_1691,B_1690,C_1687,D_1689,E_1686,F_1688))
      | ~ m1_subset_1(F_1688,k1_zfmisc_1(k2_zfmisc_1(D_1689,B_1690)))
      | ~ v1_funct_2(F_1688,D_1689,B_1690)
      | ~ v1_funct_1(F_1688)
      | ~ m1_subset_1(E_1686,k1_zfmisc_1(k2_zfmisc_1(C_1687,B_1690)))
      | ~ v1_funct_2(E_1686,C_1687,B_1690)
      | ~ v1_funct_1(E_1686)
      | ~ m1_subset_1(D_1689,k1_zfmisc_1(A_1691))
      | v1_xboole_0(D_1689)
      | ~ m1_subset_1(C_1687,k1_zfmisc_1(A_1691))
      | v1_xboole_0(C_1687)
      | v1_xboole_0(B_1690)
      | v1_xboole_0(A_1691) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_13614,plain,(
    ! [A_1691,C_1687,E_1686] :
      ( v1_funct_1(k1_tmap_1(A_1691,'#skF_3',C_1687,'#skF_5',E_1686,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1686,k1_zfmisc_1(k2_zfmisc_1(C_1687,'#skF_3')))
      | ~ v1_funct_2(E_1686,C_1687,'#skF_3')
      | ~ v1_funct_1(E_1686)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1691))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1687,k1_zfmisc_1(A_1691))
      | v1_xboole_0(C_1687)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1691) ) ),
    inference(resolution,[status(thm)],[c_68,c_13609])).

tff(c_13620,plain,(
    ! [A_1691,C_1687,E_1686] :
      ( v1_funct_1(k1_tmap_1(A_1691,'#skF_3',C_1687,'#skF_5',E_1686,'#skF_7'))
      | ~ m1_subset_1(E_1686,k1_zfmisc_1(k2_zfmisc_1(C_1687,'#skF_3')))
      | ~ v1_funct_2(E_1686,C_1687,'#skF_3')
      | ~ v1_funct_1(E_1686)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1691))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1687,k1_zfmisc_1(A_1691))
      | v1_xboole_0(C_1687)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1691) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_13614])).

tff(c_14035,plain,(
    ! [A_1743,C_1744,E_1745] :
      ( v1_funct_1(k1_tmap_1(A_1743,'#skF_3',C_1744,'#skF_5',E_1745,'#skF_7'))
      | ~ m1_subset_1(E_1745,k1_zfmisc_1(k2_zfmisc_1(C_1744,'#skF_3')))
      | ~ v1_funct_2(E_1745,C_1744,'#skF_3')
      | ~ v1_funct_1(E_1745)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1743))
      | ~ m1_subset_1(C_1744,k1_zfmisc_1(A_1743))
      | v1_xboole_0(C_1744)
      | v1_xboole_0(A_1743) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_13620])).

tff(c_14045,plain,(
    ! [A_1743] :
      ( v1_funct_1(k1_tmap_1(A_1743,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1743))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1743))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1743) ) ),
    inference(resolution,[status(thm)],[c_74,c_14035])).

tff(c_14056,plain,(
    ! [A_1743] :
      ( v1_funct_1(k1_tmap_1(A_1743,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1743))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1743))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1743) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_14045])).

tff(c_14314,plain,(
    ! [A_1780] :
      ( v1_funct_1(k1_tmap_1(A_1780,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1780))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1780))
      | v1_xboole_0(A_1780) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_14056])).

tff(c_14321,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_14314])).

tff(c_14325,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_14321])).

tff(c_14326,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_14325])).

tff(c_13393,plain,(
    ! [A_1651,B_1652,C_1653,D_1654] :
      ( k2_partfun1(A_1651,B_1652,C_1653,D_1654) = k7_relat_1(C_1653,D_1654)
      | ~ m1_subset_1(C_1653,k1_zfmisc_1(k2_zfmisc_1(A_1651,B_1652)))
      | ~ v1_funct_1(C_1653) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_13400,plain,(
    ! [D_1654] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_1654) = k7_relat_1('#skF_6',D_1654)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_13393])).

tff(c_13407,plain,(
    ! [D_1654] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_1654) = k7_relat_1('#skF_6',D_1654) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_13400])).

tff(c_13398,plain,(
    ! [D_1654] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1654) = k7_relat_1('#skF_7',D_1654)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_13393])).

tff(c_13404,plain,(
    ! [D_1654] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1654) = k7_relat_1('#skF_7',D_1654) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13398])).

tff(c_62,plain,(
    ! [F_173,C_170,D_171,A_168,B_169,E_172] :
      ( v1_funct_2(k1_tmap_1(A_168,B_169,C_170,D_171,E_172,F_173),k4_subset_1(A_168,C_170,D_171),B_169)
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(D_171,B_169)))
      | ~ v1_funct_2(F_173,D_171,B_169)
      | ~ v1_funct_1(F_173)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(C_170,B_169)))
      | ~ v1_funct_2(E_172,C_170,B_169)
      | ~ v1_funct_1(E_172)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(A_168))
      | v1_xboole_0(D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_168))
      | v1_xboole_0(C_170)
      | v1_xboole_0(B_169)
      | v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_60,plain,(
    ! [F_173,C_170,D_171,A_168,B_169,E_172] :
      ( m1_subset_1(k1_tmap_1(A_168,B_169,C_170,D_171,E_172,F_173),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_168,C_170,D_171),B_169)))
      | ~ m1_subset_1(F_173,k1_zfmisc_1(k2_zfmisc_1(D_171,B_169)))
      | ~ v1_funct_2(F_173,D_171,B_169)
      | ~ v1_funct_1(F_173)
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(C_170,B_169)))
      | ~ v1_funct_2(E_172,C_170,B_169)
      | ~ v1_funct_1(E_172)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(A_168))
      | v1_xboole_0(D_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_168))
      | v1_xboole_0(C_170)
      | v1_xboole_0(B_169)
      | v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_14142,plain,(
    ! [D_1751,B_1753,E_1754,F_1755,C_1752,A_1750] :
      ( k2_partfun1(k4_subset_1(A_1750,C_1752,D_1751),B_1753,k1_tmap_1(A_1750,B_1753,C_1752,D_1751,E_1754,F_1755),C_1752) = E_1754
      | ~ m1_subset_1(k1_tmap_1(A_1750,B_1753,C_1752,D_1751,E_1754,F_1755),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1750,C_1752,D_1751),B_1753)))
      | ~ v1_funct_2(k1_tmap_1(A_1750,B_1753,C_1752,D_1751,E_1754,F_1755),k4_subset_1(A_1750,C_1752,D_1751),B_1753)
      | ~ v1_funct_1(k1_tmap_1(A_1750,B_1753,C_1752,D_1751,E_1754,F_1755))
      | k2_partfun1(D_1751,B_1753,F_1755,k9_subset_1(A_1750,C_1752,D_1751)) != k2_partfun1(C_1752,B_1753,E_1754,k9_subset_1(A_1750,C_1752,D_1751))
      | ~ m1_subset_1(F_1755,k1_zfmisc_1(k2_zfmisc_1(D_1751,B_1753)))
      | ~ v1_funct_2(F_1755,D_1751,B_1753)
      | ~ v1_funct_1(F_1755)
      | ~ m1_subset_1(E_1754,k1_zfmisc_1(k2_zfmisc_1(C_1752,B_1753)))
      | ~ v1_funct_2(E_1754,C_1752,B_1753)
      | ~ v1_funct_1(E_1754)
      | ~ m1_subset_1(D_1751,k1_zfmisc_1(A_1750))
      | v1_xboole_0(D_1751)
      | ~ m1_subset_1(C_1752,k1_zfmisc_1(A_1750))
      | v1_xboole_0(C_1752)
      | v1_xboole_0(B_1753)
      | v1_xboole_0(A_1750) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_16900,plain,(
    ! [E_2072,D_2075,C_2073,B_2076,A_2077,F_2074] :
      ( k2_partfun1(k4_subset_1(A_2077,C_2073,D_2075),B_2076,k1_tmap_1(A_2077,B_2076,C_2073,D_2075,E_2072,F_2074),C_2073) = E_2072
      | ~ v1_funct_2(k1_tmap_1(A_2077,B_2076,C_2073,D_2075,E_2072,F_2074),k4_subset_1(A_2077,C_2073,D_2075),B_2076)
      | ~ v1_funct_1(k1_tmap_1(A_2077,B_2076,C_2073,D_2075,E_2072,F_2074))
      | k2_partfun1(D_2075,B_2076,F_2074,k9_subset_1(A_2077,C_2073,D_2075)) != k2_partfun1(C_2073,B_2076,E_2072,k9_subset_1(A_2077,C_2073,D_2075))
      | ~ m1_subset_1(F_2074,k1_zfmisc_1(k2_zfmisc_1(D_2075,B_2076)))
      | ~ v1_funct_2(F_2074,D_2075,B_2076)
      | ~ v1_funct_1(F_2074)
      | ~ m1_subset_1(E_2072,k1_zfmisc_1(k2_zfmisc_1(C_2073,B_2076)))
      | ~ v1_funct_2(E_2072,C_2073,B_2076)
      | ~ v1_funct_1(E_2072)
      | ~ m1_subset_1(D_2075,k1_zfmisc_1(A_2077))
      | v1_xboole_0(D_2075)
      | ~ m1_subset_1(C_2073,k1_zfmisc_1(A_2077))
      | v1_xboole_0(C_2073)
      | v1_xboole_0(B_2076)
      | v1_xboole_0(A_2077) ) ),
    inference(resolution,[status(thm)],[c_60,c_14142])).

tff(c_20442,plain,(
    ! [E_2349,D_2352,A_2354,B_2353,F_2351,C_2350] :
      ( k2_partfun1(k4_subset_1(A_2354,C_2350,D_2352),B_2353,k1_tmap_1(A_2354,B_2353,C_2350,D_2352,E_2349,F_2351),C_2350) = E_2349
      | ~ v1_funct_1(k1_tmap_1(A_2354,B_2353,C_2350,D_2352,E_2349,F_2351))
      | k2_partfun1(D_2352,B_2353,F_2351,k9_subset_1(A_2354,C_2350,D_2352)) != k2_partfun1(C_2350,B_2353,E_2349,k9_subset_1(A_2354,C_2350,D_2352))
      | ~ m1_subset_1(F_2351,k1_zfmisc_1(k2_zfmisc_1(D_2352,B_2353)))
      | ~ v1_funct_2(F_2351,D_2352,B_2353)
      | ~ v1_funct_1(F_2351)
      | ~ m1_subset_1(E_2349,k1_zfmisc_1(k2_zfmisc_1(C_2350,B_2353)))
      | ~ v1_funct_2(E_2349,C_2350,B_2353)
      | ~ v1_funct_1(E_2349)
      | ~ m1_subset_1(D_2352,k1_zfmisc_1(A_2354))
      | v1_xboole_0(D_2352)
      | ~ m1_subset_1(C_2350,k1_zfmisc_1(A_2354))
      | v1_xboole_0(C_2350)
      | v1_xboole_0(B_2353)
      | v1_xboole_0(A_2354) ) ),
    inference(resolution,[status(thm)],[c_62,c_16900])).

tff(c_20449,plain,(
    ! [A_2354,C_2350,E_2349] :
      ( k2_partfun1(k4_subset_1(A_2354,C_2350,'#skF_5'),'#skF_3',k1_tmap_1(A_2354,'#skF_3',C_2350,'#skF_5',E_2349,'#skF_7'),C_2350) = E_2349
      | ~ v1_funct_1(k1_tmap_1(A_2354,'#skF_3',C_2350,'#skF_5',E_2349,'#skF_7'))
      | k2_partfun1(C_2350,'#skF_3',E_2349,k9_subset_1(A_2354,C_2350,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_2354,C_2350,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_2349,k1_zfmisc_1(k2_zfmisc_1(C_2350,'#skF_3')))
      | ~ v1_funct_2(E_2349,C_2350,'#skF_3')
      | ~ v1_funct_1(E_2349)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2354))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2350,k1_zfmisc_1(A_2354))
      | v1_xboole_0(C_2350)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2354) ) ),
    inference(resolution,[status(thm)],[c_68,c_20442])).

tff(c_20456,plain,(
    ! [A_2354,C_2350,E_2349] :
      ( k2_partfun1(k4_subset_1(A_2354,C_2350,'#skF_5'),'#skF_3',k1_tmap_1(A_2354,'#skF_3',C_2350,'#skF_5',E_2349,'#skF_7'),C_2350) = E_2349
      | ~ v1_funct_1(k1_tmap_1(A_2354,'#skF_3',C_2350,'#skF_5',E_2349,'#skF_7'))
      | k2_partfun1(C_2350,'#skF_3',E_2349,k9_subset_1(A_2354,C_2350,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2354,C_2350,'#skF_5'))
      | ~ m1_subset_1(E_2349,k1_zfmisc_1(k2_zfmisc_1(C_2350,'#skF_3')))
      | ~ v1_funct_2(E_2349,C_2350,'#skF_3')
      | ~ v1_funct_1(E_2349)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2354))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_2350,k1_zfmisc_1(A_2354))
      | v1_xboole_0(C_2350)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_13404,c_20449])).

tff(c_22280,plain,(
    ! [A_2492,C_2493,E_2494] :
      ( k2_partfun1(k4_subset_1(A_2492,C_2493,'#skF_5'),'#skF_3',k1_tmap_1(A_2492,'#skF_3',C_2493,'#skF_5',E_2494,'#skF_7'),C_2493) = E_2494
      | ~ v1_funct_1(k1_tmap_1(A_2492,'#skF_3',C_2493,'#skF_5',E_2494,'#skF_7'))
      | k2_partfun1(C_2493,'#skF_3',E_2494,k9_subset_1(A_2492,C_2493,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2492,C_2493,'#skF_5'))
      | ~ m1_subset_1(E_2494,k1_zfmisc_1(k2_zfmisc_1(C_2493,'#skF_3')))
      | ~ v1_funct_2(E_2494,C_2493,'#skF_3')
      | ~ v1_funct_1(E_2494)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2492))
      | ~ m1_subset_1(C_2493,k1_zfmisc_1(A_2492))
      | v1_xboole_0(C_2493)
      | v1_xboole_0(A_2492) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_20456])).

tff(c_22290,plain,(
    ! [A_2492] :
      ( k2_partfun1(k4_subset_1(A_2492,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2492,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2492,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_2492,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_2492,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2492))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2492))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2492) ) ),
    inference(resolution,[status(thm)],[c_74,c_22280])).

tff(c_22301,plain,(
    ! [A_2492] :
      ( k2_partfun1(k4_subset_1(A_2492,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2492,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2492,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2492,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2492,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2492))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2492))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_2492) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_13407,c_22290])).

tff(c_23110,plain,(
    ! [A_2532] :
      ( k2_partfun1(k4_subset_1(A_2532,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_2532,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_2532,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_2532,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_2532,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_2532))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2532))
      | v1_xboole_0(A_2532) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_22301])).

tff(c_1495,plain,(
    ! [C_462,B_463,A_464] :
      ( ~ v1_xboole_0(C_462)
      | ~ m1_subset_1(B_463,k1_zfmisc_1(C_462))
      | ~ r2_hidden(A_464,B_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1528,plain,(
    ! [B_470,A_471,A_472] :
      ( ~ v1_xboole_0(B_470)
      | ~ r2_hidden(A_471,A_472)
      | ~ r1_tarski(A_472,B_470) ) ),
    inference(resolution,[status(thm)],[c_26,c_1495])).

tff(c_1579,plain,(
    ! [B_483,B_484,A_485] :
      ( ~ v1_xboole_0(B_483)
      | ~ r1_tarski(B_484,B_483)
      | r1_xboole_0(A_485,B_484) ) ),
    inference(resolution,[status(thm)],[c_10,c_1528])).

tff(c_1594,plain,(
    ! [B_9,A_485] :
      ( ~ v1_xboole_0(B_9)
      | r1_xboole_0(A_485,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_1579])).

tff(c_1654,plain,(
    ! [B_500,A_501] :
      ( k7_relat_1(B_500,A_501) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_500),A_501)
      | ~ v1_relat_1(B_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1675,plain,(
    ! [B_502,B_503] :
      ( k7_relat_1(B_502,B_503) = k1_xboole_0
      | ~ v1_relat_1(B_502)
      | ~ v1_xboole_0(B_503) ) ),
    inference(resolution,[status(thm)],[c_1594,c_1654])).

tff(c_1685,plain,(
    ! [B_504] :
      ( k7_relat_1('#skF_6',B_504) = k1_xboole_0
      | ~ v1_xboole_0(B_504) ) ),
    inference(resolution,[status(thm)],[c_1402,c_1675])).

tff(c_1689,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1685])).

tff(c_1449,plain,(
    ! [C_451,A_452,B_453] :
      ( v4_relat_1(C_451,A_452)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1462,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1449])).

tff(c_1827,plain,(
    ! [B_531,A_532] :
      ( k1_relat_1(B_531) = A_532
      | ~ v1_partfun1(B_531,A_532)
      | ~ v4_relat_1(B_531,A_532)
      | ~ v1_relat_1(B_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1833,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1462,c_1827])).

tff(c_1842,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_1833])).

tff(c_1861,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1842])).

tff(c_2027,plain,(
    ! [C_554,A_555,B_556] :
      ( v1_partfun1(C_554,A_555)
      | ~ v1_funct_2(C_554,A_555,B_556)
      | ~ v1_funct_1(C_554)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_555,B_556)))
      | v1_xboole_0(B_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2037,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2027])).

tff(c_2045,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2037])).

tff(c_2047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1861,c_2045])).

tff(c_2048,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1842])).

tff(c_2058,plain,(
    ! [A_21] :
      ( k7_relat_1('#skF_6',A_21) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_21)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2048,c_30])).

tff(c_2209,plain,(
    ! [A_566] :
      ( k7_relat_1('#skF_6',A_566) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_566) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_2058])).

tff(c_2217,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_2209])).

tff(c_2352,plain,(
    ! [B_578] :
      ( k7_relat_1('#skF_6',B_578) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_578)
      | v1_xboole_0(B_578) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2217])).

tff(c_2358,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_2352])).

tff(c_2362,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2358])).

tff(c_2053,plain,(
    ! [A_21] :
      ( r1_xboole_0('#skF_4',A_21)
      | k7_relat_1('#skF_6',A_21) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2048,c_32])).

tff(c_2250,plain,(
    ! [A_568] :
      ( r1_xboole_0('#skF_4',A_568)
      | k7_relat_1('#skF_6',A_568) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_2053])).

tff(c_2267,plain,(
    ! [A_568] :
      ( k3_xboole_0('#skF_4',A_568) = k1_xboole_0
      | k7_relat_1('#skF_6',A_568) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2250,c_2])).

tff(c_2375,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2362,c_2267])).

tff(c_1694,plain,(
    ! [B_505] :
      ( k7_relat_1('#skF_7',B_505) = k1_xboole_0
      | ~ v1_xboole_0(B_505) ) ),
    inference(resolution,[status(thm)],[c_1401,c_1675])).

tff(c_1698,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1694])).

tff(c_1736,plain,(
    ! [A_516,B_517,C_518] :
      ( k9_subset_1(A_516,B_517,C_518) = k3_xboole_0(B_517,C_518)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(A_516)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1750,plain,(
    ! [B_517] : k9_subset_1('#skF_2',B_517,'#skF_5') = k3_xboole_0(B_517,'#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1736])).

tff(c_2388,plain,(
    ! [F_582,E_580,D_583,B_584,A_585,C_581] :
      ( v1_funct_1(k1_tmap_1(A_585,B_584,C_581,D_583,E_580,F_582))
      | ~ m1_subset_1(F_582,k1_zfmisc_1(k2_zfmisc_1(D_583,B_584)))
      | ~ v1_funct_2(F_582,D_583,B_584)
      | ~ v1_funct_1(F_582)
      | ~ m1_subset_1(E_580,k1_zfmisc_1(k2_zfmisc_1(C_581,B_584)))
      | ~ v1_funct_2(E_580,C_581,B_584)
      | ~ v1_funct_1(E_580)
      | ~ m1_subset_1(D_583,k1_zfmisc_1(A_585))
      | v1_xboole_0(D_583)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(A_585))
      | v1_xboole_0(C_581)
      | v1_xboole_0(B_584)
      | v1_xboole_0(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_2393,plain,(
    ! [A_585,C_581,E_580] :
      ( v1_funct_1(k1_tmap_1(A_585,'#skF_3',C_581,'#skF_5',E_580,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_580,k1_zfmisc_1(k2_zfmisc_1(C_581,'#skF_3')))
      | ~ v1_funct_2(E_580,C_581,'#skF_3')
      | ~ v1_funct_1(E_580)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_585))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_581,k1_zfmisc_1(A_585))
      | v1_xboole_0(C_581)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_585) ) ),
    inference(resolution,[status(thm)],[c_68,c_2388])).

tff(c_2399,plain,(
    ! [A_585,C_581,E_580] :
      ( v1_funct_1(k1_tmap_1(A_585,'#skF_3',C_581,'#skF_5',E_580,'#skF_7'))
      | ~ m1_subset_1(E_580,k1_zfmisc_1(k2_zfmisc_1(C_581,'#skF_3')))
      | ~ v1_funct_2(E_580,C_581,'#skF_3')
      | ~ v1_funct_1(E_580)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_585))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_581,k1_zfmisc_1(A_585))
      | v1_xboole_0(C_581)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_585) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2393])).

tff(c_2861,plain,(
    ! [A_648,C_649,E_650] :
      ( v1_funct_1(k1_tmap_1(A_648,'#skF_3',C_649,'#skF_5',E_650,'#skF_7'))
      | ~ m1_subset_1(E_650,k1_zfmisc_1(k2_zfmisc_1(C_649,'#skF_3')))
      | ~ v1_funct_2(E_650,C_649,'#skF_3')
      | ~ v1_funct_1(E_650)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_648))
      | ~ m1_subset_1(C_649,k1_zfmisc_1(A_648))
      | v1_xboole_0(C_649)
      | v1_xboole_0(A_648) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_2399])).

tff(c_2871,plain,(
    ! [A_648] :
      ( v1_funct_1(k1_tmap_1(A_648,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_648))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_648))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_648) ) ),
    inference(resolution,[status(thm)],[c_74,c_2861])).

tff(c_2882,plain,(
    ! [A_648] :
      ( v1_funct_1(k1_tmap_1(A_648,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_648))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_648))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_648) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2871])).

tff(c_3101,plain,(
    ! [A_676] :
      ( v1_funct_1(k1_tmap_1(A_676,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_676))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_676))
      | v1_xboole_0(A_676) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2882])).

tff(c_3108,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_3101])).

tff(c_3112,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3108])).

tff(c_3113,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3112])).

tff(c_1846,plain,(
    ! [A_533,B_534,C_535,D_536] :
      ( k2_partfun1(A_533,B_534,C_535,D_536) = k7_relat_1(C_535,D_536)
      | ~ m1_subset_1(C_535,k1_zfmisc_1(k2_zfmisc_1(A_533,B_534)))
      | ~ v1_funct_1(C_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1853,plain,(
    ! [D_536] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_536) = k7_relat_1('#skF_6',D_536)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_1846])).

tff(c_1860,plain,(
    ! [D_536] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_536) = k7_relat_1('#skF_6',D_536) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1853])).

tff(c_1851,plain,(
    ! [D_536] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_536) = k7_relat_1('#skF_7',D_536)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_1846])).

tff(c_1857,plain,(
    ! [D_536] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_536) = k7_relat_1('#skF_7',D_536) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1851])).

tff(c_2953,plain,(
    ! [E_659,D_656,A_655,B_658,C_657,F_660] :
      ( k2_partfun1(k4_subset_1(A_655,C_657,D_656),B_658,k1_tmap_1(A_655,B_658,C_657,D_656,E_659,F_660),D_656) = F_660
      | ~ m1_subset_1(k1_tmap_1(A_655,B_658,C_657,D_656,E_659,F_660),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_655,C_657,D_656),B_658)))
      | ~ v1_funct_2(k1_tmap_1(A_655,B_658,C_657,D_656,E_659,F_660),k4_subset_1(A_655,C_657,D_656),B_658)
      | ~ v1_funct_1(k1_tmap_1(A_655,B_658,C_657,D_656,E_659,F_660))
      | k2_partfun1(D_656,B_658,F_660,k9_subset_1(A_655,C_657,D_656)) != k2_partfun1(C_657,B_658,E_659,k9_subset_1(A_655,C_657,D_656))
      | ~ m1_subset_1(F_660,k1_zfmisc_1(k2_zfmisc_1(D_656,B_658)))
      | ~ v1_funct_2(F_660,D_656,B_658)
      | ~ v1_funct_1(F_660)
      | ~ m1_subset_1(E_659,k1_zfmisc_1(k2_zfmisc_1(C_657,B_658)))
      | ~ v1_funct_2(E_659,C_657,B_658)
      | ~ v1_funct_1(E_659)
      | ~ m1_subset_1(D_656,k1_zfmisc_1(A_655))
      | v1_xboole_0(D_656)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(A_655))
      | v1_xboole_0(C_657)
      | v1_xboole_0(B_658)
      | v1_xboole_0(A_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_5803,plain,(
    ! [D_988,F_987,C_986,B_989,E_985,A_990] :
      ( k2_partfun1(k4_subset_1(A_990,C_986,D_988),B_989,k1_tmap_1(A_990,B_989,C_986,D_988,E_985,F_987),D_988) = F_987
      | ~ v1_funct_2(k1_tmap_1(A_990,B_989,C_986,D_988,E_985,F_987),k4_subset_1(A_990,C_986,D_988),B_989)
      | ~ v1_funct_1(k1_tmap_1(A_990,B_989,C_986,D_988,E_985,F_987))
      | k2_partfun1(D_988,B_989,F_987,k9_subset_1(A_990,C_986,D_988)) != k2_partfun1(C_986,B_989,E_985,k9_subset_1(A_990,C_986,D_988))
      | ~ m1_subset_1(F_987,k1_zfmisc_1(k2_zfmisc_1(D_988,B_989)))
      | ~ v1_funct_2(F_987,D_988,B_989)
      | ~ v1_funct_1(F_987)
      | ~ m1_subset_1(E_985,k1_zfmisc_1(k2_zfmisc_1(C_986,B_989)))
      | ~ v1_funct_2(E_985,C_986,B_989)
      | ~ v1_funct_1(E_985)
      | ~ m1_subset_1(D_988,k1_zfmisc_1(A_990))
      | v1_xboole_0(D_988)
      | ~ m1_subset_1(C_986,k1_zfmisc_1(A_990))
      | v1_xboole_0(C_986)
      | v1_xboole_0(B_989)
      | v1_xboole_0(A_990) ) ),
    inference(resolution,[status(thm)],[c_60,c_2953])).

tff(c_9358,plain,(
    ! [C_1275,B_1278,F_1276,A_1279,D_1277,E_1274] :
      ( k2_partfun1(k4_subset_1(A_1279,C_1275,D_1277),B_1278,k1_tmap_1(A_1279,B_1278,C_1275,D_1277,E_1274,F_1276),D_1277) = F_1276
      | ~ v1_funct_1(k1_tmap_1(A_1279,B_1278,C_1275,D_1277,E_1274,F_1276))
      | k2_partfun1(D_1277,B_1278,F_1276,k9_subset_1(A_1279,C_1275,D_1277)) != k2_partfun1(C_1275,B_1278,E_1274,k9_subset_1(A_1279,C_1275,D_1277))
      | ~ m1_subset_1(F_1276,k1_zfmisc_1(k2_zfmisc_1(D_1277,B_1278)))
      | ~ v1_funct_2(F_1276,D_1277,B_1278)
      | ~ v1_funct_1(F_1276)
      | ~ m1_subset_1(E_1274,k1_zfmisc_1(k2_zfmisc_1(C_1275,B_1278)))
      | ~ v1_funct_2(E_1274,C_1275,B_1278)
      | ~ v1_funct_1(E_1274)
      | ~ m1_subset_1(D_1277,k1_zfmisc_1(A_1279))
      | v1_xboole_0(D_1277)
      | ~ m1_subset_1(C_1275,k1_zfmisc_1(A_1279))
      | v1_xboole_0(C_1275)
      | v1_xboole_0(B_1278)
      | v1_xboole_0(A_1279) ) ),
    inference(resolution,[status(thm)],[c_62,c_5803])).

tff(c_9365,plain,(
    ! [A_1279,C_1275,E_1274] :
      ( k2_partfun1(k4_subset_1(A_1279,C_1275,'#skF_5'),'#skF_3',k1_tmap_1(A_1279,'#skF_3',C_1275,'#skF_5',E_1274,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1279,'#skF_3',C_1275,'#skF_5',E_1274,'#skF_7'))
      | k2_partfun1(C_1275,'#skF_3',E_1274,k9_subset_1(A_1279,C_1275,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1279,C_1275,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1274,k1_zfmisc_1(k2_zfmisc_1(C_1275,'#skF_3')))
      | ~ v1_funct_2(E_1274,C_1275,'#skF_3')
      | ~ v1_funct_1(E_1274)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1279))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1275,k1_zfmisc_1(A_1279))
      | v1_xboole_0(C_1275)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1279) ) ),
    inference(resolution,[status(thm)],[c_68,c_9358])).

tff(c_9372,plain,(
    ! [A_1279,C_1275,E_1274] :
      ( k2_partfun1(k4_subset_1(A_1279,C_1275,'#skF_5'),'#skF_3',k1_tmap_1(A_1279,'#skF_3',C_1275,'#skF_5',E_1274,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1279,'#skF_3',C_1275,'#skF_5',E_1274,'#skF_7'))
      | k2_partfun1(C_1275,'#skF_3',E_1274,k9_subset_1(A_1279,C_1275,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1279,C_1275,'#skF_5'))
      | ~ m1_subset_1(E_1274,k1_zfmisc_1(k2_zfmisc_1(C_1275,'#skF_3')))
      | ~ v1_funct_2(E_1274,C_1275,'#skF_3')
      | ~ v1_funct_1(E_1274)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1279))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1275,k1_zfmisc_1(A_1279))
      | v1_xboole_0(C_1275)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1857,c_9365])).

tff(c_11169,plain,(
    ! [A_1416,C_1417,E_1418] :
      ( k2_partfun1(k4_subset_1(A_1416,C_1417,'#skF_5'),'#skF_3',k1_tmap_1(A_1416,'#skF_3',C_1417,'#skF_5',E_1418,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1416,'#skF_3',C_1417,'#skF_5',E_1418,'#skF_7'))
      | k2_partfun1(C_1417,'#skF_3',E_1418,k9_subset_1(A_1416,C_1417,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1416,C_1417,'#skF_5'))
      | ~ m1_subset_1(E_1418,k1_zfmisc_1(k2_zfmisc_1(C_1417,'#skF_3')))
      | ~ v1_funct_2(E_1418,C_1417,'#skF_3')
      | ~ v1_funct_1(E_1418)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1416))
      | ~ m1_subset_1(C_1417,k1_zfmisc_1(A_1416))
      | v1_xboole_0(C_1417)
      | v1_xboole_0(A_1416) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_9372])).

tff(c_11179,plain,(
    ! [A_1416] :
      ( k2_partfun1(k4_subset_1(A_1416,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1416,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1416,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1416,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1416,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1416))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1416))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1416) ) ),
    inference(resolution,[status(thm)],[c_74,c_11169])).

tff(c_11190,plain,(
    ! [A_1416] :
      ( k2_partfun1(k4_subset_1(A_1416,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1416,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1416,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1416,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1416,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1416))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1416))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1860,c_11179])).

tff(c_11999,plain,(
    ! [A_1456] :
      ( k2_partfun1(k4_subset_1(A_1456,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1456,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1456,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1456,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1456,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1456))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1456))
      | v1_xboole_0(A_1456) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_11190])).

tff(c_147,plain,(
    ! [C_246,A_247,B_248] :
      ( v1_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_160,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_147])).

tff(c_292,plain,(
    ! [C_277,B_278,A_279] :
      ( ~ v1_xboole_0(C_277)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(C_277))
      | ~ r2_hidden(A_279,B_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_313,plain,(
    ! [B_282,A_283,A_284] :
      ( ~ v1_xboole_0(B_282)
      | ~ r2_hidden(A_283,A_284)
      | ~ r1_tarski(A_284,B_282) ) ),
    inference(resolution,[status(thm)],[c_26,c_292])).

tff(c_360,plain,(
    ! [B_293,B_294,A_295] :
      ( ~ v1_xboole_0(B_293)
      | ~ r1_tarski(B_294,B_293)
      | r1_xboole_0(A_295,B_294) ) ),
    inference(resolution,[status(thm)],[c_10,c_313])).

tff(c_375,plain,(
    ! [B_9,A_295] :
      ( ~ v1_xboole_0(B_9)
      | r1_xboole_0(A_295,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_360])).

tff(c_446,plain,(
    ! [B_311,A_312] :
      ( k7_relat_1(B_311,A_312) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_311),A_312)
      | ~ v1_relat_1(B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_471,plain,(
    ! [B_313,B_314] :
      ( k7_relat_1(B_313,B_314) = k1_xboole_0
      | ~ v1_relat_1(B_313)
      | ~ v1_xboole_0(B_314) ) ),
    inference(resolution,[status(thm)],[c_375,c_446])).

tff(c_482,plain,(
    ! [B_316] :
      ( k7_relat_1('#skF_6',B_316) = k1_xboole_0
      | ~ v1_xboole_0(B_316) ) ),
    inference(resolution,[status(thm)],[c_160,c_471])).

tff(c_486,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_482])).

tff(c_1287,plain,(
    ! [A_420,B_421,C_422,D_423] :
      ( k2_partfun1(A_420,B_421,C_422,D_423) = k7_relat_1(C_422,D_423)
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421)))
      | ~ v1_funct_1(C_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1294,plain,(
    ! [D_423] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_423) = k7_relat_1('#skF_6',D_423)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_1287])).

tff(c_1301,plain,(
    ! [D_423] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_423) = k7_relat_1('#skF_6',D_423) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1294])).

tff(c_159,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_147])).

tff(c_491,plain,(
    ! [B_317] :
      ( k7_relat_1('#skF_7',B_317) = k1_xboole_0
      | ~ v1_xboole_0(B_317) ) ),
    inference(resolution,[status(thm)],[c_159,c_471])).

tff(c_495,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_491])).

tff(c_1292,plain,(
    ! [D_423] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_423) = k7_relat_1('#skF_7',D_423)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_1287])).

tff(c_1298,plain,(
    ! [D_423] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_423) = k7_relat_1('#skF_7',D_423) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1292])).

tff(c_244,plain,(
    ! [C_264,A_265,B_266] :
      ( v4_relat_1(C_264,A_265)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_257,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_244])).

tff(c_526,plain,(
    ! [B_329,A_330] :
      ( k1_relat_1(B_329) = A_330
      | ~ v1_partfun1(B_329,A_330)
      | ~ v4_relat_1(B_329,A_330)
      | ~ v1_relat_1(B_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_532,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_257,c_526])).

tff(c_541,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_532])).

tff(c_545,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_1062,plain,(
    ! [C_401,A_402,B_403] :
      ( v1_partfun1(C_401,A_402)
      | ~ v1_funct_2(C_401,A_402,B_403)
      | ~ v1_funct_1(C_401)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | v1_xboole_0(B_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1072,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1062])).

tff(c_1080,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1072])).

tff(c_1082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_545,c_1080])).

tff(c_1083,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_1093,plain,(
    ! [A_21] :
      ( k7_relat_1('#skF_6',A_21) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_21)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_30])).

tff(c_1124,plain,(
    ! [A_405] :
      ( k7_relat_1('#skF_6',A_405) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',A_405) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_1093])).

tff(c_1131,plain,(
    ! [B_24] :
      ( k7_relat_1('#skF_6',B_24) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_1124])).

tff(c_1236,plain,(
    ! [B_416] :
      ( k7_relat_1('#skF_6',B_416) = k1_xboole_0
      | ~ r1_subset_1('#skF_4',B_416)
      | v1_xboole_0(B_416) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1131])).

tff(c_1242,plain,
    ( k7_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_1236])).

tff(c_1246,plain,(
    k7_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1242])).

tff(c_1096,plain,(
    ! [A_21] :
      ( r1_xboole_0('#skF_4',A_21)
      | k7_relat_1('#skF_6',A_21) != k1_xboole_0
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_32])).

tff(c_1110,plain,(
    ! [A_404] :
      ( r1_xboole_0('#skF_4',A_404)
      | k7_relat_1('#skF_6',A_404) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_1096])).

tff(c_1123,plain,(
    ! [A_404] :
      ( k3_xboole_0('#skF_4',A_404) = k1_xboole_0
      | k7_relat_1('#skF_6',A_404) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1110,c_2])).

tff(c_1260,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1246,c_1123])).

tff(c_1182,plain,(
    ! [A_408,B_409,C_410] :
      ( k9_subset_1(A_408,B_409,C_410) = k3_xboole_0(B_409,C_410)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(A_408)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1196,plain,(
    ! [B_409] : k9_subset_1('#skF_2',B_409,'#skF_5') = k3_xboole_0(B_409,'#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1182])).

tff(c_66,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_118,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1198,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_1196,c_118])).

tff(c_1330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_1301,c_495,c_1298,c_1260,c_1260,c_1198])).

tff(c_1331,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1404,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1331])).

tff(c_12016,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11999,c_1404])).

tff(c_12038,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_1689,c_2375,c_1698,c_2375,c_1750,c_1750,c_3113,c_12016])).

tff(c_12040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_12038])).

tff(c_12041,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1331])).

tff(c_23127,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23110,c_12041])).

tff(c_23149,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_12346,c_13386,c_12355,c_13386,c_13296,c_13296,c_14326,c_23127])).

tff(c_23151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_23149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.06/6.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.06/6.87  
% 15.06/6.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.06/6.87  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 15.06/6.87  
% 15.06/6.87  %Foreground sorts:
% 15.06/6.87  
% 15.06/6.87  
% 15.06/6.87  %Background operators:
% 15.06/6.87  
% 15.06/6.87  
% 15.06/6.87  %Foreground operators:
% 15.06/6.87  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 15.06/6.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.06/6.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.06/6.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.06/6.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.06/6.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.06/6.87  tff('#skF_7', type, '#skF_7': $i).
% 15.06/6.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.06/6.87  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 15.06/6.87  tff('#skF_5', type, '#skF_5': $i).
% 15.06/6.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.06/6.87  tff('#skF_6', type, '#skF_6': $i).
% 15.06/6.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.06/6.87  tff('#skF_2', type, '#skF_2': $i).
% 15.06/6.87  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 15.06/6.87  tff('#skF_3', type, '#skF_3': $i).
% 15.06/6.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.06/6.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.06/6.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.06/6.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.06/6.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.06/6.87  tff('#skF_4', type, '#skF_4': $i).
% 15.06/6.87  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.06/6.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.06/6.87  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.06/6.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.06/6.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.06/6.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.06/6.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.06/6.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.06/6.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.06/6.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.06/6.87  
% 15.37/6.90  tff(f_254, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 15.37/6.90  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.37/6.90  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.37/6.90  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.37/6.90  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 15.37/6.90  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.37/6.90  tff(f_76, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 15.37/6.90  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 15.37/6.90  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 15.37/6.90  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.37/6.90  tff(f_124, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 15.37/6.90  tff(f_116, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 15.37/6.90  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.37/6.90  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 15.37/6.90  tff(f_212, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 15.37/6.90  tff(f_130, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 15.37/6.90  tff(f_178, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 15.37/6.90  tff(c_92, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 15.37/6.90  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_1389, plain, (![C_438, A_439, B_440]: (v1_relat_1(C_438) | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.37/6.90  tff(c_1402, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_1389])).
% 15.37/6.90  tff(c_18, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.37/6.90  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.37/6.90  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.37/6.90  tff(c_12119, plain, (![C_1475, B_1476, A_1477]: (~v1_xboole_0(C_1475) | ~m1_subset_1(B_1476, k1_zfmisc_1(C_1475)) | ~r2_hidden(A_1477, B_1476))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.37/6.90  tff(c_12135, plain, (![B_1478, A_1479, A_1480]: (~v1_xboole_0(B_1478) | ~r2_hidden(A_1479, A_1480) | ~r1_tarski(A_1480, B_1478))), inference(resolution, [status(thm)], [c_26, c_12119])).
% 15.37/6.90  tff(c_12218, plain, (![B_1499, B_1500, A_1501]: (~v1_xboole_0(B_1499) | ~r1_tarski(B_1500, B_1499) | r1_xboole_0(A_1501, B_1500))), inference(resolution, [status(thm)], [c_10, c_12135])).
% 15.37/6.90  tff(c_12233, plain, (![B_9, A_1501]: (~v1_xboole_0(B_9) | r1_xboole_0(A_1501, B_9))), inference(resolution, [status(thm)], [c_18, c_12218])).
% 15.37/6.90  tff(c_12307, plain, (![B_1517, A_1518]: (k7_relat_1(B_1517, A_1518)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_1517), A_1518) | ~v1_relat_1(B_1517))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.37/6.90  tff(c_12332, plain, (![B_1519, B_1520]: (k7_relat_1(B_1519, B_1520)=k1_xboole_0 | ~v1_relat_1(B_1519) | ~v1_xboole_0(B_1520))), inference(resolution, [status(thm)], [c_12233, c_12307])).
% 15.37/6.90  tff(c_12342, plain, (![B_1521]: (k7_relat_1('#skF_6', B_1521)=k1_xboole_0 | ~v1_xboole_0(B_1521))), inference(resolution, [status(thm)], [c_1402, c_12332])).
% 15.37/6.90  tff(c_12346, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_12342])).
% 15.37/6.90  tff(c_84, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_80, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_88, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_36, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | ~r1_subset_1(A_23, B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.37/6.90  tff(c_90, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_12158, plain, (![C_1484, A_1485, B_1486]: (v4_relat_1(C_1484, A_1485) | ~m1_subset_1(C_1484, k1_zfmisc_1(k2_zfmisc_1(A_1485, B_1486))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.37/6.90  tff(c_12171, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_12158])).
% 15.37/6.90  tff(c_12378, plain, (![B_1532, A_1533]: (k1_relat_1(B_1532)=A_1533 | ~v1_partfun1(B_1532, A_1533) | ~v4_relat_1(B_1532, A_1533) | ~v1_relat_1(B_1532))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.37/6.90  tff(c_12384, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12171, c_12378])).
% 15.37/6.90  tff(c_12393, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_12384])).
% 15.37/6.90  tff(c_12397, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_12393])).
% 15.37/6.90  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_12841, plain, (![C_1598, A_1599, B_1600]: (v1_partfun1(C_1598, A_1599) | ~v1_funct_2(C_1598, A_1599, B_1600) | ~v1_funct_1(C_1598) | ~m1_subset_1(C_1598, k1_zfmisc_1(k2_zfmisc_1(A_1599, B_1600))) | v1_xboole_0(B_1600))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.37/6.90  tff(c_12851, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_12841])).
% 15.37/6.90  tff(c_12859, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_12851])).
% 15.37/6.90  tff(c_12861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_12397, c_12859])).
% 15.37/6.90  tff(c_12862, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_12393])).
% 15.37/6.90  tff(c_30, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.37/6.90  tff(c_12872, plain, (![A_21]: (k7_relat_1('#skF_6', A_21)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_21) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12862, c_30])).
% 15.37/6.90  tff(c_13224, plain, (![A_1638]: (k7_relat_1('#skF_6', A_1638)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_1638))), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_12872])).
% 15.37/6.90  tff(c_13231, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_24) | v1_xboole_0(B_24) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_13224])).
% 15.37/6.90  tff(c_13366, plain, (![B_1650]: (k7_relat_1('#skF_6', B_1650)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_1650) | v1_xboole_0(B_1650))), inference(negUnitSimplification, [status(thm)], [c_88, c_13231])).
% 15.37/6.90  tff(c_13369, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_13366])).
% 15.37/6.90  tff(c_13372, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_13369])).
% 15.37/6.90  tff(c_32, plain, (![B_22, A_21]: (r1_xboole_0(k1_relat_1(B_22), A_21) | k7_relat_1(B_22, A_21)!=k1_xboole_0 | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.37/6.90  tff(c_12875, plain, (![A_21]: (r1_xboole_0('#skF_4', A_21) | k7_relat_1('#skF_6', A_21)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12862, c_32])).
% 15.37/6.90  tff(c_13169, plain, (![A_1635]: (r1_xboole_0('#skF_4', A_1635) | k7_relat_1('#skF_6', A_1635)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_12875])).
% 15.37/6.90  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.37/6.90  tff(c_13182, plain, (![A_1635]: (k3_xboole_0('#skF_4', A_1635)=k1_xboole_0 | k7_relat_1('#skF_6', A_1635)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_13169, c_2])).
% 15.37/6.90  tff(c_13386, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13372, c_13182])).
% 15.37/6.90  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_1401, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_1389])).
% 15.37/6.90  tff(c_12351, plain, (![B_1522]: (k7_relat_1('#skF_7', B_1522)=k1_xboole_0 | ~v1_xboole_0(B_1522))), inference(resolution, [status(thm)], [c_1401, c_12332])).
% 15.37/6.90  tff(c_12355, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_12351])).
% 15.37/6.90  tff(c_13282, plain, (![A_1641, B_1642, C_1643]: (k9_subset_1(A_1641, B_1642, C_1643)=k3_xboole_0(B_1642, C_1643) | ~m1_subset_1(C_1643, k1_zfmisc_1(A_1641)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.37/6.90  tff(c_13296, plain, (![B_1642]: (k9_subset_1('#skF_2', B_1642, '#skF_5')=k3_xboole_0(B_1642, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_13282])).
% 15.37/6.90  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_70, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.90  tff(c_13609, plain, (![C_1687, D_1689, A_1691, B_1690, E_1686, F_1688]: (v1_funct_1(k1_tmap_1(A_1691, B_1690, C_1687, D_1689, E_1686, F_1688)) | ~m1_subset_1(F_1688, k1_zfmisc_1(k2_zfmisc_1(D_1689, B_1690))) | ~v1_funct_2(F_1688, D_1689, B_1690) | ~v1_funct_1(F_1688) | ~m1_subset_1(E_1686, k1_zfmisc_1(k2_zfmisc_1(C_1687, B_1690))) | ~v1_funct_2(E_1686, C_1687, B_1690) | ~v1_funct_1(E_1686) | ~m1_subset_1(D_1689, k1_zfmisc_1(A_1691)) | v1_xboole_0(D_1689) | ~m1_subset_1(C_1687, k1_zfmisc_1(A_1691)) | v1_xboole_0(C_1687) | v1_xboole_0(B_1690) | v1_xboole_0(A_1691))), inference(cnfTransformation, [status(thm)], [f_212])).
% 15.37/6.90  tff(c_13614, plain, (![A_1691, C_1687, E_1686]: (v1_funct_1(k1_tmap_1(A_1691, '#skF_3', C_1687, '#skF_5', E_1686, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1686, k1_zfmisc_1(k2_zfmisc_1(C_1687, '#skF_3'))) | ~v1_funct_2(E_1686, C_1687, '#skF_3') | ~v1_funct_1(E_1686) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1691)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1687, k1_zfmisc_1(A_1691)) | v1_xboole_0(C_1687) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1691))), inference(resolution, [status(thm)], [c_68, c_13609])).
% 15.37/6.90  tff(c_13620, plain, (![A_1691, C_1687, E_1686]: (v1_funct_1(k1_tmap_1(A_1691, '#skF_3', C_1687, '#skF_5', E_1686, '#skF_7')) | ~m1_subset_1(E_1686, k1_zfmisc_1(k2_zfmisc_1(C_1687, '#skF_3'))) | ~v1_funct_2(E_1686, C_1687, '#skF_3') | ~v1_funct_1(E_1686) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1691)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1687, k1_zfmisc_1(A_1691)) | v1_xboole_0(C_1687) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1691))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_13614])).
% 15.37/6.90  tff(c_14035, plain, (![A_1743, C_1744, E_1745]: (v1_funct_1(k1_tmap_1(A_1743, '#skF_3', C_1744, '#skF_5', E_1745, '#skF_7')) | ~m1_subset_1(E_1745, k1_zfmisc_1(k2_zfmisc_1(C_1744, '#skF_3'))) | ~v1_funct_2(E_1745, C_1744, '#skF_3') | ~v1_funct_1(E_1745) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1743)) | ~m1_subset_1(C_1744, k1_zfmisc_1(A_1743)) | v1_xboole_0(C_1744) | v1_xboole_0(A_1743))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_13620])).
% 15.37/6.90  tff(c_14045, plain, (![A_1743]: (v1_funct_1(k1_tmap_1(A_1743, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1743)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1743)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1743))), inference(resolution, [status(thm)], [c_74, c_14035])).
% 15.37/6.90  tff(c_14056, plain, (![A_1743]: (v1_funct_1(k1_tmap_1(A_1743, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1743)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1743)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1743))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_14045])).
% 15.37/6.90  tff(c_14314, plain, (![A_1780]: (v1_funct_1(k1_tmap_1(A_1780, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1780)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1780)) | v1_xboole_0(A_1780))), inference(negUnitSimplification, [status(thm)], [c_88, c_14056])).
% 15.37/6.90  tff(c_14321, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_14314])).
% 15.37/6.90  tff(c_14325, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_14321])).
% 15.37/6.90  tff(c_14326, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_14325])).
% 15.37/6.90  tff(c_13393, plain, (![A_1651, B_1652, C_1653, D_1654]: (k2_partfun1(A_1651, B_1652, C_1653, D_1654)=k7_relat_1(C_1653, D_1654) | ~m1_subset_1(C_1653, k1_zfmisc_1(k2_zfmisc_1(A_1651, B_1652))) | ~v1_funct_1(C_1653))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.37/6.90  tff(c_13400, plain, (![D_1654]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1654)=k7_relat_1('#skF_6', D_1654) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_13393])).
% 15.37/6.90  tff(c_13407, plain, (![D_1654]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1654)=k7_relat_1('#skF_6', D_1654))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_13400])).
% 15.37/6.90  tff(c_13398, plain, (![D_1654]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1654)=k7_relat_1('#skF_7', D_1654) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_13393])).
% 15.37/6.90  tff(c_13404, plain, (![D_1654]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1654)=k7_relat_1('#skF_7', D_1654))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_13398])).
% 15.37/6.90  tff(c_62, plain, (![F_173, C_170, D_171, A_168, B_169, E_172]: (v1_funct_2(k1_tmap_1(A_168, B_169, C_170, D_171, E_172, F_173), k4_subset_1(A_168, C_170, D_171), B_169) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(D_171, B_169))) | ~v1_funct_2(F_173, D_171, B_169) | ~v1_funct_1(F_173) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(C_170, B_169))) | ~v1_funct_2(E_172, C_170, B_169) | ~v1_funct_1(E_172) | ~m1_subset_1(D_171, k1_zfmisc_1(A_168)) | v1_xboole_0(D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(A_168)) | v1_xboole_0(C_170) | v1_xboole_0(B_169) | v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_212])).
% 15.37/6.90  tff(c_60, plain, (![F_173, C_170, D_171, A_168, B_169, E_172]: (m1_subset_1(k1_tmap_1(A_168, B_169, C_170, D_171, E_172, F_173), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_168, C_170, D_171), B_169))) | ~m1_subset_1(F_173, k1_zfmisc_1(k2_zfmisc_1(D_171, B_169))) | ~v1_funct_2(F_173, D_171, B_169) | ~v1_funct_1(F_173) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(C_170, B_169))) | ~v1_funct_2(E_172, C_170, B_169) | ~v1_funct_1(E_172) | ~m1_subset_1(D_171, k1_zfmisc_1(A_168)) | v1_xboole_0(D_171) | ~m1_subset_1(C_170, k1_zfmisc_1(A_168)) | v1_xboole_0(C_170) | v1_xboole_0(B_169) | v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_212])).
% 15.37/6.90  tff(c_14142, plain, (![D_1751, B_1753, E_1754, F_1755, C_1752, A_1750]: (k2_partfun1(k4_subset_1(A_1750, C_1752, D_1751), B_1753, k1_tmap_1(A_1750, B_1753, C_1752, D_1751, E_1754, F_1755), C_1752)=E_1754 | ~m1_subset_1(k1_tmap_1(A_1750, B_1753, C_1752, D_1751, E_1754, F_1755), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1750, C_1752, D_1751), B_1753))) | ~v1_funct_2(k1_tmap_1(A_1750, B_1753, C_1752, D_1751, E_1754, F_1755), k4_subset_1(A_1750, C_1752, D_1751), B_1753) | ~v1_funct_1(k1_tmap_1(A_1750, B_1753, C_1752, D_1751, E_1754, F_1755)) | k2_partfun1(D_1751, B_1753, F_1755, k9_subset_1(A_1750, C_1752, D_1751))!=k2_partfun1(C_1752, B_1753, E_1754, k9_subset_1(A_1750, C_1752, D_1751)) | ~m1_subset_1(F_1755, k1_zfmisc_1(k2_zfmisc_1(D_1751, B_1753))) | ~v1_funct_2(F_1755, D_1751, B_1753) | ~v1_funct_1(F_1755) | ~m1_subset_1(E_1754, k1_zfmisc_1(k2_zfmisc_1(C_1752, B_1753))) | ~v1_funct_2(E_1754, C_1752, B_1753) | ~v1_funct_1(E_1754) | ~m1_subset_1(D_1751, k1_zfmisc_1(A_1750)) | v1_xboole_0(D_1751) | ~m1_subset_1(C_1752, k1_zfmisc_1(A_1750)) | v1_xboole_0(C_1752) | v1_xboole_0(B_1753) | v1_xboole_0(A_1750))), inference(cnfTransformation, [status(thm)], [f_178])).
% 15.37/6.90  tff(c_16900, plain, (![E_2072, D_2075, C_2073, B_2076, A_2077, F_2074]: (k2_partfun1(k4_subset_1(A_2077, C_2073, D_2075), B_2076, k1_tmap_1(A_2077, B_2076, C_2073, D_2075, E_2072, F_2074), C_2073)=E_2072 | ~v1_funct_2(k1_tmap_1(A_2077, B_2076, C_2073, D_2075, E_2072, F_2074), k4_subset_1(A_2077, C_2073, D_2075), B_2076) | ~v1_funct_1(k1_tmap_1(A_2077, B_2076, C_2073, D_2075, E_2072, F_2074)) | k2_partfun1(D_2075, B_2076, F_2074, k9_subset_1(A_2077, C_2073, D_2075))!=k2_partfun1(C_2073, B_2076, E_2072, k9_subset_1(A_2077, C_2073, D_2075)) | ~m1_subset_1(F_2074, k1_zfmisc_1(k2_zfmisc_1(D_2075, B_2076))) | ~v1_funct_2(F_2074, D_2075, B_2076) | ~v1_funct_1(F_2074) | ~m1_subset_1(E_2072, k1_zfmisc_1(k2_zfmisc_1(C_2073, B_2076))) | ~v1_funct_2(E_2072, C_2073, B_2076) | ~v1_funct_1(E_2072) | ~m1_subset_1(D_2075, k1_zfmisc_1(A_2077)) | v1_xboole_0(D_2075) | ~m1_subset_1(C_2073, k1_zfmisc_1(A_2077)) | v1_xboole_0(C_2073) | v1_xboole_0(B_2076) | v1_xboole_0(A_2077))), inference(resolution, [status(thm)], [c_60, c_14142])).
% 15.37/6.90  tff(c_20442, plain, (![E_2349, D_2352, A_2354, B_2353, F_2351, C_2350]: (k2_partfun1(k4_subset_1(A_2354, C_2350, D_2352), B_2353, k1_tmap_1(A_2354, B_2353, C_2350, D_2352, E_2349, F_2351), C_2350)=E_2349 | ~v1_funct_1(k1_tmap_1(A_2354, B_2353, C_2350, D_2352, E_2349, F_2351)) | k2_partfun1(D_2352, B_2353, F_2351, k9_subset_1(A_2354, C_2350, D_2352))!=k2_partfun1(C_2350, B_2353, E_2349, k9_subset_1(A_2354, C_2350, D_2352)) | ~m1_subset_1(F_2351, k1_zfmisc_1(k2_zfmisc_1(D_2352, B_2353))) | ~v1_funct_2(F_2351, D_2352, B_2353) | ~v1_funct_1(F_2351) | ~m1_subset_1(E_2349, k1_zfmisc_1(k2_zfmisc_1(C_2350, B_2353))) | ~v1_funct_2(E_2349, C_2350, B_2353) | ~v1_funct_1(E_2349) | ~m1_subset_1(D_2352, k1_zfmisc_1(A_2354)) | v1_xboole_0(D_2352) | ~m1_subset_1(C_2350, k1_zfmisc_1(A_2354)) | v1_xboole_0(C_2350) | v1_xboole_0(B_2353) | v1_xboole_0(A_2354))), inference(resolution, [status(thm)], [c_62, c_16900])).
% 15.37/6.90  tff(c_20449, plain, (![A_2354, C_2350, E_2349]: (k2_partfun1(k4_subset_1(A_2354, C_2350, '#skF_5'), '#skF_3', k1_tmap_1(A_2354, '#skF_3', C_2350, '#skF_5', E_2349, '#skF_7'), C_2350)=E_2349 | ~v1_funct_1(k1_tmap_1(A_2354, '#skF_3', C_2350, '#skF_5', E_2349, '#skF_7')) | k2_partfun1(C_2350, '#skF_3', E_2349, k9_subset_1(A_2354, C_2350, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_2354, C_2350, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_2349, k1_zfmisc_1(k2_zfmisc_1(C_2350, '#skF_3'))) | ~v1_funct_2(E_2349, C_2350, '#skF_3') | ~v1_funct_1(E_2349) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2354)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2350, k1_zfmisc_1(A_2354)) | v1_xboole_0(C_2350) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2354))), inference(resolution, [status(thm)], [c_68, c_20442])).
% 15.37/6.90  tff(c_20456, plain, (![A_2354, C_2350, E_2349]: (k2_partfun1(k4_subset_1(A_2354, C_2350, '#skF_5'), '#skF_3', k1_tmap_1(A_2354, '#skF_3', C_2350, '#skF_5', E_2349, '#skF_7'), C_2350)=E_2349 | ~v1_funct_1(k1_tmap_1(A_2354, '#skF_3', C_2350, '#skF_5', E_2349, '#skF_7')) | k2_partfun1(C_2350, '#skF_3', E_2349, k9_subset_1(A_2354, C_2350, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2354, C_2350, '#skF_5')) | ~m1_subset_1(E_2349, k1_zfmisc_1(k2_zfmisc_1(C_2350, '#skF_3'))) | ~v1_funct_2(E_2349, C_2350, '#skF_3') | ~v1_funct_1(E_2349) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2354)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_2350, k1_zfmisc_1(A_2354)) | v1_xboole_0(C_2350) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2354))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_13404, c_20449])).
% 15.37/6.90  tff(c_22280, plain, (![A_2492, C_2493, E_2494]: (k2_partfun1(k4_subset_1(A_2492, C_2493, '#skF_5'), '#skF_3', k1_tmap_1(A_2492, '#skF_3', C_2493, '#skF_5', E_2494, '#skF_7'), C_2493)=E_2494 | ~v1_funct_1(k1_tmap_1(A_2492, '#skF_3', C_2493, '#skF_5', E_2494, '#skF_7')) | k2_partfun1(C_2493, '#skF_3', E_2494, k9_subset_1(A_2492, C_2493, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2492, C_2493, '#skF_5')) | ~m1_subset_1(E_2494, k1_zfmisc_1(k2_zfmisc_1(C_2493, '#skF_3'))) | ~v1_funct_2(E_2494, C_2493, '#skF_3') | ~v1_funct_1(E_2494) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2492)) | ~m1_subset_1(C_2493, k1_zfmisc_1(A_2492)) | v1_xboole_0(C_2493) | v1_xboole_0(A_2492))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_20456])).
% 15.37/6.90  tff(c_22290, plain, (![A_2492]: (k2_partfun1(k4_subset_1(A_2492, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2492, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2492, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_2492, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_2492, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2492)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2492)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2492))), inference(resolution, [status(thm)], [c_74, c_22280])).
% 15.37/6.90  tff(c_22301, plain, (![A_2492]: (k2_partfun1(k4_subset_1(A_2492, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2492, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2492, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2492, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2492, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2492)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2492)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_2492))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_13407, c_22290])).
% 15.37/6.90  tff(c_23110, plain, (![A_2532]: (k2_partfun1(k4_subset_1(A_2532, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_2532, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_2532, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_2532, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_2532, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_2532)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2532)) | v1_xboole_0(A_2532))), inference(negUnitSimplification, [status(thm)], [c_88, c_22301])).
% 15.37/6.90  tff(c_1495, plain, (![C_462, B_463, A_464]: (~v1_xboole_0(C_462) | ~m1_subset_1(B_463, k1_zfmisc_1(C_462)) | ~r2_hidden(A_464, B_463))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.37/6.90  tff(c_1528, plain, (![B_470, A_471, A_472]: (~v1_xboole_0(B_470) | ~r2_hidden(A_471, A_472) | ~r1_tarski(A_472, B_470))), inference(resolution, [status(thm)], [c_26, c_1495])).
% 15.37/6.90  tff(c_1579, plain, (![B_483, B_484, A_485]: (~v1_xboole_0(B_483) | ~r1_tarski(B_484, B_483) | r1_xboole_0(A_485, B_484))), inference(resolution, [status(thm)], [c_10, c_1528])).
% 15.37/6.90  tff(c_1594, plain, (![B_9, A_485]: (~v1_xboole_0(B_9) | r1_xboole_0(A_485, B_9))), inference(resolution, [status(thm)], [c_18, c_1579])).
% 15.37/6.90  tff(c_1654, plain, (![B_500, A_501]: (k7_relat_1(B_500, A_501)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_500), A_501) | ~v1_relat_1(B_500))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.37/6.90  tff(c_1675, plain, (![B_502, B_503]: (k7_relat_1(B_502, B_503)=k1_xboole_0 | ~v1_relat_1(B_502) | ~v1_xboole_0(B_503))), inference(resolution, [status(thm)], [c_1594, c_1654])).
% 15.37/6.90  tff(c_1685, plain, (![B_504]: (k7_relat_1('#skF_6', B_504)=k1_xboole_0 | ~v1_xboole_0(B_504))), inference(resolution, [status(thm)], [c_1402, c_1675])).
% 15.37/6.90  tff(c_1689, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1685])).
% 15.37/6.90  tff(c_1449, plain, (![C_451, A_452, B_453]: (v4_relat_1(C_451, A_452) | ~m1_subset_1(C_451, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.37/6.90  tff(c_1462, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_1449])).
% 15.37/6.90  tff(c_1827, plain, (![B_531, A_532]: (k1_relat_1(B_531)=A_532 | ~v1_partfun1(B_531, A_532) | ~v4_relat_1(B_531, A_532) | ~v1_relat_1(B_531))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.37/6.90  tff(c_1833, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1462, c_1827])).
% 15.37/6.90  tff(c_1842, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_1833])).
% 15.37/6.90  tff(c_1861, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1842])).
% 15.37/6.90  tff(c_2027, plain, (![C_554, A_555, B_556]: (v1_partfun1(C_554, A_555) | ~v1_funct_2(C_554, A_555, B_556) | ~v1_funct_1(C_554) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_555, B_556))) | v1_xboole_0(B_556))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.37/6.90  tff(c_2037, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2027])).
% 15.37/6.90  tff(c_2045, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2037])).
% 15.37/6.90  tff(c_2047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1861, c_2045])).
% 15.37/6.90  tff(c_2048, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1842])).
% 15.37/6.90  tff(c_2058, plain, (![A_21]: (k7_relat_1('#skF_6', A_21)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_21) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2048, c_30])).
% 15.37/6.90  tff(c_2209, plain, (![A_566]: (k7_relat_1('#skF_6', A_566)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_566))), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_2058])).
% 15.37/6.90  tff(c_2217, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_24) | v1_xboole_0(B_24) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_2209])).
% 15.37/6.90  tff(c_2352, plain, (![B_578]: (k7_relat_1('#skF_6', B_578)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_578) | v1_xboole_0(B_578))), inference(negUnitSimplification, [status(thm)], [c_88, c_2217])).
% 15.37/6.90  tff(c_2358, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_2352])).
% 15.37/6.90  tff(c_2362, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_2358])).
% 15.37/6.90  tff(c_2053, plain, (![A_21]: (r1_xboole_0('#skF_4', A_21) | k7_relat_1('#skF_6', A_21)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2048, c_32])).
% 15.37/6.90  tff(c_2250, plain, (![A_568]: (r1_xboole_0('#skF_4', A_568) | k7_relat_1('#skF_6', A_568)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_2053])).
% 15.37/6.90  tff(c_2267, plain, (![A_568]: (k3_xboole_0('#skF_4', A_568)=k1_xboole_0 | k7_relat_1('#skF_6', A_568)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2250, c_2])).
% 15.37/6.90  tff(c_2375, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2362, c_2267])).
% 15.37/6.90  tff(c_1694, plain, (![B_505]: (k7_relat_1('#skF_7', B_505)=k1_xboole_0 | ~v1_xboole_0(B_505))), inference(resolution, [status(thm)], [c_1401, c_1675])).
% 15.37/6.90  tff(c_1698, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1694])).
% 15.37/6.90  tff(c_1736, plain, (![A_516, B_517, C_518]: (k9_subset_1(A_516, B_517, C_518)=k3_xboole_0(B_517, C_518) | ~m1_subset_1(C_518, k1_zfmisc_1(A_516)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.37/6.90  tff(c_1750, plain, (![B_517]: (k9_subset_1('#skF_2', B_517, '#skF_5')=k3_xboole_0(B_517, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_1736])).
% 15.37/6.90  tff(c_2388, plain, (![F_582, E_580, D_583, B_584, A_585, C_581]: (v1_funct_1(k1_tmap_1(A_585, B_584, C_581, D_583, E_580, F_582)) | ~m1_subset_1(F_582, k1_zfmisc_1(k2_zfmisc_1(D_583, B_584))) | ~v1_funct_2(F_582, D_583, B_584) | ~v1_funct_1(F_582) | ~m1_subset_1(E_580, k1_zfmisc_1(k2_zfmisc_1(C_581, B_584))) | ~v1_funct_2(E_580, C_581, B_584) | ~v1_funct_1(E_580) | ~m1_subset_1(D_583, k1_zfmisc_1(A_585)) | v1_xboole_0(D_583) | ~m1_subset_1(C_581, k1_zfmisc_1(A_585)) | v1_xboole_0(C_581) | v1_xboole_0(B_584) | v1_xboole_0(A_585))), inference(cnfTransformation, [status(thm)], [f_212])).
% 15.37/6.90  tff(c_2393, plain, (![A_585, C_581, E_580]: (v1_funct_1(k1_tmap_1(A_585, '#skF_3', C_581, '#skF_5', E_580, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_580, k1_zfmisc_1(k2_zfmisc_1(C_581, '#skF_3'))) | ~v1_funct_2(E_580, C_581, '#skF_3') | ~v1_funct_1(E_580) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_585)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_581, k1_zfmisc_1(A_585)) | v1_xboole_0(C_581) | v1_xboole_0('#skF_3') | v1_xboole_0(A_585))), inference(resolution, [status(thm)], [c_68, c_2388])).
% 15.37/6.90  tff(c_2399, plain, (![A_585, C_581, E_580]: (v1_funct_1(k1_tmap_1(A_585, '#skF_3', C_581, '#skF_5', E_580, '#skF_7')) | ~m1_subset_1(E_580, k1_zfmisc_1(k2_zfmisc_1(C_581, '#skF_3'))) | ~v1_funct_2(E_580, C_581, '#skF_3') | ~v1_funct_1(E_580) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_585)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_581, k1_zfmisc_1(A_585)) | v1_xboole_0(C_581) | v1_xboole_0('#skF_3') | v1_xboole_0(A_585))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2393])).
% 15.37/6.90  tff(c_2861, plain, (![A_648, C_649, E_650]: (v1_funct_1(k1_tmap_1(A_648, '#skF_3', C_649, '#skF_5', E_650, '#skF_7')) | ~m1_subset_1(E_650, k1_zfmisc_1(k2_zfmisc_1(C_649, '#skF_3'))) | ~v1_funct_2(E_650, C_649, '#skF_3') | ~v1_funct_1(E_650) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_648)) | ~m1_subset_1(C_649, k1_zfmisc_1(A_648)) | v1_xboole_0(C_649) | v1_xboole_0(A_648))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_2399])).
% 15.37/6.90  tff(c_2871, plain, (![A_648]: (v1_funct_1(k1_tmap_1(A_648, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_648)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_648)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_648))), inference(resolution, [status(thm)], [c_74, c_2861])).
% 15.37/6.90  tff(c_2882, plain, (![A_648]: (v1_funct_1(k1_tmap_1(A_648, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_648)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_648)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_648))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2871])).
% 15.37/6.90  tff(c_3101, plain, (![A_676]: (v1_funct_1(k1_tmap_1(A_676, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_676)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_676)) | v1_xboole_0(A_676))), inference(negUnitSimplification, [status(thm)], [c_88, c_2882])).
% 15.37/6.90  tff(c_3108, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_3101])).
% 15.37/6.90  tff(c_3112, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3108])).
% 15.37/6.90  tff(c_3113, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_3112])).
% 15.37/6.90  tff(c_1846, plain, (![A_533, B_534, C_535, D_536]: (k2_partfun1(A_533, B_534, C_535, D_536)=k7_relat_1(C_535, D_536) | ~m1_subset_1(C_535, k1_zfmisc_1(k2_zfmisc_1(A_533, B_534))) | ~v1_funct_1(C_535))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.37/6.90  tff(c_1853, plain, (![D_536]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_536)=k7_relat_1('#skF_6', D_536) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_1846])).
% 15.37/6.90  tff(c_1860, plain, (![D_536]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_536)=k7_relat_1('#skF_6', D_536))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1853])).
% 15.37/6.90  tff(c_1851, plain, (![D_536]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_536)=k7_relat_1('#skF_7', D_536) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_1846])).
% 15.37/6.90  tff(c_1857, plain, (![D_536]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_536)=k7_relat_1('#skF_7', D_536))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1851])).
% 15.37/6.90  tff(c_2953, plain, (![E_659, D_656, A_655, B_658, C_657, F_660]: (k2_partfun1(k4_subset_1(A_655, C_657, D_656), B_658, k1_tmap_1(A_655, B_658, C_657, D_656, E_659, F_660), D_656)=F_660 | ~m1_subset_1(k1_tmap_1(A_655, B_658, C_657, D_656, E_659, F_660), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_655, C_657, D_656), B_658))) | ~v1_funct_2(k1_tmap_1(A_655, B_658, C_657, D_656, E_659, F_660), k4_subset_1(A_655, C_657, D_656), B_658) | ~v1_funct_1(k1_tmap_1(A_655, B_658, C_657, D_656, E_659, F_660)) | k2_partfun1(D_656, B_658, F_660, k9_subset_1(A_655, C_657, D_656))!=k2_partfun1(C_657, B_658, E_659, k9_subset_1(A_655, C_657, D_656)) | ~m1_subset_1(F_660, k1_zfmisc_1(k2_zfmisc_1(D_656, B_658))) | ~v1_funct_2(F_660, D_656, B_658) | ~v1_funct_1(F_660) | ~m1_subset_1(E_659, k1_zfmisc_1(k2_zfmisc_1(C_657, B_658))) | ~v1_funct_2(E_659, C_657, B_658) | ~v1_funct_1(E_659) | ~m1_subset_1(D_656, k1_zfmisc_1(A_655)) | v1_xboole_0(D_656) | ~m1_subset_1(C_657, k1_zfmisc_1(A_655)) | v1_xboole_0(C_657) | v1_xboole_0(B_658) | v1_xboole_0(A_655))), inference(cnfTransformation, [status(thm)], [f_178])).
% 15.37/6.90  tff(c_5803, plain, (![D_988, F_987, C_986, B_989, E_985, A_990]: (k2_partfun1(k4_subset_1(A_990, C_986, D_988), B_989, k1_tmap_1(A_990, B_989, C_986, D_988, E_985, F_987), D_988)=F_987 | ~v1_funct_2(k1_tmap_1(A_990, B_989, C_986, D_988, E_985, F_987), k4_subset_1(A_990, C_986, D_988), B_989) | ~v1_funct_1(k1_tmap_1(A_990, B_989, C_986, D_988, E_985, F_987)) | k2_partfun1(D_988, B_989, F_987, k9_subset_1(A_990, C_986, D_988))!=k2_partfun1(C_986, B_989, E_985, k9_subset_1(A_990, C_986, D_988)) | ~m1_subset_1(F_987, k1_zfmisc_1(k2_zfmisc_1(D_988, B_989))) | ~v1_funct_2(F_987, D_988, B_989) | ~v1_funct_1(F_987) | ~m1_subset_1(E_985, k1_zfmisc_1(k2_zfmisc_1(C_986, B_989))) | ~v1_funct_2(E_985, C_986, B_989) | ~v1_funct_1(E_985) | ~m1_subset_1(D_988, k1_zfmisc_1(A_990)) | v1_xboole_0(D_988) | ~m1_subset_1(C_986, k1_zfmisc_1(A_990)) | v1_xboole_0(C_986) | v1_xboole_0(B_989) | v1_xboole_0(A_990))), inference(resolution, [status(thm)], [c_60, c_2953])).
% 15.37/6.90  tff(c_9358, plain, (![C_1275, B_1278, F_1276, A_1279, D_1277, E_1274]: (k2_partfun1(k4_subset_1(A_1279, C_1275, D_1277), B_1278, k1_tmap_1(A_1279, B_1278, C_1275, D_1277, E_1274, F_1276), D_1277)=F_1276 | ~v1_funct_1(k1_tmap_1(A_1279, B_1278, C_1275, D_1277, E_1274, F_1276)) | k2_partfun1(D_1277, B_1278, F_1276, k9_subset_1(A_1279, C_1275, D_1277))!=k2_partfun1(C_1275, B_1278, E_1274, k9_subset_1(A_1279, C_1275, D_1277)) | ~m1_subset_1(F_1276, k1_zfmisc_1(k2_zfmisc_1(D_1277, B_1278))) | ~v1_funct_2(F_1276, D_1277, B_1278) | ~v1_funct_1(F_1276) | ~m1_subset_1(E_1274, k1_zfmisc_1(k2_zfmisc_1(C_1275, B_1278))) | ~v1_funct_2(E_1274, C_1275, B_1278) | ~v1_funct_1(E_1274) | ~m1_subset_1(D_1277, k1_zfmisc_1(A_1279)) | v1_xboole_0(D_1277) | ~m1_subset_1(C_1275, k1_zfmisc_1(A_1279)) | v1_xboole_0(C_1275) | v1_xboole_0(B_1278) | v1_xboole_0(A_1279))), inference(resolution, [status(thm)], [c_62, c_5803])).
% 15.37/6.90  tff(c_9365, plain, (![A_1279, C_1275, E_1274]: (k2_partfun1(k4_subset_1(A_1279, C_1275, '#skF_5'), '#skF_3', k1_tmap_1(A_1279, '#skF_3', C_1275, '#skF_5', E_1274, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1279, '#skF_3', C_1275, '#skF_5', E_1274, '#skF_7')) | k2_partfun1(C_1275, '#skF_3', E_1274, k9_subset_1(A_1279, C_1275, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1279, C_1275, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1274, k1_zfmisc_1(k2_zfmisc_1(C_1275, '#skF_3'))) | ~v1_funct_2(E_1274, C_1275, '#skF_3') | ~v1_funct_1(E_1274) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1279)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1275, k1_zfmisc_1(A_1279)) | v1_xboole_0(C_1275) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1279))), inference(resolution, [status(thm)], [c_68, c_9358])).
% 15.37/6.90  tff(c_9372, plain, (![A_1279, C_1275, E_1274]: (k2_partfun1(k4_subset_1(A_1279, C_1275, '#skF_5'), '#skF_3', k1_tmap_1(A_1279, '#skF_3', C_1275, '#skF_5', E_1274, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1279, '#skF_3', C_1275, '#skF_5', E_1274, '#skF_7')) | k2_partfun1(C_1275, '#skF_3', E_1274, k9_subset_1(A_1279, C_1275, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1279, C_1275, '#skF_5')) | ~m1_subset_1(E_1274, k1_zfmisc_1(k2_zfmisc_1(C_1275, '#skF_3'))) | ~v1_funct_2(E_1274, C_1275, '#skF_3') | ~v1_funct_1(E_1274) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1279)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1275, k1_zfmisc_1(A_1279)) | v1_xboole_0(C_1275) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1279))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1857, c_9365])).
% 15.37/6.90  tff(c_11169, plain, (![A_1416, C_1417, E_1418]: (k2_partfun1(k4_subset_1(A_1416, C_1417, '#skF_5'), '#skF_3', k1_tmap_1(A_1416, '#skF_3', C_1417, '#skF_5', E_1418, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1416, '#skF_3', C_1417, '#skF_5', E_1418, '#skF_7')) | k2_partfun1(C_1417, '#skF_3', E_1418, k9_subset_1(A_1416, C_1417, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1416, C_1417, '#skF_5')) | ~m1_subset_1(E_1418, k1_zfmisc_1(k2_zfmisc_1(C_1417, '#skF_3'))) | ~v1_funct_2(E_1418, C_1417, '#skF_3') | ~v1_funct_1(E_1418) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1416)) | ~m1_subset_1(C_1417, k1_zfmisc_1(A_1416)) | v1_xboole_0(C_1417) | v1_xboole_0(A_1416))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_9372])).
% 15.37/6.90  tff(c_11179, plain, (![A_1416]: (k2_partfun1(k4_subset_1(A_1416, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1416, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1416, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1416, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1416, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1416)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1416)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1416))), inference(resolution, [status(thm)], [c_74, c_11169])).
% 15.37/6.90  tff(c_11190, plain, (![A_1416]: (k2_partfun1(k4_subset_1(A_1416, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1416, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1416, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1416, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1416, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1416)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1416)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1416))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1860, c_11179])).
% 15.37/6.90  tff(c_11999, plain, (![A_1456]: (k2_partfun1(k4_subset_1(A_1456, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1456, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1456, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1456, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1456, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1456)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1456)) | v1_xboole_0(A_1456))), inference(negUnitSimplification, [status(thm)], [c_88, c_11190])).
% 15.37/6.90  tff(c_147, plain, (![C_246, A_247, B_248]: (v1_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.37/6.90  tff(c_160, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_147])).
% 15.37/6.90  tff(c_292, plain, (![C_277, B_278, A_279]: (~v1_xboole_0(C_277) | ~m1_subset_1(B_278, k1_zfmisc_1(C_277)) | ~r2_hidden(A_279, B_278))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.37/6.90  tff(c_313, plain, (![B_282, A_283, A_284]: (~v1_xboole_0(B_282) | ~r2_hidden(A_283, A_284) | ~r1_tarski(A_284, B_282))), inference(resolution, [status(thm)], [c_26, c_292])).
% 15.37/6.90  tff(c_360, plain, (![B_293, B_294, A_295]: (~v1_xboole_0(B_293) | ~r1_tarski(B_294, B_293) | r1_xboole_0(A_295, B_294))), inference(resolution, [status(thm)], [c_10, c_313])).
% 15.37/6.90  tff(c_375, plain, (![B_9, A_295]: (~v1_xboole_0(B_9) | r1_xboole_0(A_295, B_9))), inference(resolution, [status(thm)], [c_18, c_360])).
% 15.37/6.90  tff(c_446, plain, (![B_311, A_312]: (k7_relat_1(B_311, A_312)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_311), A_312) | ~v1_relat_1(B_311))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.37/6.90  tff(c_471, plain, (![B_313, B_314]: (k7_relat_1(B_313, B_314)=k1_xboole_0 | ~v1_relat_1(B_313) | ~v1_xboole_0(B_314))), inference(resolution, [status(thm)], [c_375, c_446])).
% 15.37/6.90  tff(c_482, plain, (![B_316]: (k7_relat_1('#skF_6', B_316)=k1_xboole_0 | ~v1_xboole_0(B_316))), inference(resolution, [status(thm)], [c_160, c_471])).
% 15.37/6.90  tff(c_486, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_482])).
% 15.37/6.90  tff(c_1287, plain, (![A_420, B_421, C_422, D_423]: (k2_partfun1(A_420, B_421, C_422, D_423)=k7_relat_1(C_422, D_423) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))) | ~v1_funct_1(C_422))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.37/6.90  tff(c_1294, plain, (![D_423]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_423)=k7_relat_1('#skF_6', D_423) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_1287])).
% 15.37/6.90  tff(c_1301, plain, (![D_423]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_423)=k7_relat_1('#skF_6', D_423))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1294])).
% 15.37/6.90  tff(c_159, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_147])).
% 15.37/6.90  tff(c_491, plain, (![B_317]: (k7_relat_1('#skF_7', B_317)=k1_xboole_0 | ~v1_xboole_0(B_317))), inference(resolution, [status(thm)], [c_159, c_471])).
% 15.37/6.90  tff(c_495, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_491])).
% 15.37/6.90  tff(c_1292, plain, (![D_423]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_423)=k7_relat_1('#skF_7', D_423) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_1287])).
% 15.37/6.90  tff(c_1298, plain, (![D_423]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_423)=k7_relat_1('#skF_7', D_423))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1292])).
% 15.37/6.90  tff(c_244, plain, (![C_264, A_265, B_266]: (v4_relat_1(C_264, A_265) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.37/6.90  tff(c_257, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_244])).
% 15.37/6.90  tff(c_526, plain, (![B_329, A_330]: (k1_relat_1(B_329)=A_330 | ~v1_partfun1(B_329, A_330) | ~v4_relat_1(B_329, A_330) | ~v1_relat_1(B_329))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.37/6.91  tff(c_532, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_257, c_526])).
% 15.37/6.91  tff(c_541, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_532])).
% 15.37/6.91  tff(c_545, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_541])).
% 15.37/6.91  tff(c_1062, plain, (![C_401, A_402, B_403]: (v1_partfun1(C_401, A_402) | ~v1_funct_2(C_401, A_402, B_403) | ~v1_funct_1(C_401) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | v1_xboole_0(B_403))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.37/6.91  tff(c_1072, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1062])).
% 15.37/6.91  tff(c_1080, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1072])).
% 15.37/6.91  tff(c_1082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_545, c_1080])).
% 15.37/6.91  tff(c_1083, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_541])).
% 15.37/6.91  tff(c_1093, plain, (![A_21]: (k7_relat_1('#skF_6', A_21)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_21) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1083, c_30])).
% 15.37/6.91  tff(c_1124, plain, (![A_405]: (k7_relat_1('#skF_6', A_405)=k1_xboole_0 | ~r1_xboole_0('#skF_4', A_405))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_1093])).
% 15.37/6.91  tff(c_1131, plain, (![B_24]: (k7_relat_1('#skF_6', B_24)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_24) | v1_xboole_0(B_24) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_1124])).
% 15.37/6.91  tff(c_1236, plain, (![B_416]: (k7_relat_1('#skF_6', B_416)=k1_xboole_0 | ~r1_subset_1('#skF_4', B_416) | v1_xboole_0(B_416))), inference(negUnitSimplification, [status(thm)], [c_88, c_1131])).
% 15.37/6.91  tff(c_1242, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_1236])).
% 15.37/6.91  tff(c_1246, plain, (k7_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_1242])).
% 15.37/6.91  tff(c_1096, plain, (![A_21]: (r1_xboole_0('#skF_4', A_21) | k7_relat_1('#skF_6', A_21)!=k1_xboole_0 | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1083, c_32])).
% 15.37/6.91  tff(c_1110, plain, (![A_404]: (r1_xboole_0('#skF_4', A_404) | k7_relat_1('#skF_6', A_404)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_1096])).
% 15.37/6.91  tff(c_1123, plain, (![A_404]: (k3_xboole_0('#skF_4', A_404)=k1_xboole_0 | k7_relat_1('#skF_6', A_404)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1110, c_2])).
% 15.37/6.91  tff(c_1260, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1246, c_1123])).
% 15.37/6.91  tff(c_1182, plain, (![A_408, B_409, C_410]: (k9_subset_1(A_408, B_409, C_410)=k3_xboole_0(B_409, C_410) | ~m1_subset_1(C_410, k1_zfmisc_1(A_408)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.37/6.91  tff(c_1196, plain, (![B_409]: (k9_subset_1('#skF_2', B_409, '#skF_5')=k3_xboole_0(B_409, '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_1182])).
% 15.37/6.91  tff(c_66, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 15.37/6.91  tff(c_118, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_66])).
% 15.37/6.91  tff(c_1198, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_1196, c_118])).
% 15.37/6.91  tff(c_1330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_486, c_1301, c_495, c_1298, c_1260, c_1260, c_1198])).
% 15.37/6.91  tff(c_1331, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 15.37/6.91  tff(c_1404, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_1331])).
% 15.37/6.91  tff(c_12016, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11999, c_1404])).
% 15.37/6.91  tff(c_12038, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_1689, c_2375, c_1698, c_2375, c_1750, c_1750, c_3113, c_12016])).
% 15.37/6.91  tff(c_12040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_12038])).
% 15.37/6.91  tff(c_12041, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_1331])).
% 15.37/6.91  tff(c_23127, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_23110, c_12041])).
% 15.37/6.91  tff(c_23149, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_12346, c_13386, c_12355, c_13386, c_13296, c_13296, c_14326, c_23127])).
% 15.37/6.91  tff(c_23151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_23149])).
% 15.37/6.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.37/6.91  
% 15.37/6.91  Inference rules
% 15.37/6.91  ----------------------
% 15.37/6.91  #Ref     : 0
% 15.37/6.91  #Sup     : 4391
% 15.37/6.91  #Fact    : 0
% 15.37/6.91  #Define  : 0
% 15.37/6.91  #Split   : 45
% 15.37/6.91  #Chain   : 0
% 15.37/6.91  #Close   : 0
% 15.37/6.91  
% 15.37/6.91  Ordering : KBO
% 15.37/6.91  
% 15.37/6.91  Simplification rules
% 15.37/6.91  ----------------------
% 15.37/6.91  #Subsume      : 1168
% 15.37/6.91  #Demod        : 4769
% 15.37/6.91  #Tautology    : 1911
% 15.37/6.91  #SimpNegUnit  : 1450
% 15.37/6.91  #BackRed      : 13
% 15.37/6.91  
% 15.37/6.91  #Partial instantiations: 0
% 15.37/6.91  #Strategies tried      : 1
% 15.37/6.91  
% 15.37/6.91  Timing (in seconds)
% 15.37/6.91  ----------------------
% 15.37/6.91  Preprocessing        : 0.43
% 15.37/6.91  Parsing              : 0.21
% 15.37/6.91  CNF conversion       : 0.06
% 15.37/6.91  Main loop            : 5.67
% 15.37/6.91  Inferencing          : 1.86
% 15.37/6.91  Reduction            : 1.98
% 15.37/6.91  Demodulation         : 1.47
% 15.37/6.91  BG Simplification    : 0.10
% 15.37/6.91  Subsumption          : 1.45
% 15.37/6.91  Abstraction          : 0.17
% 15.37/6.91  MUC search           : 0.00
% 15.37/6.91  Cooper               : 0.00
% 15.37/6.91  Total                : 6.18
% 15.37/6.91  Index Insertion      : 0.00
% 15.37/6.91  Index Deletion       : 0.00
% 15.37/6.91  Index Matching       : 0.00
% 15.37/6.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
