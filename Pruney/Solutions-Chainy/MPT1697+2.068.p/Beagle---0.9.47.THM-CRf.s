%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:20 EST 2020

% Result     : Theorem 15.90s
% Output     : CNFRefutation 15.95s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 718 expanded)
%              Number of leaves         :   43 ( 273 expanded)
%              Depth                    :   15
%              Number of atoms          :  692 (3563 expanded)
%              Number of equality atoms :  139 ( 693 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_218,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_176,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_142,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_12,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_725,plain,(
    ! [C_327,A_328,B_329] :
      ( v1_relat_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_737,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_725])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_781,plain,(
    ! [B_335,A_336] :
      ( v4_relat_1(B_335,A_336)
      | ~ r1_tarski(k1_relat_1(B_335),A_336)
      | ~ v1_relat_1(B_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_786,plain,(
    ! [B_335] :
      ( v4_relat_1(B_335,k1_relat_1(B_335))
      | ~ v1_relat_1(B_335) ) ),
    inference(resolution,[status(thm)],[c_10,c_781])).

tff(c_10801,plain,(
    ! [C_1406,A_1407,B_1408] :
      ( v4_relat_1(C_1406,A_1407)
      | ~ m1_subset_1(C_1406,k1_zfmisc_1(B_1408))
      | ~ v4_relat_1(B_1408,A_1407)
      | ~ v1_relat_1(B_1408) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10805,plain,(
    ! [A_1407] :
      ( v4_relat_1('#skF_6',A_1407)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_1407)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_10801])).

tff(c_10826,plain,(
    ! [A_1409] :
      ( v4_relat_1('#skF_6',A_1409)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_1409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10805])).

tff(c_10830,plain,
    ( v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_786,c_10826])).

tff(c_10833,plain,(
    v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10830])).

tff(c_30,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10836,plain,
    ( k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10833,c_30])).

tff(c_10839,plain,(
    k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_10836])).

tff(c_28,plain,(
    ! [C_21,A_19,B_20] :
      ( k7_relat_1(k7_relat_1(C_21,A_19),B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10843,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10839,c_28])).

tff(c_10872,plain,(
    ! [B_1411] :
      ( k7_relat_1('#skF_6',B_1411) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_1411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_10843])).

tff(c_10999,plain,(
    ! [B_1422] :
      ( k7_relat_1('#skF_6',B_1422) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_1422) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_10872])).

tff(c_11004,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10999])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_10668,plain,(
    ! [A_1382,B_1383] :
      ( r1_xboole_0(A_1382,B_1383)
      | ~ r1_subset_1(A_1382,B_1383)
      | v1_xboole_0(B_1383)
      | v1_xboole_0(A_1382) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10790,plain,(
    ! [A_1404,B_1405] :
      ( k3_xboole_0(A_1404,B_1405) = k1_xboole_0
      | ~ r1_subset_1(A_1404,B_1405)
      | v1_xboole_0(B_1405)
      | v1_xboole_0(A_1404) ) ),
    inference(resolution,[status(thm)],[c_10668,c_2])).

tff(c_10796,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_10790])).

tff(c_10800,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_10796])).

tff(c_10704,plain,(
    ! [A_1390,B_1391,C_1392] :
      ( k9_subset_1(A_1390,B_1391,C_1392) = k3_xboole_0(B_1391,C_1392)
      | ~ m1_subset_1(C_1392,k1_zfmisc_1(A_1390)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10718,plain,(
    ! [B_1391] : k9_subset_1('#skF_1',B_1391,'#skF_4') = k3_xboole_0(B_1391,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10704])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_11047,plain,(
    ! [A_1425,B_1426,C_1427,D_1428] :
      ( k2_partfun1(A_1425,B_1426,C_1427,D_1428) = k7_relat_1(C_1427,D_1428)
      | ~ m1_subset_1(C_1427,k1_zfmisc_1(k2_zfmisc_1(A_1425,B_1426)))
      | ~ v1_funct_1(C_1427) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_11054,plain,(
    ! [D_1428] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1428) = k7_relat_1('#skF_5',D_1428)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_11047])).

tff(c_11077,plain,(
    ! [D_1430] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1430) = k7_relat_1('#skF_5',D_1430) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_11054])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_11052,plain,(
    ! [D_1428] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1428) = k7_relat_1('#skF_6',D_1428)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_11047])).

tff(c_11058,plain,(
    ! [D_1428] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1428) = k7_relat_1('#skF_6',D_1428) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_11052])).

tff(c_139,plain,(
    ! [C_237,A_238,B_239] :
      ( v1_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_152,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_139])).

tff(c_180,plain,(
    ! [B_247,A_248] :
      ( v4_relat_1(B_247,A_248)
      | ~ r1_tarski(k1_relat_1(B_247),A_248)
      | ~ v1_relat_1(B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_189,plain,(
    ! [B_247] :
      ( v4_relat_1(B_247,k1_relat_1(B_247))
      | ~ v1_relat_1(B_247) ) ),
    inference(resolution,[status(thm)],[c_10,c_180])).

tff(c_332,plain,(
    ! [C_273,A_274,B_275] :
      ( v4_relat_1(C_273,A_274)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(B_275))
      | ~ v4_relat_1(B_275,A_274)
      | ~ v1_relat_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_338,plain,(
    ! [A_274] :
      ( v4_relat_1('#skF_5',A_274)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_274)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_60,c_332])).

tff(c_376,plain,(
    ! [A_277] :
      ( v4_relat_1('#skF_5',A_277)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_338])).

tff(c_380,plain,
    ( v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_189,c_376])).

tff(c_383,plain,(
    v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_380])).

tff(c_386,plain,
    ( k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_383,c_30])).

tff(c_389,plain,(
    k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_386])).

tff(c_393,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_5',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_28])).

tff(c_444,plain,(
    ! [B_285] :
      ( k7_relat_1('#skF_5',B_285) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_393])).

tff(c_603,plain,(
    ! [B_314] :
      ( k7_relat_1('#skF_5',B_314) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_314) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_444])).

tff(c_608,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_603])).

tff(c_206,plain,(
    ! [A_251,B_252] :
      ( r1_xboole_0(A_251,B_252)
      | ~ r1_subset_1(A_251,B_252)
      | v1_xboole_0(B_252)
      | v1_xboole_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_456,plain,(
    ! [A_288,B_289] :
      ( k3_xboole_0(A_288,B_289) = k1_xboole_0
      | ~ r1_subset_1(A_288,B_289)
      | v1_xboole_0(B_289)
      | v1_xboole_0(A_288) ) ),
    inference(resolution,[status(thm)],[c_206,c_2])).

tff(c_462,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_456])).

tff(c_466,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_462])).

tff(c_399,plain,(
    ! [A_278,B_279,C_280,D_281] :
      ( k2_partfun1(A_278,B_279,C_280,D_281) = k7_relat_1(C_280,D_281)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279)))
      | ~ v1_funct_1(C_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_406,plain,(
    ! [D_281] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_281) = k7_relat_1('#skF_5',D_281)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_399])).

tff(c_413,plain,(
    ! [D_281] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_281) = k7_relat_1('#skF_5',D_281) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_406])).

tff(c_404,plain,(
    ! [D_281] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_281) = k7_relat_1('#skF_6',D_281)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_399])).

tff(c_410,plain,(
    ! [D_281] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_281) = k7_relat_1('#skF_6',D_281) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_404])).

tff(c_221,plain,(
    ! [A_258,B_259,C_260] :
      ( k9_subset_1(A_258,B_259,C_260) = k3_xboole_0(B_259,C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(A_258)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_235,plain,(
    ! [B_259] : k9_subset_1('#skF_1',B_259,'#skF_4') = k3_xboole_0(B_259,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_221])).

tff(c_52,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_96,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_237,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_235,c_96])).

tff(c_443,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_410,c_237])).

tff(c_467,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_466,c_443])).

tff(c_621,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_467])).

tff(c_151,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_139])).

tff(c_336,plain,(
    ! [A_274] :
      ( v4_relat_1('#skF_6',A_274)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_274)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_332])).

tff(c_352,plain,(
    ! [A_276] :
      ( v4_relat_1('#skF_6',A_276)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_336])).

tff(c_356,plain,
    ( v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_189,c_352])).

tff(c_359,plain,(
    v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_356])).

tff(c_362,plain,
    ( k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_359,c_30])).

tff(c_365,plain,(
    k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_362])).

tff(c_369,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_28])).

tff(c_432,plain,(
    ! [B_284] :
      ( k7_relat_1('#skF_6',B_284) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_369])).

tff(c_693,plain,(
    ! [B_324] :
      ( k7_relat_1('#skF_6',B_324) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_324) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_432])).

tff(c_697,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_693])).

tff(c_701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_697])).

tff(c_703,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10720,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10718,c_10718,c_703])).

tff(c_10894,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10800,c_10800,c_10720])).

tff(c_11062,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11058,c_10894])).

tff(c_11063,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11004,c_11062])).

tff(c_11083,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11077,c_11063])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_11122,plain,(
    ! [C_1434,A_1438,D_1436,E_1437,B_1435,F_1439] :
      ( v1_funct_1(k1_tmap_1(A_1438,B_1435,C_1434,D_1436,E_1437,F_1439))
      | ~ m1_subset_1(F_1439,k1_zfmisc_1(k2_zfmisc_1(D_1436,B_1435)))
      | ~ v1_funct_2(F_1439,D_1436,B_1435)
      | ~ v1_funct_1(F_1439)
      | ~ m1_subset_1(E_1437,k1_zfmisc_1(k2_zfmisc_1(C_1434,B_1435)))
      | ~ v1_funct_2(E_1437,C_1434,B_1435)
      | ~ v1_funct_1(E_1437)
      | ~ m1_subset_1(D_1436,k1_zfmisc_1(A_1438))
      | v1_xboole_0(D_1436)
      | ~ m1_subset_1(C_1434,k1_zfmisc_1(A_1438))
      | v1_xboole_0(C_1434)
      | v1_xboole_0(B_1435)
      | v1_xboole_0(A_1438) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_11127,plain,(
    ! [A_1438,C_1434,E_1437] :
      ( v1_funct_1(k1_tmap_1(A_1438,'#skF_2',C_1434,'#skF_4',E_1437,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1437,k1_zfmisc_1(k2_zfmisc_1(C_1434,'#skF_2')))
      | ~ v1_funct_2(E_1437,C_1434,'#skF_2')
      | ~ v1_funct_1(E_1437)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1438))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1434,k1_zfmisc_1(A_1438))
      | v1_xboole_0(C_1434)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1438) ) ),
    inference(resolution,[status(thm)],[c_54,c_11122])).

tff(c_11133,plain,(
    ! [A_1438,C_1434,E_1437] :
      ( v1_funct_1(k1_tmap_1(A_1438,'#skF_2',C_1434,'#skF_4',E_1437,'#skF_6'))
      | ~ m1_subset_1(E_1437,k1_zfmisc_1(k2_zfmisc_1(C_1434,'#skF_2')))
      | ~ v1_funct_2(E_1437,C_1434,'#skF_2')
      | ~ v1_funct_1(E_1437)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1438))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1434,k1_zfmisc_1(A_1438))
      | v1_xboole_0(C_1434)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11127])).

tff(c_11701,plain,(
    ! [A_1503,C_1504,E_1505] :
      ( v1_funct_1(k1_tmap_1(A_1503,'#skF_2',C_1504,'#skF_4',E_1505,'#skF_6'))
      | ~ m1_subset_1(E_1505,k1_zfmisc_1(k2_zfmisc_1(C_1504,'#skF_2')))
      | ~ v1_funct_2(E_1505,C_1504,'#skF_2')
      | ~ v1_funct_1(E_1505)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1503))
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(A_1503))
      | v1_xboole_0(C_1504)
      | v1_xboole_0(A_1503) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_11133])).

tff(c_11711,plain,(
    ! [A_1503] :
      ( v1_funct_1(k1_tmap_1(A_1503,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1503))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1503))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1503) ) ),
    inference(resolution,[status(thm)],[c_60,c_11701])).

tff(c_11722,plain,(
    ! [A_1503] :
      ( v1_funct_1(k1_tmap_1(A_1503,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1503))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1503))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_11711])).

tff(c_11836,plain,(
    ! [A_1518] :
      ( v1_funct_1(k1_tmap_1(A_1518,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1518))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1518))
      | v1_xboole_0(A_1518) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_11722])).

tff(c_11843,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_11836])).

tff(c_11847,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_11843])).

tff(c_11848,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_11847])).

tff(c_11061,plain,(
    ! [D_1428] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1428) = k7_relat_1('#skF_5',D_1428) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_11054])).

tff(c_48,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_11630,plain,(
    ! [C_1499,D_1500,B_1497,A_1495,F_1498,E_1496] :
      ( k2_partfun1(k4_subset_1(A_1495,C_1499,D_1500),B_1497,k1_tmap_1(A_1495,B_1497,C_1499,D_1500,E_1496,F_1498),C_1499) = E_1496
      | ~ m1_subset_1(k1_tmap_1(A_1495,B_1497,C_1499,D_1500,E_1496,F_1498),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1495,C_1499,D_1500),B_1497)))
      | ~ v1_funct_2(k1_tmap_1(A_1495,B_1497,C_1499,D_1500,E_1496,F_1498),k4_subset_1(A_1495,C_1499,D_1500),B_1497)
      | ~ v1_funct_1(k1_tmap_1(A_1495,B_1497,C_1499,D_1500,E_1496,F_1498))
      | k2_partfun1(D_1500,B_1497,F_1498,k9_subset_1(A_1495,C_1499,D_1500)) != k2_partfun1(C_1499,B_1497,E_1496,k9_subset_1(A_1495,C_1499,D_1500))
      | ~ m1_subset_1(F_1498,k1_zfmisc_1(k2_zfmisc_1(D_1500,B_1497)))
      | ~ v1_funct_2(F_1498,D_1500,B_1497)
      | ~ v1_funct_1(F_1498)
      | ~ m1_subset_1(E_1496,k1_zfmisc_1(k2_zfmisc_1(C_1499,B_1497)))
      | ~ v1_funct_2(E_1496,C_1499,B_1497)
      | ~ v1_funct_1(E_1496)
      | ~ m1_subset_1(D_1500,k1_zfmisc_1(A_1495))
      | v1_xboole_0(D_1500)
      | ~ m1_subset_1(C_1499,k1_zfmisc_1(A_1495))
      | v1_xboole_0(C_1499)
      | v1_xboole_0(B_1497)
      | v1_xboole_0(A_1495) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_13045,plain,(
    ! [B_1651,A_1654,D_1652,C_1650,E_1653,F_1655] :
      ( k2_partfun1(k4_subset_1(A_1654,C_1650,D_1652),B_1651,k1_tmap_1(A_1654,B_1651,C_1650,D_1652,E_1653,F_1655),C_1650) = E_1653
      | ~ v1_funct_2(k1_tmap_1(A_1654,B_1651,C_1650,D_1652,E_1653,F_1655),k4_subset_1(A_1654,C_1650,D_1652),B_1651)
      | ~ v1_funct_1(k1_tmap_1(A_1654,B_1651,C_1650,D_1652,E_1653,F_1655))
      | k2_partfun1(D_1652,B_1651,F_1655,k9_subset_1(A_1654,C_1650,D_1652)) != k2_partfun1(C_1650,B_1651,E_1653,k9_subset_1(A_1654,C_1650,D_1652))
      | ~ m1_subset_1(F_1655,k1_zfmisc_1(k2_zfmisc_1(D_1652,B_1651)))
      | ~ v1_funct_2(F_1655,D_1652,B_1651)
      | ~ v1_funct_1(F_1655)
      | ~ m1_subset_1(E_1653,k1_zfmisc_1(k2_zfmisc_1(C_1650,B_1651)))
      | ~ v1_funct_2(E_1653,C_1650,B_1651)
      | ~ v1_funct_1(E_1653)
      | ~ m1_subset_1(D_1652,k1_zfmisc_1(A_1654))
      | v1_xboole_0(D_1652)
      | ~ m1_subset_1(C_1650,k1_zfmisc_1(A_1654))
      | v1_xboole_0(C_1650)
      | v1_xboole_0(B_1651)
      | v1_xboole_0(A_1654) ) ),
    inference(resolution,[status(thm)],[c_46,c_11630])).

tff(c_15437,plain,(
    ! [A_1906,B_1903,F_1907,C_1902,D_1904,E_1905] :
      ( k2_partfun1(k4_subset_1(A_1906,C_1902,D_1904),B_1903,k1_tmap_1(A_1906,B_1903,C_1902,D_1904,E_1905,F_1907),C_1902) = E_1905
      | ~ v1_funct_1(k1_tmap_1(A_1906,B_1903,C_1902,D_1904,E_1905,F_1907))
      | k2_partfun1(D_1904,B_1903,F_1907,k9_subset_1(A_1906,C_1902,D_1904)) != k2_partfun1(C_1902,B_1903,E_1905,k9_subset_1(A_1906,C_1902,D_1904))
      | ~ m1_subset_1(F_1907,k1_zfmisc_1(k2_zfmisc_1(D_1904,B_1903)))
      | ~ v1_funct_2(F_1907,D_1904,B_1903)
      | ~ v1_funct_1(F_1907)
      | ~ m1_subset_1(E_1905,k1_zfmisc_1(k2_zfmisc_1(C_1902,B_1903)))
      | ~ v1_funct_2(E_1905,C_1902,B_1903)
      | ~ v1_funct_1(E_1905)
      | ~ m1_subset_1(D_1904,k1_zfmisc_1(A_1906))
      | v1_xboole_0(D_1904)
      | ~ m1_subset_1(C_1902,k1_zfmisc_1(A_1906))
      | v1_xboole_0(C_1902)
      | v1_xboole_0(B_1903)
      | v1_xboole_0(A_1906) ) ),
    inference(resolution,[status(thm)],[c_48,c_13045])).

tff(c_15444,plain,(
    ! [A_1906,C_1902,E_1905] :
      ( k2_partfun1(k4_subset_1(A_1906,C_1902,'#skF_4'),'#skF_2',k1_tmap_1(A_1906,'#skF_2',C_1902,'#skF_4',E_1905,'#skF_6'),C_1902) = E_1905
      | ~ v1_funct_1(k1_tmap_1(A_1906,'#skF_2',C_1902,'#skF_4',E_1905,'#skF_6'))
      | k2_partfun1(C_1902,'#skF_2',E_1905,k9_subset_1(A_1906,C_1902,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1906,C_1902,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1905,k1_zfmisc_1(k2_zfmisc_1(C_1902,'#skF_2')))
      | ~ v1_funct_2(E_1905,C_1902,'#skF_2')
      | ~ v1_funct_1(E_1905)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1906))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1902,k1_zfmisc_1(A_1906))
      | v1_xboole_0(C_1902)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1906) ) ),
    inference(resolution,[status(thm)],[c_54,c_15437])).

tff(c_15451,plain,(
    ! [A_1906,C_1902,E_1905] :
      ( k2_partfun1(k4_subset_1(A_1906,C_1902,'#skF_4'),'#skF_2',k1_tmap_1(A_1906,'#skF_2',C_1902,'#skF_4',E_1905,'#skF_6'),C_1902) = E_1905
      | ~ v1_funct_1(k1_tmap_1(A_1906,'#skF_2',C_1902,'#skF_4',E_1905,'#skF_6'))
      | k2_partfun1(C_1902,'#skF_2',E_1905,k9_subset_1(A_1906,C_1902,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1906,C_1902,'#skF_4'))
      | ~ m1_subset_1(E_1905,k1_zfmisc_1(k2_zfmisc_1(C_1902,'#skF_2')))
      | ~ v1_funct_2(E_1905,C_1902,'#skF_2')
      | ~ v1_funct_1(E_1905)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1906))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1902,k1_zfmisc_1(A_1906))
      | v1_xboole_0(C_1902)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1906) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11058,c_15444])).

tff(c_18150,plain,(
    ! [A_2182,C_2183,E_2184] :
      ( k2_partfun1(k4_subset_1(A_2182,C_2183,'#skF_4'),'#skF_2',k1_tmap_1(A_2182,'#skF_2',C_2183,'#skF_4',E_2184,'#skF_6'),C_2183) = E_2184
      | ~ v1_funct_1(k1_tmap_1(A_2182,'#skF_2',C_2183,'#skF_4',E_2184,'#skF_6'))
      | k2_partfun1(C_2183,'#skF_2',E_2184,k9_subset_1(A_2182,C_2183,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2182,C_2183,'#skF_4'))
      | ~ m1_subset_1(E_2184,k1_zfmisc_1(k2_zfmisc_1(C_2183,'#skF_2')))
      | ~ v1_funct_2(E_2184,C_2183,'#skF_2')
      | ~ v1_funct_1(E_2184)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2182))
      | ~ m1_subset_1(C_2183,k1_zfmisc_1(A_2182))
      | v1_xboole_0(C_2183)
      | v1_xboole_0(A_2182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_15451])).

tff(c_18160,plain,(
    ! [A_2182] :
      ( k2_partfun1(k4_subset_1(A_2182,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2182,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2182,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2182,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2182,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2182))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2182))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2182) ) ),
    inference(resolution,[status(thm)],[c_60,c_18150])).

tff(c_18171,plain,(
    ! [A_2182] :
      ( k2_partfun1(k4_subset_1(A_2182,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2182,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2182,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2182,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2182,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2182))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2182))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_11061,c_18160])).

tff(c_20174,plain,(
    ! [A_2371] :
      ( k2_partfun1(k4_subset_1(A_2371,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2371,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2371,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2371,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2371,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2371))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2371))
      | v1_xboole_0(A_2371) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_18171])).

tff(c_738,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_725])).

tff(c_956,plain,(
    ! [C_369,A_370,B_371] :
      ( v4_relat_1(C_369,A_370)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(B_371))
      | ~ v4_relat_1(B_371,A_370)
      | ~ v1_relat_1(B_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_962,plain,(
    ! [A_370] :
      ( v4_relat_1('#skF_5',A_370)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_370)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_60,c_956])).

tff(c_1004,plain,(
    ! [A_373] :
      ( v4_relat_1('#skF_5',A_373)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_962])).

tff(c_1008,plain,
    ( v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_786,c_1004])).

tff(c_1011,plain,(
    v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1008])).

tff(c_1014,plain,
    ( k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1011,c_30])).

tff(c_1017,plain,(
    k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_1014])).

tff(c_1021,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_5',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_28])).

tff(c_1038,plain,(
    ! [B_375] :
      ( k7_relat_1('#skF_5',B_375) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_1021])).

tff(c_1254,plain,(
    ! [B_398] :
      ( k7_relat_1('#skF_5',B_398) = k1_xboole_0
      | k3_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_398) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1038])).

tff(c_1259,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1254])).

tff(c_1136,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( k2_partfun1(A_384,B_385,C_386,D_387) = k7_relat_1(C_386,D_387)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385)))
      | ~ v1_funct_1(C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1141,plain,(
    ! [D_387] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_387) = k7_relat_1('#skF_6',D_387)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_1136])).

tff(c_1147,plain,(
    ! [D_387] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_387) = k7_relat_1('#skF_6',D_387) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1141])).

tff(c_823,plain,(
    ! [A_345,B_346] :
      ( r1_xboole_0(A_345,B_346)
      | ~ r1_subset_1(A_345,B_346)
      | v1_xboole_0(B_346)
      | v1_xboole_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_945,plain,(
    ! [A_367,B_368] :
      ( k3_xboole_0(A_367,B_368) = k1_xboole_0
      | ~ r1_subset_1(A_367,B_368)
      | v1_xboole_0(B_368)
      | v1_xboole_0(A_367) ) ),
    inference(resolution,[status(thm)],[c_823,c_2])).

tff(c_951,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_945])).

tff(c_955,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_951])).

tff(c_859,plain,(
    ! [A_353,B_354,C_355] :
      ( k9_subset_1(A_353,B_354,C_355) = k3_xboole_0(B_354,C_355)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(A_353)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_873,plain,(
    ! [B_354] : k9_subset_1('#skF_1',B_354,'#skF_4') = k3_xboole_0(B_354,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_859])).

tff(c_875,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_873,c_703])).

tff(c_1049,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_955,c_875])).

tff(c_1151,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_1049])).

tff(c_1143,plain,(
    ! [D_387] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_387) = k7_relat_1('#skF_5',D_387)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_1136])).

tff(c_1150,plain,(
    ! [D_387] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_387) = k7_relat_1('#skF_5',D_387) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1143])).

tff(c_1173,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_1150])).

tff(c_1277,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1259,c_1173])).

tff(c_1236,plain,(
    ! [B_393,A_396,F_397,D_394,C_392,E_395] :
      ( v1_funct_1(k1_tmap_1(A_396,B_393,C_392,D_394,E_395,F_397))
      | ~ m1_subset_1(F_397,k1_zfmisc_1(k2_zfmisc_1(D_394,B_393)))
      | ~ v1_funct_2(F_397,D_394,B_393)
      | ~ v1_funct_1(F_397)
      | ~ m1_subset_1(E_395,k1_zfmisc_1(k2_zfmisc_1(C_392,B_393)))
      | ~ v1_funct_2(E_395,C_392,B_393)
      | ~ v1_funct_1(E_395)
      | ~ m1_subset_1(D_394,k1_zfmisc_1(A_396))
      | v1_xboole_0(D_394)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(A_396))
      | v1_xboole_0(C_392)
      | v1_xboole_0(B_393)
      | v1_xboole_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1241,plain,(
    ! [A_396,C_392,E_395] :
      ( v1_funct_1(k1_tmap_1(A_396,'#skF_2',C_392,'#skF_4',E_395,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_395,k1_zfmisc_1(k2_zfmisc_1(C_392,'#skF_2')))
      | ~ v1_funct_2(E_395,C_392,'#skF_2')
      | ~ v1_funct_1(E_395)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_396))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_392,k1_zfmisc_1(A_396))
      | v1_xboole_0(C_392)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_396) ) ),
    inference(resolution,[status(thm)],[c_54,c_1236])).

tff(c_1247,plain,(
    ! [A_396,C_392,E_395] :
      ( v1_funct_1(k1_tmap_1(A_396,'#skF_2',C_392,'#skF_4',E_395,'#skF_6'))
      | ~ m1_subset_1(E_395,k1_zfmisc_1(k2_zfmisc_1(C_392,'#skF_2')))
      | ~ v1_funct_2(E_395,C_392,'#skF_2')
      | ~ v1_funct_1(E_395)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_396))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_392,k1_zfmisc_1(A_396))
      | v1_xboole_0(C_392)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1241])).

tff(c_1260,plain,(
    ! [A_399,C_400,E_401] :
      ( v1_funct_1(k1_tmap_1(A_399,'#skF_2',C_400,'#skF_4',E_401,'#skF_6'))
      | ~ m1_subset_1(E_401,k1_zfmisc_1(k2_zfmisc_1(C_400,'#skF_2')))
      | ~ v1_funct_2(E_401,C_400,'#skF_2')
      | ~ v1_funct_1(E_401)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_399))
      | ~ m1_subset_1(C_400,k1_zfmisc_1(A_399))
      | v1_xboole_0(C_400)
      | v1_xboole_0(A_399) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_1247])).

tff(c_1267,plain,(
    ! [A_399] :
      ( v1_funct_1(k1_tmap_1(A_399,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_399))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_399))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_399) ) ),
    inference(resolution,[status(thm)],[c_60,c_1260])).

tff(c_1275,plain,(
    ! [A_399] :
      ( v1_funct_1(k1_tmap_1(A_399,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_399))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_399))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1267])).

tff(c_1449,plain,(
    ! [A_427] :
      ( v1_funct_1(k1_tmap_1(A_427,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_427))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_427))
      | v1_xboole_0(A_427) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1275])).

tff(c_1456,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_1449])).

tff(c_1460,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1456])).

tff(c_1461,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1460])).

tff(c_1671,plain,(
    ! [B_435,A_433,C_437,E_434,F_436,D_438] :
      ( k2_partfun1(k4_subset_1(A_433,C_437,D_438),B_435,k1_tmap_1(A_433,B_435,C_437,D_438,E_434,F_436),D_438) = F_436
      | ~ m1_subset_1(k1_tmap_1(A_433,B_435,C_437,D_438,E_434,F_436),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_433,C_437,D_438),B_435)))
      | ~ v1_funct_2(k1_tmap_1(A_433,B_435,C_437,D_438,E_434,F_436),k4_subset_1(A_433,C_437,D_438),B_435)
      | ~ v1_funct_1(k1_tmap_1(A_433,B_435,C_437,D_438,E_434,F_436))
      | k2_partfun1(D_438,B_435,F_436,k9_subset_1(A_433,C_437,D_438)) != k2_partfun1(C_437,B_435,E_434,k9_subset_1(A_433,C_437,D_438))
      | ~ m1_subset_1(F_436,k1_zfmisc_1(k2_zfmisc_1(D_438,B_435)))
      | ~ v1_funct_2(F_436,D_438,B_435)
      | ~ v1_funct_1(F_436)
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(C_437,B_435)))
      | ~ v1_funct_2(E_434,C_437,B_435)
      | ~ v1_funct_1(E_434)
      | ~ m1_subset_1(D_438,k1_zfmisc_1(A_433))
      | v1_xboole_0(D_438)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(A_433))
      | v1_xboole_0(C_437)
      | v1_xboole_0(B_435)
      | v1_xboole_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2907,plain,(
    ! [F_593,E_591,D_590,A_592,C_588,B_589] :
      ( k2_partfun1(k4_subset_1(A_592,C_588,D_590),B_589,k1_tmap_1(A_592,B_589,C_588,D_590,E_591,F_593),D_590) = F_593
      | ~ v1_funct_2(k1_tmap_1(A_592,B_589,C_588,D_590,E_591,F_593),k4_subset_1(A_592,C_588,D_590),B_589)
      | ~ v1_funct_1(k1_tmap_1(A_592,B_589,C_588,D_590,E_591,F_593))
      | k2_partfun1(D_590,B_589,F_593,k9_subset_1(A_592,C_588,D_590)) != k2_partfun1(C_588,B_589,E_591,k9_subset_1(A_592,C_588,D_590))
      | ~ m1_subset_1(F_593,k1_zfmisc_1(k2_zfmisc_1(D_590,B_589)))
      | ~ v1_funct_2(F_593,D_590,B_589)
      | ~ v1_funct_1(F_593)
      | ~ m1_subset_1(E_591,k1_zfmisc_1(k2_zfmisc_1(C_588,B_589)))
      | ~ v1_funct_2(E_591,C_588,B_589)
      | ~ v1_funct_1(E_591)
      | ~ m1_subset_1(D_590,k1_zfmisc_1(A_592))
      | v1_xboole_0(D_590)
      | ~ m1_subset_1(C_588,k1_zfmisc_1(A_592))
      | v1_xboole_0(C_588)
      | v1_xboole_0(B_589)
      | v1_xboole_0(A_592) ) ),
    inference(resolution,[status(thm)],[c_46,c_1671])).

tff(c_5574,plain,(
    ! [A_868,F_869,E_867,C_864,B_865,D_866] :
      ( k2_partfun1(k4_subset_1(A_868,C_864,D_866),B_865,k1_tmap_1(A_868,B_865,C_864,D_866,E_867,F_869),D_866) = F_869
      | ~ v1_funct_1(k1_tmap_1(A_868,B_865,C_864,D_866,E_867,F_869))
      | k2_partfun1(D_866,B_865,F_869,k9_subset_1(A_868,C_864,D_866)) != k2_partfun1(C_864,B_865,E_867,k9_subset_1(A_868,C_864,D_866))
      | ~ m1_subset_1(F_869,k1_zfmisc_1(k2_zfmisc_1(D_866,B_865)))
      | ~ v1_funct_2(F_869,D_866,B_865)
      | ~ v1_funct_1(F_869)
      | ~ m1_subset_1(E_867,k1_zfmisc_1(k2_zfmisc_1(C_864,B_865)))
      | ~ v1_funct_2(E_867,C_864,B_865)
      | ~ v1_funct_1(E_867)
      | ~ m1_subset_1(D_866,k1_zfmisc_1(A_868))
      | v1_xboole_0(D_866)
      | ~ m1_subset_1(C_864,k1_zfmisc_1(A_868))
      | v1_xboole_0(C_864)
      | v1_xboole_0(B_865)
      | v1_xboole_0(A_868) ) ),
    inference(resolution,[status(thm)],[c_48,c_2907])).

tff(c_5581,plain,(
    ! [A_868,C_864,E_867] :
      ( k2_partfun1(k4_subset_1(A_868,C_864,'#skF_4'),'#skF_2',k1_tmap_1(A_868,'#skF_2',C_864,'#skF_4',E_867,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_868,'#skF_2',C_864,'#skF_4',E_867,'#skF_6'))
      | k2_partfun1(C_864,'#skF_2',E_867,k9_subset_1(A_868,C_864,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_868,C_864,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_867,k1_zfmisc_1(k2_zfmisc_1(C_864,'#skF_2')))
      | ~ v1_funct_2(E_867,C_864,'#skF_2')
      | ~ v1_funct_1(E_867)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_868))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_864,k1_zfmisc_1(A_868))
      | v1_xboole_0(C_864)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_868) ) ),
    inference(resolution,[status(thm)],[c_54,c_5574])).

tff(c_5588,plain,(
    ! [A_868,C_864,E_867] :
      ( k2_partfun1(k4_subset_1(A_868,C_864,'#skF_4'),'#skF_2',k1_tmap_1(A_868,'#skF_2',C_864,'#skF_4',E_867,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_868,'#skF_2',C_864,'#skF_4',E_867,'#skF_6'))
      | k2_partfun1(C_864,'#skF_2',E_867,k9_subset_1(A_868,C_864,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_868,C_864,'#skF_4'))
      | ~ m1_subset_1(E_867,k1_zfmisc_1(k2_zfmisc_1(C_864,'#skF_2')))
      | ~ v1_funct_2(E_867,C_864,'#skF_2')
      | ~ v1_funct_1(E_867)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_868))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_864,k1_zfmisc_1(A_868))
      | v1_xboole_0(C_864)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_868) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1147,c_5581])).

tff(c_8217,plain,(
    ! [A_1125,C_1126,E_1127] :
      ( k2_partfun1(k4_subset_1(A_1125,C_1126,'#skF_4'),'#skF_2',k1_tmap_1(A_1125,'#skF_2',C_1126,'#skF_4',E_1127,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1125,'#skF_2',C_1126,'#skF_4',E_1127,'#skF_6'))
      | k2_partfun1(C_1126,'#skF_2',E_1127,k9_subset_1(A_1125,C_1126,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1125,C_1126,'#skF_4'))
      | ~ m1_subset_1(E_1127,k1_zfmisc_1(k2_zfmisc_1(C_1126,'#skF_2')))
      | ~ v1_funct_2(E_1127,C_1126,'#skF_2')
      | ~ v1_funct_1(E_1127)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1125))
      | ~ m1_subset_1(C_1126,k1_zfmisc_1(A_1125))
      | v1_xboole_0(C_1126)
      | v1_xboole_0(A_1125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_5588])).

tff(c_8227,plain,(
    ! [A_1125] :
      ( k2_partfun1(k4_subset_1(A_1125,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1125,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1125,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1125,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1125,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1125))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1125))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1125) ) ),
    inference(resolution,[status(thm)],[c_60,c_8217])).

tff(c_8238,plain,(
    ! [A_1125] :
      ( k2_partfun1(k4_subset_1(A_1125,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1125,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1125,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1125,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1125,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1125))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1125))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1150,c_8227])).

tff(c_10598,plain,(
    ! [A_1379] :
      ( k2_partfun1(k4_subset_1(A_1379,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1379,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1379,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1379,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1379,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1379))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1379))
      | v1_xboole_0(A_1379) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8238])).

tff(c_702,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_816,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_702])).

tff(c_10621,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10598,c_816])).

tff(c_10657,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1277,c_955,c_873,c_1259,c_955,c_873,c_1461,c_10621])).

tff(c_10659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_10657])).

tff(c_10660,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_702])).

tff(c_20197,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20174,c_10660])).

tff(c_20233,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_11004,c_10800,c_10718,c_11083,c_10800,c_10718,c_11848,c_20197])).

tff(c_20235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_20233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.90/7.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/7.44  
% 15.95/7.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/7.44  %$ v1_funct_2 > v4_relat_1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.95/7.44  
% 15.95/7.44  %Foreground sorts:
% 15.95/7.44  
% 15.95/7.44  
% 15.95/7.44  %Background operators:
% 15.95/7.44  
% 15.95/7.44  
% 15.95/7.44  %Foreground operators:
% 15.95/7.44  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 15.95/7.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.95/7.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.95/7.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.95/7.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.95/7.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.95/7.44  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 15.95/7.44  tff('#skF_5', type, '#skF_5': $i).
% 15.95/7.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.95/7.44  tff('#skF_6', type, '#skF_6': $i).
% 15.95/7.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.95/7.44  tff('#skF_2', type, '#skF_2': $i).
% 15.95/7.44  tff('#skF_3', type, '#skF_3': $i).
% 15.95/7.44  tff('#skF_1', type, '#skF_1': $i).
% 15.95/7.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.95/7.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.95/7.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.95/7.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.95/7.44  tff('#skF_4', type, '#skF_4': $i).
% 15.95/7.44  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.95/7.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.95/7.44  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.95/7.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.95/7.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.95/7.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.95/7.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.95/7.44  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.95/7.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.95/7.44  
% 15.95/7.48  tff(f_218, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 15.95/7.48  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 15.95/7.48  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.95/7.48  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.95/7.48  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.95/7.48  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.95/7.48  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 15.95/7.48  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_relat_1)).
% 15.95/7.48  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 15.95/7.48  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 15.95/7.48  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 15.95/7.48  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 15.95/7.48  tff(f_94, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 15.95/7.48  tff(f_176, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 15.95/7.48  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 15.95/7.48  tff(c_78, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_12, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.95/7.48  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.95/7.48  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_725, plain, (![C_327, A_328, B_329]: (v1_relat_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.95/7.48  tff(c_737, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_725])).
% 15.95/7.48  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.95/7.48  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.95/7.48  tff(c_781, plain, (![B_335, A_336]: (v4_relat_1(B_335, A_336) | ~r1_tarski(k1_relat_1(B_335), A_336) | ~v1_relat_1(B_335))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.95/7.48  tff(c_786, plain, (![B_335]: (v4_relat_1(B_335, k1_relat_1(B_335)) | ~v1_relat_1(B_335))), inference(resolution, [status(thm)], [c_10, c_781])).
% 15.95/7.48  tff(c_10801, plain, (![C_1406, A_1407, B_1408]: (v4_relat_1(C_1406, A_1407) | ~m1_subset_1(C_1406, k1_zfmisc_1(B_1408)) | ~v4_relat_1(B_1408, A_1407) | ~v1_relat_1(B_1408))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.95/7.48  tff(c_10805, plain, (![A_1407]: (v4_relat_1('#skF_6', A_1407) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_1407) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_10801])).
% 15.95/7.48  tff(c_10826, plain, (![A_1409]: (v4_relat_1('#skF_6', A_1409) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_1409))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10805])).
% 15.95/7.48  tff(c_10830, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_786, c_10826])).
% 15.95/7.48  tff(c_10833, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10830])).
% 15.95/7.48  tff(c_30, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 15.95/7.48  tff(c_10836, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10833, c_30])).
% 15.95/7.48  tff(c_10839, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_737, c_10836])).
% 15.95/7.48  tff(c_28, plain, (![C_21, A_19, B_20]: (k7_relat_1(k7_relat_1(C_21, A_19), B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.95/7.48  tff(c_10843, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10839, c_28])).
% 15.95/7.48  tff(c_10872, plain, (![B_1411]: (k7_relat_1('#skF_6', B_1411)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_1411))), inference(demodulation, [status(thm), theory('equality')], [c_737, c_10843])).
% 15.95/7.48  tff(c_10999, plain, (![B_1422]: (k7_relat_1('#skF_6', B_1422)=k1_xboole_0 | k3_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_1422)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_10872])).
% 15.95/7.48  tff(c_11004, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12, c_10999])).
% 15.95/7.48  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_66, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_10668, plain, (![A_1382, B_1383]: (r1_xboole_0(A_1382, B_1383) | ~r1_subset_1(A_1382, B_1383) | v1_xboole_0(B_1383) | v1_xboole_0(A_1382))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.48  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.95/7.48  tff(c_10790, plain, (![A_1404, B_1405]: (k3_xboole_0(A_1404, B_1405)=k1_xboole_0 | ~r1_subset_1(A_1404, B_1405) | v1_xboole_0(B_1405) | v1_xboole_0(A_1404))), inference(resolution, [status(thm)], [c_10668, c_2])).
% 15.95/7.48  tff(c_10796, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_10790])).
% 15.95/7.48  tff(c_10800, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_10796])).
% 15.95/7.48  tff(c_10704, plain, (![A_1390, B_1391, C_1392]: (k9_subset_1(A_1390, B_1391, C_1392)=k3_xboole_0(B_1391, C_1392) | ~m1_subset_1(C_1392, k1_zfmisc_1(A_1390)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.95/7.48  tff(c_10718, plain, (![B_1391]: (k9_subset_1('#skF_1', B_1391, '#skF_4')=k3_xboole_0(B_1391, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_10704])).
% 15.95/7.48  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_11047, plain, (![A_1425, B_1426, C_1427, D_1428]: (k2_partfun1(A_1425, B_1426, C_1427, D_1428)=k7_relat_1(C_1427, D_1428) | ~m1_subset_1(C_1427, k1_zfmisc_1(k2_zfmisc_1(A_1425, B_1426))) | ~v1_funct_1(C_1427))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.95/7.48  tff(c_11054, plain, (![D_1428]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1428)=k7_relat_1('#skF_5', D_1428) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_11047])).
% 15.95/7.48  tff(c_11077, plain, (![D_1430]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1430)=k7_relat_1('#skF_5', D_1430))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_11054])).
% 15.95/7.48  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_11052, plain, (![D_1428]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1428)=k7_relat_1('#skF_6', D_1428) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_11047])).
% 15.95/7.48  tff(c_11058, plain, (![D_1428]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1428)=k7_relat_1('#skF_6', D_1428))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_11052])).
% 15.95/7.48  tff(c_139, plain, (![C_237, A_238, B_239]: (v1_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.95/7.48  tff(c_152, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_139])).
% 15.95/7.48  tff(c_180, plain, (![B_247, A_248]: (v4_relat_1(B_247, A_248) | ~r1_tarski(k1_relat_1(B_247), A_248) | ~v1_relat_1(B_247))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.95/7.48  tff(c_189, plain, (![B_247]: (v4_relat_1(B_247, k1_relat_1(B_247)) | ~v1_relat_1(B_247))), inference(resolution, [status(thm)], [c_10, c_180])).
% 15.95/7.48  tff(c_332, plain, (![C_273, A_274, B_275]: (v4_relat_1(C_273, A_274) | ~m1_subset_1(C_273, k1_zfmisc_1(B_275)) | ~v4_relat_1(B_275, A_274) | ~v1_relat_1(B_275))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.95/7.48  tff(c_338, plain, (![A_274]: (v4_relat_1('#skF_5', A_274) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_274) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_60, c_332])).
% 15.95/7.48  tff(c_376, plain, (![A_277]: (v4_relat_1('#skF_5', A_277) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_277))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_338])).
% 15.95/7.48  tff(c_380, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_189, c_376])).
% 15.95/7.48  tff(c_383, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_380])).
% 15.95/7.48  tff(c_386, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_383, c_30])).
% 15.95/7.48  tff(c_389, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_386])).
% 15.95/7.48  tff(c_393, plain, (![B_20]: (k7_relat_1('#skF_5', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_389, c_28])).
% 15.95/7.48  tff(c_444, plain, (![B_285]: (k7_relat_1('#skF_5', B_285)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_285))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_393])).
% 15.95/7.48  tff(c_603, plain, (![B_314]: (k7_relat_1('#skF_5', B_314)=k1_xboole_0 | k3_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_314)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_444])).
% 15.95/7.48  tff(c_608, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12, c_603])).
% 15.95/7.48  tff(c_206, plain, (![A_251, B_252]: (r1_xboole_0(A_251, B_252) | ~r1_subset_1(A_251, B_252) | v1_xboole_0(B_252) | v1_xboole_0(A_251))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.48  tff(c_456, plain, (![A_288, B_289]: (k3_xboole_0(A_288, B_289)=k1_xboole_0 | ~r1_subset_1(A_288, B_289) | v1_xboole_0(B_289) | v1_xboole_0(A_288))), inference(resolution, [status(thm)], [c_206, c_2])).
% 15.95/7.48  tff(c_462, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_456])).
% 15.95/7.48  tff(c_466, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_462])).
% 15.95/7.48  tff(c_399, plain, (![A_278, B_279, C_280, D_281]: (k2_partfun1(A_278, B_279, C_280, D_281)=k7_relat_1(C_280, D_281) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))) | ~v1_funct_1(C_280))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.95/7.48  tff(c_406, plain, (![D_281]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_281)=k7_relat_1('#skF_5', D_281) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_399])).
% 15.95/7.48  tff(c_413, plain, (![D_281]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_281)=k7_relat_1('#skF_5', D_281))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_406])).
% 15.95/7.48  tff(c_404, plain, (![D_281]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_281)=k7_relat_1('#skF_6', D_281) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_399])).
% 15.95/7.48  tff(c_410, plain, (![D_281]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_281)=k7_relat_1('#skF_6', D_281))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_404])).
% 15.95/7.48  tff(c_221, plain, (![A_258, B_259, C_260]: (k9_subset_1(A_258, B_259, C_260)=k3_xboole_0(B_259, C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(A_258)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.95/7.48  tff(c_235, plain, (![B_259]: (k9_subset_1('#skF_1', B_259, '#skF_4')=k3_xboole_0(B_259, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_221])).
% 15.95/7.48  tff(c_52, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_96, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 15.95/7.48  tff(c_237, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_235, c_96])).
% 15.95/7.48  tff(c_443, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_410, c_237])).
% 15.95/7.48  tff(c_467, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_466, c_466, c_443])).
% 15.95/7.48  tff(c_621, plain, (k7_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_608, c_467])).
% 15.95/7.48  tff(c_151, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_139])).
% 15.95/7.48  tff(c_336, plain, (![A_274]: (v4_relat_1('#skF_6', A_274) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_274) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_332])).
% 15.95/7.48  tff(c_352, plain, (![A_276]: (v4_relat_1('#skF_6', A_276) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_276))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_336])).
% 15.95/7.48  tff(c_356, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_189, c_352])).
% 15.95/7.48  tff(c_359, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_356])).
% 15.95/7.48  tff(c_362, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_359, c_30])).
% 15.95/7.48  tff(c_365, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_151, c_362])).
% 15.95/7.48  tff(c_369, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_365, c_28])).
% 15.95/7.48  tff(c_432, plain, (![B_284]: (k7_relat_1('#skF_6', B_284)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_284))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_369])).
% 15.95/7.48  tff(c_693, plain, (![B_324]: (k7_relat_1('#skF_6', B_324)=k1_xboole_0 | k3_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_324)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_432])).
% 15.95/7.48  tff(c_697, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12, c_693])).
% 15.95/7.48  tff(c_701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_621, c_697])).
% 15.95/7.48  tff(c_703, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 15.95/7.48  tff(c_10720, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10718, c_10718, c_703])).
% 15.95/7.48  tff(c_10894, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10800, c_10800, c_10720])).
% 15.95/7.48  tff(c_11062, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11058, c_10894])).
% 15.95/7.48  tff(c_11063, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11004, c_11062])).
% 15.95/7.48  tff(c_11083, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11077, c_11063])).
% 15.95/7.48  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_76, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 15.95/7.48  tff(c_11122, plain, (![C_1434, A_1438, D_1436, E_1437, B_1435, F_1439]: (v1_funct_1(k1_tmap_1(A_1438, B_1435, C_1434, D_1436, E_1437, F_1439)) | ~m1_subset_1(F_1439, k1_zfmisc_1(k2_zfmisc_1(D_1436, B_1435))) | ~v1_funct_2(F_1439, D_1436, B_1435) | ~v1_funct_1(F_1439) | ~m1_subset_1(E_1437, k1_zfmisc_1(k2_zfmisc_1(C_1434, B_1435))) | ~v1_funct_2(E_1437, C_1434, B_1435) | ~v1_funct_1(E_1437) | ~m1_subset_1(D_1436, k1_zfmisc_1(A_1438)) | v1_xboole_0(D_1436) | ~m1_subset_1(C_1434, k1_zfmisc_1(A_1438)) | v1_xboole_0(C_1434) | v1_xboole_0(B_1435) | v1_xboole_0(A_1438))), inference(cnfTransformation, [status(thm)], [f_176])).
% 15.95/7.48  tff(c_11127, plain, (![A_1438, C_1434, E_1437]: (v1_funct_1(k1_tmap_1(A_1438, '#skF_2', C_1434, '#skF_4', E_1437, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1437, k1_zfmisc_1(k2_zfmisc_1(C_1434, '#skF_2'))) | ~v1_funct_2(E_1437, C_1434, '#skF_2') | ~v1_funct_1(E_1437) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1438)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1434, k1_zfmisc_1(A_1438)) | v1_xboole_0(C_1434) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1438))), inference(resolution, [status(thm)], [c_54, c_11122])).
% 15.95/7.48  tff(c_11133, plain, (![A_1438, C_1434, E_1437]: (v1_funct_1(k1_tmap_1(A_1438, '#skF_2', C_1434, '#skF_4', E_1437, '#skF_6')) | ~m1_subset_1(E_1437, k1_zfmisc_1(k2_zfmisc_1(C_1434, '#skF_2'))) | ~v1_funct_2(E_1437, C_1434, '#skF_2') | ~v1_funct_1(E_1437) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1438)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1434, k1_zfmisc_1(A_1438)) | v1_xboole_0(C_1434) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1438))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11127])).
% 15.95/7.48  tff(c_11701, plain, (![A_1503, C_1504, E_1505]: (v1_funct_1(k1_tmap_1(A_1503, '#skF_2', C_1504, '#skF_4', E_1505, '#skF_6')) | ~m1_subset_1(E_1505, k1_zfmisc_1(k2_zfmisc_1(C_1504, '#skF_2'))) | ~v1_funct_2(E_1505, C_1504, '#skF_2') | ~v1_funct_1(E_1505) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1503)) | ~m1_subset_1(C_1504, k1_zfmisc_1(A_1503)) | v1_xboole_0(C_1504) | v1_xboole_0(A_1503))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_11133])).
% 15.95/7.48  tff(c_11711, plain, (![A_1503]: (v1_funct_1(k1_tmap_1(A_1503, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1503)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1503)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1503))), inference(resolution, [status(thm)], [c_60, c_11701])).
% 15.95/7.48  tff(c_11722, plain, (![A_1503]: (v1_funct_1(k1_tmap_1(A_1503, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1503)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1503)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1503))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_11711])).
% 15.95/7.48  tff(c_11836, plain, (![A_1518]: (v1_funct_1(k1_tmap_1(A_1518, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1518)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1518)) | v1_xboole_0(A_1518))), inference(negUnitSimplification, [status(thm)], [c_74, c_11722])).
% 15.95/7.48  tff(c_11843, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_11836])).
% 15.95/7.48  tff(c_11847, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_11843])).
% 15.95/7.48  tff(c_11848, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_11847])).
% 15.95/7.48  tff(c_11061, plain, (![D_1428]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1428)=k7_relat_1('#skF_5', D_1428))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_11054])).
% 15.95/7.48  tff(c_48, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_176])).
% 15.95/7.48  tff(c_46, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_176])).
% 15.95/7.48  tff(c_11630, plain, (![C_1499, D_1500, B_1497, A_1495, F_1498, E_1496]: (k2_partfun1(k4_subset_1(A_1495, C_1499, D_1500), B_1497, k1_tmap_1(A_1495, B_1497, C_1499, D_1500, E_1496, F_1498), C_1499)=E_1496 | ~m1_subset_1(k1_tmap_1(A_1495, B_1497, C_1499, D_1500, E_1496, F_1498), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1495, C_1499, D_1500), B_1497))) | ~v1_funct_2(k1_tmap_1(A_1495, B_1497, C_1499, D_1500, E_1496, F_1498), k4_subset_1(A_1495, C_1499, D_1500), B_1497) | ~v1_funct_1(k1_tmap_1(A_1495, B_1497, C_1499, D_1500, E_1496, F_1498)) | k2_partfun1(D_1500, B_1497, F_1498, k9_subset_1(A_1495, C_1499, D_1500))!=k2_partfun1(C_1499, B_1497, E_1496, k9_subset_1(A_1495, C_1499, D_1500)) | ~m1_subset_1(F_1498, k1_zfmisc_1(k2_zfmisc_1(D_1500, B_1497))) | ~v1_funct_2(F_1498, D_1500, B_1497) | ~v1_funct_1(F_1498) | ~m1_subset_1(E_1496, k1_zfmisc_1(k2_zfmisc_1(C_1499, B_1497))) | ~v1_funct_2(E_1496, C_1499, B_1497) | ~v1_funct_1(E_1496) | ~m1_subset_1(D_1500, k1_zfmisc_1(A_1495)) | v1_xboole_0(D_1500) | ~m1_subset_1(C_1499, k1_zfmisc_1(A_1495)) | v1_xboole_0(C_1499) | v1_xboole_0(B_1497) | v1_xboole_0(A_1495))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.95/7.48  tff(c_13045, plain, (![B_1651, A_1654, D_1652, C_1650, E_1653, F_1655]: (k2_partfun1(k4_subset_1(A_1654, C_1650, D_1652), B_1651, k1_tmap_1(A_1654, B_1651, C_1650, D_1652, E_1653, F_1655), C_1650)=E_1653 | ~v1_funct_2(k1_tmap_1(A_1654, B_1651, C_1650, D_1652, E_1653, F_1655), k4_subset_1(A_1654, C_1650, D_1652), B_1651) | ~v1_funct_1(k1_tmap_1(A_1654, B_1651, C_1650, D_1652, E_1653, F_1655)) | k2_partfun1(D_1652, B_1651, F_1655, k9_subset_1(A_1654, C_1650, D_1652))!=k2_partfun1(C_1650, B_1651, E_1653, k9_subset_1(A_1654, C_1650, D_1652)) | ~m1_subset_1(F_1655, k1_zfmisc_1(k2_zfmisc_1(D_1652, B_1651))) | ~v1_funct_2(F_1655, D_1652, B_1651) | ~v1_funct_1(F_1655) | ~m1_subset_1(E_1653, k1_zfmisc_1(k2_zfmisc_1(C_1650, B_1651))) | ~v1_funct_2(E_1653, C_1650, B_1651) | ~v1_funct_1(E_1653) | ~m1_subset_1(D_1652, k1_zfmisc_1(A_1654)) | v1_xboole_0(D_1652) | ~m1_subset_1(C_1650, k1_zfmisc_1(A_1654)) | v1_xboole_0(C_1650) | v1_xboole_0(B_1651) | v1_xboole_0(A_1654))), inference(resolution, [status(thm)], [c_46, c_11630])).
% 15.95/7.48  tff(c_15437, plain, (![A_1906, B_1903, F_1907, C_1902, D_1904, E_1905]: (k2_partfun1(k4_subset_1(A_1906, C_1902, D_1904), B_1903, k1_tmap_1(A_1906, B_1903, C_1902, D_1904, E_1905, F_1907), C_1902)=E_1905 | ~v1_funct_1(k1_tmap_1(A_1906, B_1903, C_1902, D_1904, E_1905, F_1907)) | k2_partfun1(D_1904, B_1903, F_1907, k9_subset_1(A_1906, C_1902, D_1904))!=k2_partfun1(C_1902, B_1903, E_1905, k9_subset_1(A_1906, C_1902, D_1904)) | ~m1_subset_1(F_1907, k1_zfmisc_1(k2_zfmisc_1(D_1904, B_1903))) | ~v1_funct_2(F_1907, D_1904, B_1903) | ~v1_funct_1(F_1907) | ~m1_subset_1(E_1905, k1_zfmisc_1(k2_zfmisc_1(C_1902, B_1903))) | ~v1_funct_2(E_1905, C_1902, B_1903) | ~v1_funct_1(E_1905) | ~m1_subset_1(D_1904, k1_zfmisc_1(A_1906)) | v1_xboole_0(D_1904) | ~m1_subset_1(C_1902, k1_zfmisc_1(A_1906)) | v1_xboole_0(C_1902) | v1_xboole_0(B_1903) | v1_xboole_0(A_1906))), inference(resolution, [status(thm)], [c_48, c_13045])).
% 15.95/7.48  tff(c_15444, plain, (![A_1906, C_1902, E_1905]: (k2_partfun1(k4_subset_1(A_1906, C_1902, '#skF_4'), '#skF_2', k1_tmap_1(A_1906, '#skF_2', C_1902, '#skF_4', E_1905, '#skF_6'), C_1902)=E_1905 | ~v1_funct_1(k1_tmap_1(A_1906, '#skF_2', C_1902, '#skF_4', E_1905, '#skF_6')) | k2_partfun1(C_1902, '#skF_2', E_1905, k9_subset_1(A_1906, C_1902, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1906, C_1902, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1905, k1_zfmisc_1(k2_zfmisc_1(C_1902, '#skF_2'))) | ~v1_funct_2(E_1905, C_1902, '#skF_2') | ~v1_funct_1(E_1905) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1906)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1902, k1_zfmisc_1(A_1906)) | v1_xboole_0(C_1902) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1906))), inference(resolution, [status(thm)], [c_54, c_15437])).
% 15.95/7.48  tff(c_15451, plain, (![A_1906, C_1902, E_1905]: (k2_partfun1(k4_subset_1(A_1906, C_1902, '#skF_4'), '#skF_2', k1_tmap_1(A_1906, '#skF_2', C_1902, '#skF_4', E_1905, '#skF_6'), C_1902)=E_1905 | ~v1_funct_1(k1_tmap_1(A_1906, '#skF_2', C_1902, '#skF_4', E_1905, '#skF_6')) | k2_partfun1(C_1902, '#skF_2', E_1905, k9_subset_1(A_1906, C_1902, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1906, C_1902, '#skF_4')) | ~m1_subset_1(E_1905, k1_zfmisc_1(k2_zfmisc_1(C_1902, '#skF_2'))) | ~v1_funct_2(E_1905, C_1902, '#skF_2') | ~v1_funct_1(E_1905) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1906)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1902, k1_zfmisc_1(A_1906)) | v1_xboole_0(C_1902) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1906))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_11058, c_15444])).
% 15.95/7.48  tff(c_18150, plain, (![A_2182, C_2183, E_2184]: (k2_partfun1(k4_subset_1(A_2182, C_2183, '#skF_4'), '#skF_2', k1_tmap_1(A_2182, '#skF_2', C_2183, '#skF_4', E_2184, '#skF_6'), C_2183)=E_2184 | ~v1_funct_1(k1_tmap_1(A_2182, '#skF_2', C_2183, '#skF_4', E_2184, '#skF_6')) | k2_partfun1(C_2183, '#skF_2', E_2184, k9_subset_1(A_2182, C_2183, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2182, C_2183, '#skF_4')) | ~m1_subset_1(E_2184, k1_zfmisc_1(k2_zfmisc_1(C_2183, '#skF_2'))) | ~v1_funct_2(E_2184, C_2183, '#skF_2') | ~v1_funct_1(E_2184) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2182)) | ~m1_subset_1(C_2183, k1_zfmisc_1(A_2182)) | v1_xboole_0(C_2183) | v1_xboole_0(A_2182))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_15451])).
% 15.95/7.48  tff(c_18160, plain, (![A_2182]: (k2_partfun1(k4_subset_1(A_2182, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2182, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2182, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2182, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2182, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2182)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2182)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2182))), inference(resolution, [status(thm)], [c_60, c_18150])).
% 15.95/7.48  tff(c_18171, plain, (![A_2182]: (k2_partfun1(k4_subset_1(A_2182, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2182, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2182, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2182, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2182, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2182)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2182)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2182))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_11061, c_18160])).
% 15.95/7.48  tff(c_20174, plain, (![A_2371]: (k2_partfun1(k4_subset_1(A_2371, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2371, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2371, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2371, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2371, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2371)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2371)) | v1_xboole_0(A_2371))), inference(negUnitSimplification, [status(thm)], [c_74, c_18171])).
% 15.95/7.48  tff(c_738, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_725])).
% 15.95/7.48  tff(c_956, plain, (![C_369, A_370, B_371]: (v4_relat_1(C_369, A_370) | ~m1_subset_1(C_369, k1_zfmisc_1(B_371)) | ~v4_relat_1(B_371, A_370) | ~v1_relat_1(B_371))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.95/7.48  tff(c_962, plain, (![A_370]: (v4_relat_1('#skF_5', A_370) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_370) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_60, c_956])).
% 15.95/7.48  tff(c_1004, plain, (![A_373]: (v4_relat_1('#skF_5', A_373) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_373))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_962])).
% 15.95/7.48  tff(c_1008, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_786, c_1004])).
% 15.95/7.48  tff(c_1011, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1008])).
% 15.95/7.48  tff(c_1014, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1011, c_30])).
% 15.95/7.48  tff(c_1017, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_738, c_1014])).
% 15.95/7.48  tff(c_1021, plain, (![B_20]: (k7_relat_1('#skF_5', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1017, c_28])).
% 15.95/7.48  tff(c_1038, plain, (![B_375]: (k7_relat_1('#skF_5', B_375)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_375))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_1021])).
% 15.95/7.48  tff(c_1254, plain, (![B_398]: (k7_relat_1('#skF_5', B_398)=k1_xboole_0 | k3_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_398)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1038])).
% 15.95/7.48  tff(c_1259, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12, c_1254])).
% 15.95/7.48  tff(c_1136, plain, (![A_384, B_385, C_386, D_387]: (k2_partfun1(A_384, B_385, C_386, D_387)=k7_relat_1(C_386, D_387) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))) | ~v1_funct_1(C_386))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.95/7.48  tff(c_1141, plain, (![D_387]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_387)=k7_relat_1('#skF_6', D_387) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_1136])).
% 15.95/7.48  tff(c_1147, plain, (![D_387]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_387)=k7_relat_1('#skF_6', D_387))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1141])).
% 15.95/7.48  tff(c_823, plain, (![A_345, B_346]: (r1_xboole_0(A_345, B_346) | ~r1_subset_1(A_345, B_346) | v1_xboole_0(B_346) | v1_xboole_0(A_345))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.95/7.48  tff(c_945, plain, (![A_367, B_368]: (k3_xboole_0(A_367, B_368)=k1_xboole_0 | ~r1_subset_1(A_367, B_368) | v1_xboole_0(B_368) | v1_xboole_0(A_367))), inference(resolution, [status(thm)], [c_823, c_2])).
% 15.95/7.48  tff(c_951, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_945])).
% 15.95/7.48  tff(c_955, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_951])).
% 15.95/7.48  tff(c_859, plain, (![A_353, B_354, C_355]: (k9_subset_1(A_353, B_354, C_355)=k3_xboole_0(B_354, C_355) | ~m1_subset_1(C_355, k1_zfmisc_1(A_353)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.95/7.48  tff(c_873, plain, (![B_354]: (k9_subset_1('#skF_1', B_354, '#skF_4')=k3_xboole_0(B_354, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_859])).
% 15.95/7.48  tff(c_875, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_873, c_873, c_703])).
% 15.95/7.48  tff(c_1049, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_955, c_955, c_875])).
% 15.95/7.48  tff(c_1151, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_1049])).
% 15.95/7.48  tff(c_1143, plain, (![D_387]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_387)=k7_relat_1('#skF_5', D_387) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_1136])).
% 15.95/7.48  tff(c_1150, plain, (![D_387]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_387)=k7_relat_1('#skF_5', D_387))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1143])).
% 15.95/7.48  tff(c_1173, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1151, c_1150])).
% 15.95/7.48  tff(c_1277, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1259, c_1173])).
% 15.95/7.48  tff(c_1236, plain, (![B_393, A_396, F_397, D_394, C_392, E_395]: (v1_funct_1(k1_tmap_1(A_396, B_393, C_392, D_394, E_395, F_397)) | ~m1_subset_1(F_397, k1_zfmisc_1(k2_zfmisc_1(D_394, B_393))) | ~v1_funct_2(F_397, D_394, B_393) | ~v1_funct_1(F_397) | ~m1_subset_1(E_395, k1_zfmisc_1(k2_zfmisc_1(C_392, B_393))) | ~v1_funct_2(E_395, C_392, B_393) | ~v1_funct_1(E_395) | ~m1_subset_1(D_394, k1_zfmisc_1(A_396)) | v1_xboole_0(D_394) | ~m1_subset_1(C_392, k1_zfmisc_1(A_396)) | v1_xboole_0(C_392) | v1_xboole_0(B_393) | v1_xboole_0(A_396))), inference(cnfTransformation, [status(thm)], [f_176])).
% 15.95/7.48  tff(c_1241, plain, (![A_396, C_392, E_395]: (v1_funct_1(k1_tmap_1(A_396, '#skF_2', C_392, '#skF_4', E_395, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_395, k1_zfmisc_1(k2_zfmisc_1(C_392, '#skF_2'))) | ~v1_funct_2(E_395, C_392, '#skF_2') | ~v1_funct_1(E_395) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_396)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_392, k1_zfmisc_1(A_396)) | v1_xboole_0(C_392) | v1_xboole_0('#skF_2') | v1_xboole_0(A_396))), inference(resolution, [status(thm)], [c_54, c_1236])).
% 15.95/7.48  tff(c_1247, plain, (![A_396, C_392, E_395]: (v1_funct_1(k1_tmap_1(A_396, '#skF_2', C_392, '#skF_4', E_395, '#skF_6')) | ~m1_subset_1(E_395, k1_zfmisc_1(k2_zfmisc_1(C_392, '#skF_2'))) | ~v1_funct_2(E_395, C_392, '#skF_2') | ~v1_funct_1(E_395) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_396)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_392, k1_zfmisc_1(A_396)) | v1_xboole_0(C_392) | v1_xboole_0('#skF_2') | v1_xboole_0(A_396))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1241])).
% 15.95/7.48  tff(c_1260, plain, (![A_399, C_400, E_401]: (v1_funct_1(k1_tmap_1(A_399, '#skF_2', C_400, '#skF_4', E_401, '#skF_6')) | ~m1_subset_1(E_401, k1_zfmisc_1(k2_zfmisc_1(C_400, '#skF_2'))) | ~v1_funct_2(E_401, C_400, '#skF_2') | ~v1_funct_1(E_401) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_399)) | ~m1_subset_1(C_400, k1_zfmisc_1(A_399)) | v1_xboole_0(C_400) | v1_xboole_0(A_399))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_1247])).
% 15.95/7.48  tff(c_1267, plain, (![A_399]: (v1_funct_1(k1_tmap_1(A_399, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_399)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_399)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_399))), inference(resolution, [status(thm)], [c_60, c_1260])).
% 15.95/7.48  tff(c_1275, plain, (![A_399]: (v1_funct_1(k1_tmap_1(A_399, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_399)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_399)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_399))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1267])).
% 15.95/7.48  tff(c_1449, plain, (![A_427]: (v1_funct_1(k1_tmap_1(A_427, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_427)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_427)) | v1_xboole_0(A_427))), inference(negUnitSimplification, [status(thm)], [c_74, c_1275])).
% 15.95/7.48  tff(c_1456, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_1449])).
% 15.95/7.48  tff(c_1460, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1456])).
% 15.95/7.48  tff(c_1461, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_1460])).
% 15.95/7.48  tff(c_1671, plain, (![B_435, A_433, C_437, E_434, F_436, D_438]: (k2_partfun1(k4_subset_1(A_433, C_437, D_438), B_435, k1_tmap_1(A_433, B_435, C_437, D_438, E_434, F_436), D_438)=F_436 | ~m1_subset_1(k1_tmap_1(A_433, B_435, C_437, D_438, E_434, F_436), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_433, C_437, D_438), B_435))) | ~v1_funct_2(k1_tmap_1(A_433, B_435, C_437, D_438, E_434, F_436), k4_subset_1(A_433, C_437, D_438), B_435) | ~v1_funct_1(k1_tmap_1(A_433, B_435, C_437, D_438, E_434, F_436)) | k2_partfun1(D_438, B_435, F_436, k9_subset_1(A_433, C_437, D_438))!=k2_partfun1(C_437, B_435, E_434, k9_subset_1(A_433, C_437, D_438)) | ~m1_subset_1(F_436, k1_zfmisc_1(k2_zfmisc_1(D_438, B_435))) | ~v1_funct_2(F_436, D_438, B_435) | ~v1_funct_1(F_436) | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(C_437, B_435))) | ~v1_funct_2(E_434, C_437, B_435) | ~v1_funct_1(E_434) | ~m1_subset_1(D_438, k1_zfmisc_1(A_433)) | v1_xboole_0(D_438) | ~m1_subset_1(C_437, k1_zfmisc_1(A_433)) | v1_xboole_0(C_437) | v1_xboole_0(B_435) | v1_xboole_0(A_433))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.95/7.48  tff(c_2907, plain, (![F_593, E_591, D_590, A_592, C_588, B_589]: (k2_partfun1(k4_subset_1(A_592, C_588, D_590), B_589, k1_tmap_1(A_592, B_589, C_588, D_590, E_591, F_593), D_590)=F_593 | ~v1_funct_2(k1_tmap_1(A_592, B_589, C_588, D_590, E_591, F_593), k4_subset_1(A_592, C_588, D_590), B_589) | ~v1_funct_1(k1_tmap_1(A_592, B_589, C_588, D_590, E_591, F_593)) | k2_partfun1(D_590, B_589, F_593, k9_subset_1(A_592, C_588, D_590))!=k2_partfun1(C_588, B_589, E_591, k9_subset_1(A_592, C_588, D_590)) | ~m1_subset_1(F_593, k1_zfmisc_1(k2_zfmisc_1(D_590, B_589))) | ~v1_funct_2(F_593, D_590, B_589) | ~v1_funct_1(F_593) | ~m1_subset_1(E_591, k1_zfmisc_1(k2_zfmisc_1(C_588, B_589))) | ~v1_funct_2(E_591, C_588, B_589) | ~v1_funct_1(E_591) | ~m1_subset_1(D_590, k1_zfmisc_1(A_592)) | v1_xboole_0(D_590) | ~m1_subset_1(C_588, k1_zfmisc_1(A_592)) | v1_xboole_0(C_588) | v1_xboole_0(B_589) | v1_xboole_0(A_592))), inference(resolution, [status(thm)], [c_46, c_1671])).
% 15.95/7.48  tff(c_5574, plain, (![A_868, F_869, E_867, C_864, B_865, D_866]: (k2_partfun1(k4_subset_1(A_868, C_864, D_866), B_865, k1_tmap_1(A_868, B_865, C_864, D_866, E_867, F_869), D_866)=F_869 | ~v1_funct_1(k1_tmap_1(A_868, B_865, C_864, D_866, E_867, F_869)) | k2_partfun1(D_866, B_865, F_869, k9_subset_1(A_868, C_864, D_866))!=k2_partfun1(C_864, B_865, E_867, k9_subset_1(A_868, C_864, D_866)) | ~m1_subset_1(F_869, k1_zfmisc_1(k2_zfmisc_1(D_866, B_865))) | ~v1_funct_2(F_869, D_866, B_865) | ~v1_funct_1(F_869) | ~m1_subset_1(E_867, k1_zfmisc_1(k2_zfmisc_1(C_864, B_865))) | ~v1_funct_2(E_867, C_864, B_865) | ~v1_funct_1(E_867) | ~m1_subset_1(D_866, k1_zfmisc_1(A_868)) | v1_xboole_0(D_866) | ~m1_subset_1(C_864, k1_zfmisc_1(A_868)) | v1_xboole_0(C_864) | v1_xboole_0(B_865) | v1_xboole_0(A_868))), inference(resolution, [status(thm)], [c_48, c_2907])).
% 15.95/7.48  tff(c_5581, plain, (![A_868, C_864, E_867]: (k2_partfun1(k4_subset_1(A_868, C_864, '#skF_4'), '#skF_2', k1_tmap_1(A_868, '#skF_2', C_864, '#skF_4', E_867, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_868, '#skF_2', C_864, '#skF_4', E_867, '#skF_6')) | k2_partfun1(C_864, '#skF_2', E_867, k9_subset_1(A_868, C_864, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_868, C_864, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_867, k1_zfmisc_1(k2_zfmisc_1(C_864, '#skF_2'))) | ~v1_funct_2(E_867, C_864, '#skF_2') | ~v1_funct_1(E_867) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_868)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_864, k1_zfmisc_1(A_868)) | v1_xboole_0(C_864) | v1_xboole_0('#skF_2') | v1_xboole_0(A_868))), inference(resolution, [status(thm)], [c_54, c_5574])).
% 15.95/7.48  tff(c_5588, plain, (![A_868, C_864, E_867]: (k2_partfun1(k4_subset_1(A_868, C_864, '#skF_4'), '#skF_2', k1_tmap_1(A_868, '#skF_2', C_864, '#skF_4', E_867, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_868, '#skF_2', C_864, '#skF_4', E_867, '#skF_6')) | k2_partfun1(C_864, '#skF_2', E_867, k9_subset_1(A_868, C_864, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_868, C_864, '#skF_4')) | ~m1_subset_1(E_867, k1_zfmisc_1(k2_zfmisc_1(C_864, '#skF_2'))) | ~v1_funct_2(E_867, C_864, '#skF_2') | ~v1_funct_1(E_867) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_868)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_864, k1_zfmisc_1(A_868)) | v1_xboole_0(C_864) | v1_xboole_0('#skF_2') | v1_xboole_0(A_868))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1147, c_5581])).
% 15.95/7.48  tff(c_8217, plain, (![A_1125, C_1126, E_1127]: (k2_partfun1(k4_subset_1(A_1125, C_1126, '#skF_4'), '#skF_2', k1_tmap_1(A_1125, '#skF_2', C_1126, '#skF_4', E_1127, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1125, '#skF_2', C_1126, '#skF_4', E_1127, '#skF_6')) | k2_partfun1(C_1126, '#skF_2', E_1127, k9_subset_1(A_1125, C_1126, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1125, C_1126, '#skF_4')) | ~m1_subset_1(E_1127, k1_zfmisc_1(k2_zfmisc_1(C_1126, '#skF_2'))) | ~v1_funct_2(E_1127, C_1126, '#skF_2') | ~v1_funct_1(E_1127) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1125)) | ~m1_subset_1(C_1126, k1_zfmisc_1(A_1125)) | v1_xboole_0(C_1126) | v1_xboole_0(A_1125))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_5588])).
% 15.95/7.48  tff(c_8227, plain, (![A_1125]: (k2_partfun1(k4_subset_1(A_1125, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1125, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1125, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1125, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1125, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1125)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1125)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1125))), inference(resolution, [status(thm)], [c_60, c_8217])).
% 15.95/7.48  tff(c_8238, plain, (![A_1125]: (k2_partfun1(k4_subset_1(A_1125, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1125, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1125, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1125, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1125, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1125)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1125)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1125))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1150, c_8227])).
% 15.95/7.48  tff(c_10598, plain, (![A_1379]: (k2_partfun1(k4_subset_1(A_1379, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1379, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1379, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1379, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1379, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1379)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1379)) | v1_xboole_0(A_1379))), inference(negUnitSimplification, [status(thm)], [c_74, c_8238])).
% 15.95/7.48  tff(c_702, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 15.95/7.48  tff(c_816, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_702])).
% 15.95/7.48  tff(c_10621, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10598, c_816])).
% 15.95/7.48  tff(c_10657, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1277, c_955, c_873, c_1259, c_955, c_873, c_1461, c_10621])).
% 15.95/7.48  tff(c_10659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_10657])).
% 15.95/7.48  tff(c_10660, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_702])).
% 15.95/7.48  tff(c_20197, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20174, c_10660])).
% 15.95/7.48  tff(c_20233, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_11004, c_10800, c_10718, c_11083, c_10800, c_10718, c_11848, c_20197])).
% 15.95/7.48  tff(c_20235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_20233])).
% 15.95/7.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/7.48  
% 15.95/7.48  Inference rules
% 15.95/7.48  ----------------------
% 15.95/7.48  #Ref     : 0
% 15.95/7.48  #Sup     : 4379
% 15.95/7.48  #Fact    : 0
% 15.95/7.48  #Define  : 0
% 15.95/7.48  #Split   : 138
% 15.95/7.48  #Chain   : 0
% 15.95/7.48  #Close   : 0
% 15.95/7.48  
% 15.95/7.48  Ordering : KBO
% 15.95/7.48  
% 15.95/7.48  Simplification rules
% 15.95/7.48  ----------------------
% 15.95/7.48  #Subsume      : 1700
% 15.95/7.48  #Demod        : 3379
% 15.95/7.48  #Tautology    : 871
% 15.95/7.48  #SimpNegUnit  : 667
% 15.95/7.48  #BackRed      : 10
% 15.95/7.48  
% 15.95/7.48  #Partial instantiations: 0
% 15.95/7.48  #Strategies tried      : 1
% 15.95/7.48  
% 15.95/7.48  Timing (in seconds)
% 15.95/7.48  ----------------------
% 15.95/7.48  Preprocessing        : 0.41
% 15.95/7.48  Parsing              : 0.20
% 15.95/7.48  CNF conversion       : 0.06
% 15.95/7.48  Main loop            : 6.26
% 15.95/7.48  Inferencing          : 1.60
% 15.95/7.48  Reduction            : 2.13
% 15.95/7.48  Demodulation         : 1.50
% 15.95/7.48  BG Simplification    : 0.12
% 15.95/7.48  Subsumption          : 2.10
% 15.95/7.48  Abstraction          : 0.20
% 15.95/7.48  MUC search           : 0.00
% 15.95/7.48  Cooper               : 0.00
% 15.95/7.48  Total                : 6.74
% 15.95/7.48  Index Insertion      : 0.00
% 15.95/7.48  Index Deletion       : 0.00
% 15.95/7.48  Index Matching       : 0.00
% 15.95/7.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
