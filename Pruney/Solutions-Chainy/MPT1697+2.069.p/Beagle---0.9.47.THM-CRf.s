%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:20 EST 2020

% Result     : Theorem 40.79s
% Output     : CNFRefutation 41.06s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 579 expanded)
%              Number of leaves         :   43 ( 225 expanded)
%              Depth                    :   12
%              Number of atoms          :  703 (2932 expanded)
%              Number of equality atoms :  125 ( 512 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_84,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

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
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_645,plain,(
    ! [C_306,A_307,B_308] :
      ( v1_relat_1(C_306)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_307,B_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_658,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_645])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_689,plain,(
    ! [B_314,A_315] :
      ( v4_relat_1(B_314,A_315)
      | ~ r1_tarski(k1_relat_1(B_314),A_315)
      | ~ v1_relat_1(B_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_698,plain,(
    ! [B_314] :
      ( v4_relat_1(B_314,k1_relat_1(B_314))
      | ~ v1_relat_1(B_314) ) ),
    inference(resolution,[status(thm)],[c_10,c_689])).

tff(c_14215,plain,(
    ! [C_1616,A_1617,B_1618] :
      ( v4_relat_1(C_1616,A_1617)
      | ~ m1_subset_1(C_1616,k1_zfmisc_1(B_1618))
      | ~ v4_relat_1(B_1618,A_1617)
      | ~ v1_relat_1(B_1618) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14221,plain,(
    ! [A_1617] :
      ( v4_relat_1('#skF_5',A_1617)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_1617)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_60,c_14215])).

tff(c_14259,plain,(
    ! [A_1620] :
      ( v4_relat_1('#skF_5',A_1620)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_1620) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14221])).

tff(c_14263,plain,
    ( v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_698,c_14259])).

tff(c_14266,plain,(
    v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14263])).

tff(c_30,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14269,plain,
    ( k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14266,c_30])).

tff(c_14272,plain,(
    k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_14269])).

tff(c_28,plain,(
    ! [C_21,A_19,B_20] :
      ( k7_relat_1(k7_relat_1(C_21,A_19),B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14276,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_5',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14272,c_28])).

tff(c_14374,plain,(
    ! [B_1624] :
      ( k7_relat_1('#skF_5',B_1624) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_1624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_14276])).

tff(c_14389,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_14374])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_657,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_645])).

tff(c_14219,plain,(
    ! [A_1617] :
      ( v4_relat_1('#skF_6',A_1617)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_1617)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_14215])).

tff(c_14235,plain,(
    ! [A_1619] :
      ( v4_relat_1('#skF_6',A_1619)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_1619) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14219])).

tff(c_14239,plain,
    ( v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_698,c_14235])).

tff(c_14242,plain,(
    v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14239])).

tff(c_14245,plain,
    ( k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_14242,c_30])).

tff(c_14248,plain,(
    k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_14245])).

tff(c_14252,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14248,c_28])).

tff(c_14286,plain,(
    ! [B_1621] :
      ( k7_relat_1('#skF_6',B_1621) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_1621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_14252])).

tff(c_14301,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_14286])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_14078,plain,(
    ! [A_1592,B_1593] :
      ( r1_xboole_0(A_1592,B_1593)
      | ~ r1_subset_1(A_1592,B_1593)
      | v1_xboole_0(B_1593)
      | v1_xboole_0(A_1592) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14199,plain,(
    ! [A_1612,B_1613] :
      ( k3_xboole_0(A_1612,B_1613) = k1_xboole_0
      | ~ r1_subset_1(A_1612,B_1613)
      | v1_xboole_0(B_1613)
      | v1_xboole_0(A_1612) ) ),
    inference(resolution,[status(thm)],[c_14078,c_2])).

tff(c_14202,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_14199])).

tff(c_14205,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_14202])).

tff(c_14114,plain,(
    ! [A_1600,B_1601,C_1602] :
      ( k9_subset_1(A_1600,B_1601,C_1602) = k3_xboole_0(B_1601,C_1602)
      | ~ m1_subset_1(C_1602,k1_zfmisc_1(A_1600)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14128,plain,(
    ! [B_1601] : k9_subset_1('#skF_1',B_1601,'#skF_4') = k3_xboole_0(B_1601,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_14114])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_14659,plain,(
    ! [A_1653,B_1650,F_1654,E_1652,D_1651,C_1649] :
      ( v1_funct_1(k1_tmap_1(A_1653,B_1650,C_1649,D_1651,E_1652,F_1654))
      | ~ m1_subset_1(F_1654,k1_zfmisc_1(k2_zfmisc_1(D_1651,B_1650)))
      | ~ v1_funct_2(F_1654,D_1651,B_1650)
      | ~ v1_funct_1(F_1654)
      | ~ m1_subset_1(E_1652,k1_zfmisc_1(k2_zfmisc_1(C_1649,B_1650)))
      | ~ v1_funct_2(E_1652,C_1649,B_1650)
      | ~ v1_funct_1(E_1652)
      | ~ m1_subset_1(D_1651,k1_zfmisc_1(A_1653))
      | v1_xboole_0(D_1651)
      | ~ m1_subset_1(C_1649,k1_zfmisc_1(A_1653))
      | v1_xboole_0(C_1649)
      | v1_xboole_0(B_1650)
      | v1_xboole_0(A_1653) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_14664,plain,(
    ! [A_1653,C_1649,E_1652] :
      ( v1_funct_1(k1_tmap_1(A_1653,'#skF_2',C_1649,'#skF_4',E_1652,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1652,k1_zfmisc_1(k2_zfmisc_1(C_1649,'#skF_2')))
      | ~ v1_funct_2(E_1652,C_1649,'#skF_2')
      | ~ v1_funct_1(E_1652)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1653))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1649,k1_zfmisc_1(A_1653))
      | v1_xboole_0(C_1649)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1653) ) ),
    inference(resolution,[status(thm)],[c_54,c_14659])).

tff(c_14670,plain,(
    ! [A_1653,C_1649,E_1652] :
      ( v1_funct_1(k1_tmap_1(A_1653,'#skF_2',C_1649,'#skF_4',E_1652,'#skF_6'))
      | ~ m1_subset_1(E_1652,k1_zfmisc_1(k2_zfmisc_1(C_1649,'#skF_2')))
      | ~ v1_funct_2(E_1652,C_1649,'#skF_2')
      | ~ v1_funct_1(E_1652)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1653))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1649,k1_zfmisc_1(A_1653))
      | v1_xboole_0(C_1649)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1653) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_14664])).

tff(c_15068,plain,(
    ! [A_1699,C_1700,E_1701] :
      ( v1_funct_1(k1_tmap_1(A_1699,'#skF_2',C_1700,'#skF_4',E_1701,'#skF_6'))
      | ~ m1_subset_1(E_1701,k1_zfmisc_1(k2_zfmisc_1(C_1700,'#skF_2')))
      | ~ v1_funct_2(E_1701,C_1700,'#skF_2')
      | ~ v1_funct_1(E_1701)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1699))
      | ~ m1_subset_1(C_1700,k1_zfmisc_1(A_1699))
      | v1_xboole_0(C_1700)
      | v1_xboole_0(A_1699) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_14670])).

tff(c_15078,plain,(
    ! [A_1699] :
      ( v1_funct_1(k1_tmap_1(A_1699,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1699))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1699))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1699) ) ),
    inference(resolution,[status(thm)],[c_60,c_15068])).

tff(c_15089,plain,(
    ! [A_1699] :
      ( v1_funct_1(k1_tmap_1(A_1699,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1699))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1699))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1699) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_15078])).

tff(c_15174,plain,(
    ! [A_1721] :
      ( v1_funct_1(k1_tmap_1(A_1721,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1721))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1721))
      | v1_xboole_0(A_1721) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_15089])).

tff(c_15181,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_15174])).

tff(c_15185,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_15181])).

tff(c_15186,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_15185])).

tff(c_14495,plain,(
    ! [A_1634,B_1635,C_1636,D_1637] :
      ( k2_partfun1(A_1634,B_1635,C_1636,D_1637) = k7_relat_1(C_1636,D_1637)
      | ~ m1_subset_1(C_1636,k1_zfmisc_1(k2_zfmisc_1(A_1634,B_1635)))
      | ~ v1_funct_1(C_1636) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14502,plain,(
    ! [D_1637] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_1637) = k7_relat_1('#skF_5',D_1637)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_14495])).

tff(c_14509,plain,(
    ! [D_1637] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_1637) = k7_relat_1('#skF_5',D_1637) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14502])).

tff(c_14500,plain,(
    ! [D_1637] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_1637) = k7_relat_1('#skF_6',D_1637)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_14495])).

tff(c_14506,plain,(
    ! [D_1637] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_1637) = k7_relat_1('#skF_6',D_1637) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14500])).

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

tff(c_15121,plain,(
    ! [C_1714,B_1712,E_1711,F_1713,D_1715,A_1710] :
      ( k2_partfun1(k4_subset_1(A_1710,C_1714,D_1715),B_1712,k1_tmap_1(A_1710,B_1712,C_1714,D_1715,E_1711,F_1713),C_1714) = E_1711
      | ~ m1_subset_1(k1_tmap_1(A_1710,B_1712,C_1714,D_1715,E_1711,F_1713),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1710,C_1714,D_1715),B_1712)))
      | ~ v1_funct_2(k1_tmap_1(A_1710,B_1712,C_1714,D_1715,E_1711,F_1713),k4_subset_1(A_1710,C_1714,D_1715),B_1712)
      | ~ v1_funct_1(k1_tmap_1(A_1710,B_1712,C_1714,D_1715,E_1711,F_1713))
      | k2_partfun1(D_1715,B_1712,F_1713,k9_subset_1(A_1710,C_1714,D_1715)) != k2_partfun1(C_1714,B_1712,E_1711,k9_subset_1(A_1710,C_1714,D_1715))
      | ~ m1_subset_1(F_1713,k1_zfmisc_1(k2_zfmisc_1(D_1715,B_1712)))
      | ~ v1_funct_2(F_1713,D_1715,B_1712)
      | ~ v1_funct_1(F_1713)
      | ~ m1_subset_1(E_1711,k1_zfmisc_1(k2_zfmisc_1(C_1714,B_1712)))
      | ~ v1_funct_2(E_1711,C_1714,B_1712)
      | ~ v1_funct_1(E_1711)
      | ~ m1_subset_1(D_1715,k1_zfmisc_1(A_1710))
      | v1_xboole_0(D_1715)
      | ~ m1_subset_1(C_1714,k1_zfmisc_1(A_1710))
      | v1_xboole_0(C_1714)
      | v1_xboole_0(B_1712)
      | v1_xboole_0(A_1710) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_16508,plain,(
    ! [E_1869,B_1867,D_1868,F_1871,A_1870,C_1866] :
      ( k2_partfun1(k4_subset_1(A_1870,C_1866,D_1868),B_1867,k1_tmap_1(A_1870,B_1867,C_1866,D_1868,E_1869,F_1871),C_1866) = E_1869
      | ~ v1_funct_2(k1_tmap_1(A_1870,B_1867,C_1866,D_1868,E_1869,F_1871),k4_subset_1(A_1870,C_1866,D_1868),B_1867)
      | ~ v1_funct_1(k1_tmap_1(A_1870,B_1867,C_1866,D_1868,E_1869,F_1871))
      | k2_partfun1(D_1868,B_1867,F_1871,k9_subset_1(A_1870,C_1866,D_1868)) != k2_partfun1(C_1866,B_1867,E_1869,k9_subset_1(A_1870,C_1866,D_1868))
      | ~ m1_subset_1(F_1871,k1_zfmisc_1(k2_zfmisc_1(D_1868,B_1867)))
      | ~ v1_funct_2(F_1871,D_1868,B_1867)
      | ~ v1_funct_1(F_1871)
      | ~ m1_subset_1(E_1869,k1_zfmisc_1(k2_zfmisc_1(C_1866,B_1867)))
      | ~ v1_funct_2(E_1869,C_1866,B_1867)
      | ~ v1_funct_1(E_1869)
      | ~ m1_subset_1(D_1868,k1_zfmisc_1(A_1870))
      | v1_xboole_0(D_1868)
      | ~ m1_subset_1(C_1866,k1_zfmisc_1(A_1870))
      | v1_xboole_0(C_1866)
      | v1_xboole_0(B_1867)
      | v1_xboole_0(A_1870) ) ),
    inference(resolution,[status(thm)],[c_46,c_15121])).

tff(c_18866,plain,(
    ! [C_2113,A_2117,F_2118,E_2116,D_2115,B_2114] :
      ( k2_partfun1(k4_subset_1(A_2117,C_2113,D_2115),B_2114,k1_tmap_1(A_2117,B_2114,C_2113,D_2115,E_2116,F_2118),C_2113) = E_2116
      | ~ v1_funct_1(k1_tmap_1(A_2117,B_2114,C_2113,D_2115,E_2116,F_2118))
      | k2_partfun1(D_2115,B_2114,F_2118,k9_subset_1(A_2117,C_2113,D_2115)) != k2_partfun1(C_2113,B_2114,E_2116,k9_subset_1(A_2117,C_2113,D_2115))
      | ~ m1_subset_1(F_2118,k1_zfmisc_1(k2_zfmisc_1(D_2115,B_2114)))
      | ~ v1_funct_2(F_2118,D_2115,B_2114)
      | ~ v1_funct_1(F_2118)
      | ~ m1_subset_1(E_2116,k1_zfmisc_1(k2_zfmisc_1(C_2113,B_2114)))
      | ~ v1_funct_2(E_2116,C_2113,B_2114)
      | ~ v1_funct_1(E_2116)
      | ~ m1_subset_1(D_2115,k1_zfmisc_1(A_2117))
      | v1_xboole_0(D_2115)
      | ~ m1_subset_1(C_2113,k1_zfmisc_1(A_2117))
      | v1_xboole_0(C_2113)
      | v1_xboole_0(B_2114)
      | v1_xboole_0(A_2117) ) ),
    inference(resolution,[status(thm)],[c_48,c_16508])).

tff(c_18873,plain,(
    ! [A_2117,C_2113,E_2116] :
      ( k2_partfun1(k4_subset_1(A_2117,C_2113,'#skF_4'),'#skF_2',k1_tmap_1(A_2117,'#skF_2',C_2113,'#skF_4',E_2116,'#skF_6'),C_2113) = E_2116
      | ~ v1_funct_1(k1_tmap_1(A_2117,'#skF_2',C_2113,'#skF_4',E_2116,'#skF_6'))
      | k2_partfun1(C_2113,'#skF_2',E_2116,k9_subset_1(A_2117,C_2113,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_2117,C_2113,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_2116,k1_zfmisc_1(k2_zfmisc_1(C_2113,'#skF_2')))
      | ~ v1_funct_2(E_2116,C_2113,'#skF_2')
      | ~ v1_funct_1(E_2116)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2117))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2113,k1_zfmisc_1(A_2117))
      | v1_xboole_0(C_2113)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2117) ) ),
    inference(resolution,[status(thm)],[c_54,c_18866])).

tff(c_18880,plain,(
    ! [A_2117,C_2113,E_2116] :
      ( k2_partfun1(k4_subset_1(A_2117,C_2113,'#skF_4'),'#skF_2',k1_tmap_1(A_2117,'#skF_2',C_2113,'#skF_4',E_2116,'#skF_6'),C_2113) = E_2116
      | ~ v1_funct_1(k1_tmap_1(A_2117,'#skF_2',C_2113,'#skF_4',E_2116,'#skF_6'))
      | k2_partfun1(C_2113,'#skF_2',E_2116,k9_subset_1(A_2117,C_2113,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2117,C_2113,'#skF_4'))
      | ~ m1_subset_1(E_2116,k1_zfmisc_1(k2_zfmisc_1(C_2113,'#skF_2')))
      | ~ v1_funct_2(E_2116,C_2113,'#skF_2')
      | ~ v1_funct_1(E_2116)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2117))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_2113,k1_zfmisc_1(A_2117))
      | v1_xboole_0(C_2113)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_2117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_14506,c_18873])).

tff(c_21585,plain,(
    ! [A_2359,C_2360,E_2361] :
      ( k2_partfun1(k4_subset_1(A_2359,C_2360,'#skF_4'),'#skF_2',k1_tmap_1(A_2359,'#skF_2',C_2360,'#skF_4',E_2361,'#skF_6'),C_2360) = E_2361
      | ~ v1_funct_1(k1_tmap_1(A_2359,'#skF_2',C_2360,'#skF_4',E_2361,'#skF_6'))
      | k2_partfun1(C_2360,'#skF_2',E_2361,k9_subset_1(A_2359,C_2360,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2359,C_2360,'#skF_4'))
      | ~ m1_subset_1(E_2361,k1_zfmisc_1(k2_zfmisc_1(C_2360,'#skF_2')))
      | ~ v1_funct_2(E_2361,C_2360,'#skF_2')
      | ~ v1_funct_1(E_2361)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2359))
      | ~ m1_subset_1(C_2360,k1_zfmisc_1(A_2359))
      | v1_xboole_0(C_2360)
      | v1_xboole_0(A_2359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_18880])).

tff(c_21595,plain,(
    ! [A_2359] :
      ( k2_partfun1(k4_subset_1(A_2359,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2359,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2359,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_2359,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2359,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2359))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2359))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2359) ) ),
    inference(resolution,[status(thm)],[c_60,c_21585])).

tff(c_21606,plain,(
    ! [A_2359] :
      ( k2_partfun1(k4_subset_1(A_2359,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2359,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2359,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2359,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2359,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2359))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2359))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_2359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_14509,c_21595])).

tff(c_23367,plain,(
    ! [A_2530] :
      ( k2_partfun1(k4_subset_1(A_2530,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_2530,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_2530,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_2530,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_2530,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_2530))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_2530))
      | v1_xboole_0(A_2530) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_21606])).

tff(c_864,plain,(
    ! [C_346,A_347,B_348] :
      ( v4_relat_1(C_346,A_347)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(B_348))
      | ~ v4_relat_1(B_348,A_347)
      | ~ v1_relat_1(B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_870,plain,(
    ! [A_347] :
      ( v4_relat_1('#skF_5',A_347)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_347)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_60,c_864])).

tff(c_908,plain,(
    ! [A_350] :
      ( v4_relat_1('#skF_5',A_350)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_350) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_870])).

tff(c_912,plain,
    ( v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_698,c_908])).

tff(c_915,plain,(
    v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_912])).

tff(c_918,plain,
    ( k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_915,c_30])).

tff(c_921,plain,(
    k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_918])).

tff(c_925,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_5',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_28])).

tff(c_1019,plain,(
    ! [B_354] :
      ( k7_relat_1('#skF_5',B_354) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_925])).

tff(c_1034,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_1019])).

tff(c_868,plain,(
    ! [A_347] :
      ( v4_relat_1('#skF_6',A_347)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_347)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_864])).

tff(c_884,plain,(
    ! [A_349] :
      ( v4_relat_1('#skF_6',A_349)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_868])).

tff(c_888,plain,
    ( v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_698,c_884])).

tff(c_891,plain,(
    v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_888])).

tff(c_894,plain,
    ( k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_891,c_30])).

tff(c_897,plain,(
    k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_894])).

tff(c_901,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_28])).

tff(c_931,plain,(
    ! [B_351] :
      ( k7_relat_1('#skF_6',B_351) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_901])).

tff(c_946,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_931])).

tff(c_727,plain,(
    ! [A_322,B_323] :
      ( r1_xboole_0(A_322,B_323)
      | ~ r1_subset_1(A_322,B_323)
      | v1_xboole_0(B_323)
      | v1_xboole_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_849,plain,(
    ! [A_344,B_345] :
      ( k3_xboole_0(A_344,B_345) = k1_xboole_0
      | ~ r1_subset_1(A_344,B_345)
      | v1_xboole_0(B_345)
      | v1_xboole_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_727,c_2])).

tff(c_855,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_849])).

tff(c_859,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_855])).

tff(c_763,plain,(
    ! [A_330,B_331,C_332] :
      ( k9_subset_1(A_330,B_331,C_332) = k3_xboole_0(B_331,C_332)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(A_330)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_777,plain,(
    ! [B_331] : k9_subset_1('#skF_1',B_331,'#skF_4') = k3_xboole_0(B_331,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_763])).

tff(c_1186,plain,(
    ! [D_372,A_374,B_371,E_373,C_370,F_375] :
      ( v1_funct_1(k1_tmap_1(A_374,B_371,C_370,D_372,E_373,F_375))
      | ~ m1_subset_1(F_375,k1_zfmisc_1(k2_zfmisc_1(D_372,B_371)))
      | ~ v1_funct_2(F_375,D_372,B_371)
      | ~ v1_funct_1(F_375)
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_370,B_371)))
      | ~ v1_funct_2(E_373,C_370,B_371)
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1(D_372,k1_zfmisc_1(A_374))
      | v1_xboole_0(D_372)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(A_374))
      | v1_xboole_0(C_370)
      | v1_xboole_0(B_371)
      | v1_xboole_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1191,plain,(
    ! [A_374,C_370,E_373] :
      ( v1_funct_1(k1_tmap_1(A_374,'#skF_2',C_370,'#skF_4',E_373,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_370,'#skF_2')))
      | ~ v1_funct_2(E_373,C_370,'#skF_2')
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_374))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_370,k1_zfmisc_1(A_374))
      | v1_xboole_0(C_370)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_374) ) ),
    inference(resolution,[status(thm)],[c_54,c_1186])).

tff(c_1197,plain,(
    ! [A_374,C_370,E_373] :
      ( v1_funct_1(k1_tmap_1(A_374,'#skF_2',C_370,'#skF_4',E_373,'#skF_6'))
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(C_370,'#skF_2')))
      | ~ v1_funct_2(E_373,C_370,'#skF_2')
      | ~ v1_funct_1(E_373)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_374))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_370,k1_zfmisc_1(A_374))
      | v1_xboole_0(C_370)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1191])).

tff(c_1204,plain,(
    ! [A_376,C_377,E_378] :
      ( v1_funct_1(k1_tmap_1(A_376,'#skF_2',C_377,'#skF_4',E_378,'#skF_6'))
      | ~ m1_subset_1(E_378,k1_zfmisc_1(k2_zfmisc_1(C_377,'#skF_2')))
      | ~ v1_funct_2(E_378,C_377,'#skF_2')
      | ~ v1_funct_1(E_378)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_376))
      | ~ m1_subset_1(C_377,k1_zfmisc_1(A_376))
      | v1_xboole_0(C_377)
      | v1_xboole_0(A_376) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_1197])).

tff(c_1211,plain,(
    ! [A_376] :
      ( v1_funct_1(k1_tmap_1(A_376,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_376))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_376))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_376) ) ),
    inference(resolution,[status(thm)],[c_60,c_1204])).

tff(c_1219,plain,(
    ! [A_376] :
      ( v1_funct_1(k1_tmap_1(A_376,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_376))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_376))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1211])).

tff(c_1557,plain,(
    ! [A_410] :
      ( v1_funct_1(k1_tmap_1(A_410,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_410))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_410))
      | v1_xboole_0(A_410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1219])).

tff(c_1564,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_1557])).

tff(c_1568,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1564])).

tff(c_1569,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1568])).

tff(c_1058,plain,(
    ! [A_358,B_359,C_360,D_361] :
      ( k2_partfun1(A_358,B_359,C_360,D_361) = k7_relat_1(C_360,D_361)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359)))
      | ~ v1_funct_1(C_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1065,plain,(
    ! [D_361] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_361) = k7_relat_1('#skF_5',D_361)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_1058])).

tff(c_1072,plain,(
    ! [D_361] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_361) = k7_relat_1('#skF_5',D_361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1065])).

tff(c_1063,plain,(
    ! [D_361] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_361) = k7_relat_1('#skF_6',D_361)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_1058])).

tff(c_1069,plain,(
    ! [D_361] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_361) = k7_relat_1('#skF_6',D_361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1063])).

tff(c_1774,plain,(
    ! [F_449,C_450,E_447,D_451,B_448,A_446] :
      ( k2_partfun1(k4_subset_1(A_446,C_450,D_451),B_448,k1_tmap_1(A_446,B_448,C_450,D_451,E_447,F_449),D_451) = F_449
      | ~ m1_subset_1(k1_tmap_1(A_446,B_448,C_450,D_451,E_447,F_449),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_446,C_450,D_451),B_448)))
      | ~ v1_funct_2(k1_tmap_1(A_446,B_448,C_450,D_451,E_447,F_449),k4_subset_1(A_446,C_450,D_451),B_448)
      | ~ v1_funct_1(k1_tmap_1(A_446,B_448,C_450,D_451,E_447,F_449))
      | k2_partfun1(D_451,B_448,F_449,k9_subset_1(A_446,C_450,D_451)) != k2_partfun1(C_450,B_448,E_447,k9_subset_1(A_446,C_450,D_451))
      | ~ m1_subset_1(F_449,k1_zfmisc_1(k2_zfmisc_1(D_451,B_448)))
      | ~ v1_funct_2(F_449,D_451,B_448)
      | ~ v1_funct_1(F_449)
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(C_450,B_448)))
      | ~ v1_funct_2(E_447,C_450,B_448)
      | ~ v1_funct_1(E_447)
      | ~ m1_subset_1(D_451,k1_zfmisc_1(A_446))
      | v1_xboole_0(D_451)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(A_446))
      | v1_xboole_0(C_450)
      | v1_xboole_0(B_448)
      | v1_xboole_0(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3207,plain,(
    ! [B_601,C_600,F_605,E_603,A_604,D_602] :
      ( k2_partfun1(k4_subset_1(A_604,C_600,D_602),B_601,k1_tmap_1(A_604,B_601,C_600,D_602,E_603,F_605),D_602) = F_605
      | ~ v1_funct_2(k1_tmap_1(A_604,B_601,C_600,D_602,E_603,F_605),k4_subset_1(A_604,C_600,D_602),B_601)
      | ~ v1_funct_1(k1_tmap_1(A_604,B_601,C_600,D_602,E_603,F_605))
      | k2_partfun1(D_602,B_601,F_605,k9_subset_1(A_604,C_600,D_602)) != k2_partfun1(C_600,B_601,E_603,k9_subset_1(A_604,C_600,D_602))
      | ~ m1_subset_1(F_605,k1_zfmisc_1(k2_zfmisc_1(D_602,B_601)))
      | ~ v1_funct_2(F_605,D_602,B_601)
      | ~ v1_funct_1(F_605)
      | ~ m1_subset_1(E_603,k1_zfmisc_1(k2_zfmisc_1(C_600,B_601)))
      | ~ v1_funct_2(E_603,C_600,B_601)
      | ~ v1_funct_1(E_603)
      | ~ m1_subset_1(D_602,k1_zfmisc_1(A_604))
      | v1_xboole_0(D_602)
      | ~ m1_subset_1(C_600,k1_zfmisc_1(A_604))
      | v1_xboole_0(C_600)
      | v1_xboole_0(B_601)
      | v1_xboole_0(A_604) ) ),
    inference(resolution,[status(thm)],[c_46,c_1774])).

tff(c_5335,plain,(
    ! [E_824,D_823,B_822,A_825,F_826,C_821] :
      ( k2_partfun1(k4_subset_1(A_825,C_821,D_823),B_822,k1_tmap_1(A_825,B_822,C_821,D_823,E_824,F_826),D_823) = F_826
      | ~ v1_funct_1(k1_tmap_1(A_825,B_822,C_821,D_823,E_824,F_826))
      | k2_partfun1(D_823,B_822,F_826,k9_subset_1(A_825,C_821,D_823)) != k2_partfun1(C_821,B_822,E_824,k9_subset_1(A_825,C_821,D_823))
      | ~ m1_subset_1(F_826,k1_zfmisc_1(k2_zfmisc_1(D_823,B_822)))
      | ~ v1_funct_2(F_826,D_823,B_822)
      | ~ v1_funct_1(F_826)
      | ~ m1_subset_1(E_824,k1_zfmisc_1(k2_zfmisc_1(C_821,B_822)))
      | ~ v1_funct_2(E_824,C_821,B_822)
      | ~ v1_funct_1(E_824)
      | ~ m1_subset_1(D_823,k1_zfmisc_1(A_825))
      | v1_xboole_0(D_823)
      | ~ m1_subset_1(C_821,k1_zfmisc_1(A_825))
      | v1_xboole_0(C_821)
      | v1_xboole_0(B_822)
      | v1_xboole_0(A_825) ) ),
    inference(resolution,[status(thm)],[c_48,c_3207])).

tff(c_5342,plain,(
    ! [A_825,C_821,E_824] :
      ( k2_partfun1(k4_subset_1(A_825,C_821,'#skF_4'),'#skF_2',k1_tmap_1(A_825,'#skF_2',C_821,'#skF_4',E_824,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_825,'#skF_2',C_821,'#skF_4',E_824,'#skF_6'))
      | k2_partfun1(C_821,'#skF_2',E_824,k9_subset_1(A_825,C_821,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_825,C_821,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_824,k1_zfmisc_1(k2_zfmisc_1(C_821,'#skF_2')))
      | ~ v1_funct_2(E_824,C_821,'#skF_2')
      | ~ v1_funct_1(E_824)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_825))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_821,k1_zfmisc_1(A_825))
      | v1_xboole_0(C_821)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_825) ) ),
    inference(resolution,[status(thm)],[c_54,c_5335])).

tff(c_5349,plain,(
    ! [A_825,C_821,E_824] :
      ( k2_partfun1(k4_subset_1(A_825,C_821,'#skF_4'),'#skF_2',k1_tmap_1(A_825,'#skF_2',C_821,'#skF_4',E_824,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_825,'#skF_2',C_821,'#skF_4',E_824,'#skF_6'))
      | k2_partfun1(C_821,'#skF_2',E_824,k9_subset_1(A_825,C_821,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_825,C_821,'#skF_4'))
      | ~ m1_subset_1(E_824,k1_zfmisc_1(k2_zfmisc_1(C_821,'#skF_2')))
      | ~ v1_funct_2(E_824,C_821,'#skF_2')
      | ~ v1_funct_1(E_824)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_825))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_821,k1_zfmisc_1(A_825))
      | v1_xboole_0(C_821)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_825) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1069,c_5342])).

tff(c_8248,plain,(
    ! [A_1107,C_1108,E_1109] :
      ( k2_partfun1(k4_subset_1(A_1107,C_1108,'#skF_4'),'#skF_2',k1_tmap_1(A_1107,'#skF_2',C_1108,'#skF_4',E_1109,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1107,'#skF_2',C_1108,'#skF_4',E_1109,'#skF_6'))
      | k2_partfun1(C_1108,'#skF_2',E_1109,k9_subset_1(A_1107,C_1108,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1107,C_1108,'#skF_4'))
      | ~ m1_subset_1(E_1109,k1_zfmisc_1(k2_zfmisc_1(C_1108,'#skF_2')))
      | ~ v1_funct_2(E_1109,C_1108,'#skF_2')
      | ~ v1_funct_1(E_1109)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1107))
      | ~ m1_subset_1(C_1108,k1_zfmisc_1(A_1107))
      | v1_xboole_0(C_1108)
      | v1_xboole_0(A_1107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_5349])).

tff(c_8258,plain,(
    ! [A_1107] :
      ( k2_partfun1(k4_subset_1(A_1107,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1107,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1107,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1107,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1107,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1107))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1107))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1107) ) ),
    inference(resolution,[status(thm)],[c_60,c_8248])).

tff(c_8269,plain,(
    ! [A_1107] :
      ( k2_partfun1(k4_subset_1(A_1107,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1107,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1107,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1107,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1107,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1107))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1107))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1072,c_8258])).

tff(c_13996,plain,(
    ! [A_1591] :
      ( k2_partfun1(k4_subset_1(A_1591,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1591,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1591,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1591,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1591,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1591))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1591))
      | v1_xboole_0(A_1591) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8269])).

tff(c_144,plain,(
    ! [C_238,A_239,B_240] :
      ( v1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_157,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_144])).

tff(c_185,plain,(
    ! [B_248,A_249] :
      ( v4_relat_1(B_248,A_249)
      | ~ r1_tarski(k1_relat_1(B_248),A_249)
      | ~ v1_relat_1(B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_194,plain,(
    ! [B_248] :
      ( v4_relat_1(B_248,k1_relat_1(B_248))
      | ~ v1_relat_1(B_248) ) ),
    inference(resolution,[status(thm)],[c_10,c_185])).

tff(c_301,plain,(
    ! [C_268,A_269,B_270] :
      ( v4_relat_1(C_268,A_269)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(B_270))
      | ~ v4_relat_1(B_270,A_269)
      | ~ v1_relat_1(B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_307,plain,(
    ! [A_269] :
      ( v4_relat_1('#skF_5',A_269)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_269)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_60,c_301])).

tff(c_345,plain,(
    ! [A_272] :
      ( v4_relat_1('#skF_5',A_272)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_3','#skF_2'),A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_307])).

tff(c_349,plain,
    ( v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_194,c_345])).

tff(c_352,plain,(
    v4_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_349])).

tff(c_355,plain,
    ( k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_352,c_30])).

tff(c_358,plain,(
    k7_relat_1('#skF_5',k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2'))) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_355])).

tff(c_362,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_5',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_28])).

tff(c_543,plain,(
    ! [B_294] :
      ( k7_relat_1('#skF_5',B_294) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')),B_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_362])).

tff(c_558,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_543])).

tff(c_156,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_144])).

tff(c_305,plain,(
    ! [A_269] :
      ( v4_relat_1('#skF_6',A_269)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_269)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_54,c_301])).

tff(c_321,plain,(
    ! [A_271] :
      ( v4_relat_1('#skF_6',A_271)
      | ~ v4_relat_1(k2_zfmisc_1('#skF_4','#skF_2'),A_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_305])).

tff(c_325,plain,
    ( v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_194,c_321])).

tff(c_328,plain,(
    v4_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_325])).

tff(c_331,plain,
    ( k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_328,c_30])).

tff(c_334,plain,(
    k7_relat_1('#skF_6',k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_331])).

tff(c_338,plain,(
    ! [B_20] :
      ( k7_relat_1('#skF_6',B_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_20)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_28])).

tff(c_443,plain,(
    ! [B_285] :
      ( k7_relat_1('#skF_6',B_285) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')),B_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_338])).

tff(c_458,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_443])).

tff(c_211,plain,(
    ! [A_252,B_253] :
      ( r1_xboole_0(A_252,B_253)
      | ~ r1_subset_1(A_252,B_253)
      | v1_xboole_0(B_253)
      | v1_xboole_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_585,plain,(
    ! [A_298,B_299] :
      ( k3_xboole_0(A_298,B_299) = k1_xboole_0
      | ~ r1_subset_1(A_298,B_299)
      | v1_xboole_0(B_299)
      | v1_xboole_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_211,c_2])).

tff(c_588,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_585])).

tff(c_591,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_70,c_588])).

tff(c_368,plain,(
    ! [A_273,B_274,C_275,D_276] :
      ( k2_partfun1(A_273,B_274,C_275,D_276) = k7_relat_1(C_275,D_276)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274)))
      | ~ v1_funct_1(C_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_375,plain,(
    ! [D_276] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_276) = k7_relat_1('#skF_5',D_276)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_368])).

tff(c_382,plain,(
    ! [D_276] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_276) = k7_relat_1('#skF_5',D_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_375])).

tff(c_373,plain,(
    ! [D_276] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_276) = k7_relat_1('#skF_6',D_276)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_368])).

tff(c_379,plain,(
    ! [D_276] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_276) = k7_relat_1('#skF_6',D_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_373])).

tff(c_257,plain,(
    ! [A_262,B_263,C_264] :
      ( k9_subset_1(A_262,B_263,C_264) = k3_xboole_0(B_263,C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(A_262)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_271,plain,(
    ! [B_263] : k9_subset_1('#skF_1',B_263,'#skF_4') = k3_xboole_0(B_263,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_257])).

tff(c_52,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_96,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_273,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_271,c_96])).

tff(c_410,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k7_relat_1('#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_379,c_273])).

tff(c_592,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) != k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_591,c_410])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_458,c_592])).

tff(c_596,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_725,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_14028,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13996,c_725])).

tff(c_14072,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1034,c_946,c_859,c_859,c_777,c_777,c_1569,c_14028])).

tff(c_14074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14072])).

tff(c_14075,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_23390,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23367,c_14075])).

tff(c_23426,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_14389,c_14301,c_14205,c_14205,c_14128,c_14128,c_15186,c_23390])).

tff(c_23428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_23426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:36:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.79/30.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.79/30.57  
% 40.79/30.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.79/30.58  %$ v1_funct_2 > v4_relat_1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 40.79/30.58  
% 40.79/30.58  %Foreground sorts:
% 40.79/30.58  
% 40.79/30.58  
% 40.79/30.58  %Background operators:
% 40.79/30.58  
% 40.79/30.58  
% 40.79/30.58  %Foreground operators:
% 40.79/30.58  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 40.79/30.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 40.79/30.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.79/30.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 40.79/30.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.79/30.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.79/30.58  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 40.79/30.58  tff('#skF_5', type, '#skF_5': $i).
% 40.79/30.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 40.79/30.58  tff('#skF_6', type, '#skF_6': $i).
% 40.79/30.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 40.79/30.58  tff('#skF_2', type, '#skF_2': $i).
% 40.79/30.58  tff('#skF_3', type, '#skF_3': $i).
% 40.79/30.58  tff('#skF_1', type, '#skF_1': $i).
% 40.79/30.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 40.79/30.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.79/30.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 40.79/30.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 40.79/30.58  tff('#skF_4', type, '#skF_4': $i).
% 40.79/30.58  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 40.79/30.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.79/30.58  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 40.79/30.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 40.79/30.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 40.79/30.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 40.79/30.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 40.79/30.58  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 40.79/30.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 40.79/30.58  
% 41.06/30.61  tff(f_218, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 41.06/30.61  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 41.06/30.61  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 41.06/30.61  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 41.06/30.61  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 41.06/30.61  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 41.06/30.61  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_relat_1)).
% 41.06/30.61  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 41.06/30.61  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 41.06/30.61  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 41.06/30.61  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 41.06/30.61  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 41.06/30.61  tff(f_176, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 41.06/30.61  tff(f_94, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 41.06/30.61  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 41.06/30.61  tff(c_78, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.06/30.61  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_645, plain, (![C_306, A_307, B_308]: (v1_relat_1(C_306) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_307, B_308))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 41.06/30.61  tff(c_658, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_645])).
% 41.06/30.61  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 41.06/30.61  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 41.06/30.61  tff(c_689, plain, (![B_314, A_315]: (v4_relat_1(B_314, A_315) | ~r1_tarski(k1_relat_1(B_314), A_315) | ~v1_relat_1(B_314))), inference(cnfTransformation, [status(thm)], [f_60])).
% 41.06/30.61  tff(c_698, plain, (![B_314]: (v4_relat_1(B_314, k1_relat_1(B_314)) | ~v1_relat_1(B_314))), inference(resolution, [status(thm)], [c_10, c_689])).
% 41.06/30.61  tff(c_14215, plain, (![C_1616, A_1617, B_1618]: (v4_relat_1(C_1616, A_1617) | ~m1_subset_1(C_1616, k1_zfmisc_1(B_1618)) | ~v4_relat_1(B_1618, A_1617) | ~v1_relat_1(B_1618))), inference(cnfTransformation, [status(thm)], [f_54])).
% 41.06/30.61  tff(c_14221, plain, (![A_1617]: (v4_relat_1('#skF_5', A_1617) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_1617) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_60, c_14215])).
% 41.06/30.61  tff(c_14259, plain, (![A_1620]: (v4_relat_1('#skF_5', A_1620) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_1620))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14221])).
% 41.06/30.61  tff(c_14263, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_698, c_14259])).
% 41.06/30.61  tff(c_14266, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14263])).
% 41.06/30.61  tff(c_30, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 41.06/30.61  tff(c_14269, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14266, c_30])).
% 41.06/30.61  tff(c_14272, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_14269])).
% 41.06/30.61  tff(c_28, plain, (![C_21, A_19, B_20]: (k7_relat_1(k7_relat_1(C_21, A_19), B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 41.06/30.61  tff(c_14276, plain, (![B_20]: (k7_relat_1('#skF_5', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14272, c_28])).
% 41.06/30.61  tff(c_14374, plain, (![B_1624]: (k7_relat_1('#skF_5', B_1624)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_1624))), inference(demodulation, [status(thm), theory('equality')], [c_658, c_14276])).
% 41.06/30.61  tff(c_14389, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_14374])).
% 41.06/30.61  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_657, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_645])).
% 41.06/30.61  tff(c_14219, plain, (![A_1617]: (v4_relat_1('#skF_6', A_1617) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_1617) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_14215])).
% 41.06/30.61  tff(c_14235, plain, (![A_1619]: (v4_relat_1('#skF_6', A_1619) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_1619))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14219])).
% 41.06/30.61  tff(c_14239, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_698, c_14235])).
% 41.06/30.61  tff(c_14242, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14239])).
% 41.06/30.61  tff(c_14245, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_14242, c_30])).
% 41.06/30.61  tff(c_14248, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_657, c_14245])).
% 41.06/30.61  tff(c_14252, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_14248, c_28])).
% 41.06/30.61  tff(c_14286, plain, (![B_1621]: (k7_relat_1('#skF_6', B_1621)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_1621))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_14252])).
% 41.06/30.61  tff(c_14301, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_14286])).
% 41.06/30.61  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_66, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_14078, plain, (![A_1592, B_1593]: (r1_xboole_0(A_1592, B_1593) | ~r1_subset_1(A_1592, B_1593) | v1_xboole_0(B_1593) | v1_xboole_0(A_1592))), inference(cnfTransformation, [status(thm)], [f_84])).
% 41.06/30.61  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 41.06/30.61  tff(c_14199, plain, (![A_1612, B_1613]: (k3_xboole_0(A_1612, B_1613)=k1_xboole_0 | ~r1_subset_1(A_1612, B_1613) | v1_xboole_0(B_1613) | v1_xboole_0(A_1612))), inference(resolution, [status(thm)], [c_14078, c_2])).
% 41.06/30.61  tff(c_14202, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_14199])).
% 41.06/30.61  tff(c_14205, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_14202])).
% 41.06/30.61  tff(c_14114, plain, (![A_1600, B_1601, C_1602]: (k9_subset_1(A_1600, B_1601, C_1602)=k3_xboole_0(B_1601, C_1602) | ~m1_subset_1(C_1602, k1_zfmisc_1(A_1600)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 41.06/30.61  tff(c_14128, plain, (![B_1601]: (k9_subset_1('#skF_1', B_1601, '#skF_4')=k3_xboole_0(B_1601, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_14114])).
% 41.06/30.61  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_76, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_14659, plain, (![A_1653, B_1650, F_1654, E_1652, D_1651, C_1649]: (v1_funct_1(k1_tmap_1(A_1653, B_1650, C_1649, D_1651, E_1652, F_1654)) | ~m1_subset_1(F_1654, k1_zfmisc_1(k2_zfmisc_1(D_1651, B_1650))) | ~v1_funct_2(F_1654, D_1651, B_1650) | ~v1_funct_1(F_1654) | ~m1_subset_1(E_1652, k1_zfmisc_1(k2_zfmisc_1(C_1649, B_1650))) | ~v1_funct_2(E_1652, C_1649, B_1650) | ~v1_funct_1(E_1652) | ~m1_subset_1(D_1651, k1_zfmisc_1(A_1653)) | v1_xboole_0(D_1651) | ~m1_subset_1(C_1649, k1_zfmisc_1(A_1653)) | v1_xboole_0(C_1649) | v1_xboole_0(B_1650) | v1_xboole_0(A_1653))), inference(cnfTransformation, [status(thm)], [f_176])).
% 41.06/30.61  tff(c_14664, plain, (![A_1653, C_1649, E_1652]: (v1_funct_1(k1_tmap_1(A_1653, '#skF_2', C_1649, '#skF_4', E_1652, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1652, k1_zfmisc_1(k2_zfmisc_1(C_1649, '#skF_2'))) | ~v1_funct_2(E_1652, C_1649, '#skF_2') | ~v1_funct_1(E_1652) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1653)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1649, k1_zfmisc_1(A_1653)) | v1_xboole_0(C_1649) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1653))), inference(resolution, [status(thm)], [c_54, c_14659])).
% 41.06/30.61  tff(c_14670, plain, (![A_1653, C_1649, E_1652]: (v1_funct_1(k1_tmap_1(A_1653, '#skF_2', C_1649, '#skF_4', E_1652, '#skF_6')) | ~m1_subset_1(E_1652, k1_zfmisc_1(k2_zfmisc_1(C_1649, '#skF_2'))) | ~v1_funct_2(E_1652, C_1649, '#skF_2') | ~v1_funct_1(E_1652) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1653)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1649, k1_zfmisc_1(A_1653)) | v1_xboole_0(C_1649) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1653))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_14664])).
% 41.06/30.61  tff(c_15068, plain, (![A_1699, C_1700, E_1701]: (v1_funct_1(k1_tmap_1(A_1699, '#skF_2', C_1700, '#skF_4', E_1701, '#skF_6')) | ~m1_subset_1(E_1701, k1_zfmisc_1(k2_zfmisc_1(C_1700, '#skF_2'))) | ~v1_funct_2(E_1701, C_1700, '#skF_2') | ~v1_funct_1(E_1701) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1699)) | ~m1_subset_1(C_1700, k1_zfmisc_1(A_1699)) | v1_xboole_0(C_1700) | v1_xboole_0(A_1699))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_14670])).
% 41.06/30.61  tff(c_15078, plain, (![A_1699]: (v1_funct_1(k1_tmap_1(A_1699, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1699)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1699)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1699))), inference(resolution, [status(thm)], [c_60, c_15068])).
% 41.06/30.61  tff(c_15089, plain, (![A_1699]: (v1_funct_1(k1_tmap_1(A_1699, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1699)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1699)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1699))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_15078])).
% 41.06/30.61  tff(c_15174, plain, (![A_1721]: (v1_funct_1(k1_tmap_1(A_1721, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1721)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1721)) | v1_xboole_0(A_1721))), inference(negUnitSimplification, [status(thm)], [c_74, c_15089])).
% 41.06/30.61  tff(c_15181, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_15174])).
% 41.06/30.61  tff(c_15185, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_15181])).
% 41.06/30.61  tff(c_15186, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_15185])).
% 41.06/30.61  tff(c_14495, plain, (![A_1634, B_1635, C_1636, D_1637]: (k2_partfun1(A_1634, B_1635, C_1636, D_1637)=k7_relat_1(C_1636, D_1637) | ~m1_subset_1(C_1636, k1_zfmisc_1(k2_zfmisc_1(A_1634, B_1635))) | ~v1_funct_1(C_1636))), inference(cnfTransformation, [status(thm)], [f_94])).
% 41.06/30.61  tff(c_14502, plain, (![D_1637]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1637)=k7_relat_1('#skF_5', D_1637) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_14495])).
% 41.06/30.61  tff(c_14509, plain, (![D_1637]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_1637)=k7_relat_1('#skF_5', D_1637))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_14502])).
% 41.06/30.61  tff(c_14500, plain, (![D_1637]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1637)=k7_relat_1('#skF_6', D_1637) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_14495])).
% 41.06/30.61  tff(c_14506, plain, (![D_1637]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_1637)=k7_relat_1('#skF_6', D_1637))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14500])).
% 41.06/30.61  tff(c_48, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (v1_funct_2(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k4_subset_1(A_160, C_162, D_163), B_161) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_176])).
% 41.06/30.61  tff(c_46, plain, (![B_161, C_162, A_160, E_164, F_165, D_163]: (m1_subset_1(k1_tmap_1(A_160, B_161, C_162, D_163, E_164, F_165), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_160, C_162, D_163), B_161))) | ~m1_subset_1(F_165, k1_zfmisc_1(k2_zfmisc_1(D_163, B_161))) | ~v1_funct_2(F_165, D_163, B_161) | ~v1_funct_1(F_165) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(C_162, B_161))) | ~v1_funct_2(E_164, C_162, B_161) | ~v1_funct_1(E_164) | ~m1_subset_1(D_163, k1_zfmisc_1(A_160)) | v1_xboole_0(D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(A_160)) | v1_xboole_0(C_162) | v1_xboole_0(B_161) | v1_xboole_0(A_160))), inference(cnfTransformation, [status(thm)], [f_176])).
% 41.06/30.61  tff(c_15121, plain, (![C_1714, B_1712, E_1711, F_1713, D_1715, A_1710]: (k2_partfun1(k4_subset_1(A_1710, C_1714, D_1715), B_1712, k1_tmap_1(A_1710, B_1712, C_1714, D_1715, E_1711, F_1713), C_1714)=E_1711 | ~m1_subset_1(k1_tmap_1(A_1710, B_1712, C_1714, D_1715, E_1711, F_1713), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1710, C_1714, D_1715), B_1712))) | ~v1_funct_2(k1_tmap_1(A_1710, B_1712, C_1714, D_1715, E_1711, F_1713), k4_subset_1(A_1710, C_1714, D_1715), B_1712) | ~v1_funct_1(k1_tmap_1(A_1710, B_1712, C_1714, D_1715, E_1711, F_1713)) | k2_partfun1(D_1715, B_1712, F_1713, k9_subset_1(A_1710, C_1714, D_1715))!=k2_partfun1(C_1714, B_1712, E_1711, k9_subset_1(A_1710, C_1714, D_1715)) | ~m1_subset_1(F_1713, k1_zfmisc_1(k2_zfmisc_1(D_1715, B_1712))) | ~v1_funct_2(F_1713, D_1715, B_1712) | ~v1_funct_1(F_1713) | ~m1_subset_1(E_1711, k1_zfmisc_1(k2_zfmisc_1(C_1714, B_1712))) | ~v1_funct_2(E_1711, C_1714, B_1712) | ~v1_funct_1(E_1711) | ~m1_subset_1(D_1715, k1_zfmisc_1(A_1710)) | v1_xboole_0(D_1715) | ~m1_subset_1(C_1714, k1_zfmisc_1(A_1710)) | v1_xboole_0(C_1714) | v1_xboole_0(B_1712) | v1_xboole_0(A_1710))), inference(cnfTransformation, [status(thm)], [f_142])).
% 41.06/30.61  tff(c_16508, plain, (![E_1869, B_1867, D_1868, F_1871, A_1870, C_1866]: (k2_partfun1(k4_subset_1(A_1870, C_1866, D_1868), B_1867, k1_tmap_1(A_1870, B_1867, C_1866, D_1868, E_1869, F_1871), C_1866)=E_1869 | ~v1_funct_2(k1_tmap_1(A_1870, B_1867, C_1866, D_1868, E_1869, F_1871), k4_subset_1(A_1870, C_1866, D_1868), B_1867) | ~v1_funct_1(k1_tmap_1(A_1870, B_1867, C_1866, D_1868, E_1869, F_1871)) | k2_partfun1(D_1868, B_1867, F_1871, k9_subset_1(A_1870, C_1866, D_1868))!=k2_partfun1(C_1866, B_1867, E_1869, k9_subset_1(A_1870, C_1866, D_1868)) | ~m1_subset_1(F_1871, k1_zfmisc_1(k2_zfmisc_1(D_1868, B_1867))) | ~v1_funct_2(F_1871, D_1868, B_1867) | ~v1_funct_1(F_1871) | ~m1_subset_1(E_1869, k1_zfmisc_1(k2_zfmisc_1(C_1866, B_1867))) | ~v1_funct_2(E_1869, C_1866, B_1867) | ~v1_funct_1(E_1869) | ~m1_subset_1(D_1868, k1_zfmisc_1(A_1870)) | v1_xboole_0(D_1868) | ~m1_subset_1(C_1866, k1_zfmisc_1(A_1870)) | v1_xboole_0(C_1866) | v1_xboole_0(B_1867) | v1_xboole_0(A_1870))), inference(resolution, [status(thm)], [c_46, c_15121])).
% 41.06/30.61  tff(c_18866, plain, (![C_2113, A_2117, F_2118, E_2116, D_2115, B_2114]: (k2_partfun1(k4_subset_1(A_2117, C_2113, D_2115), B_2114, k1_tmap_1(A_2117, B_2114, C_2113, D_2115, E_2116, F_2118), C_2113)=E_2116 | ~v1_funct_1(k1_tmap_1(A_2117, B_2114, C_2113, D_2115, E_2116, F_2118)) | k2_partfun1(D_2115, B_2114, F_2118, k9_subset_1(A_2117, C_2113, D_2115))!=k2_partfun1(C_2113, B_2114, E_2116, k9_subset_1(A_2117, C_2113, D_2115)) | ~m1_subset_1(F_2118, k1_zfmisc_1(k2_zfmisc_1(D_2115, B_2114))) | ~v1_funct_2(F_2118, D_2115, B_2114) | ~v1_funct_1(F_2118) | ~m1_subset_1(E_2116, k1_zfmisc_1(k2_zfmisc_1(C_2113, B_2114))) | ~v1_funct_2(E_2116, C_2113, B_2114) | ~v1_funct_1(E_2116) | ~m1_subset_1(D_2115, k1_zfmisc_1(A_2117)) | v1_xboole_0(D_2115) | ~m1_subset_1(C_2113, k1_zfmisc_1(A_2117)) | v1_xboole_0(C_2113) | v1_xboole_0(B_2114) | v1_xboole_0(A_2117))), inference(resolution, [status(thm)], [c_48, c_16508])).
% 41.06/30.61  tff(c_18873, plain, (![A_2117, C_2113, E_2116]: (k2_partfun1(k4_subset_1(A_2117, C_2113, '#skF_4'), '#skF_2', k1_tmap_1(A_2117, '#skF_2', C_2113, '#skF_4', E_2116, '#skF_6'), C_2113)=E_2116 | ~v1_funct_1(k1_tmap_1(A_2117, '#skF_2', C_2113, '#skF_4', E_2116, '#skF_6')) | k2_partfun1(C_2113, '#skF_2', E_2116, k9_subset_1(A_2117, C_2113, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_2117, C_2113, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_2116, k1_zfmisc_1(k2_zfmisc_1(C_2113, '#skF_2'))) | ~v1_funct_2(E_2116, C_2113, '#skF_2') | ~v1_funct_1(E_2116) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2117)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2113, k1_zfmisc_1(A_2117)) | v1_xboole_0(C_2113) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2117))), inference(resolution, [status(thm)], [c_54, c_18866])).
% 41.06/30.61  tff(c_18880, plain, (![A_2117, C_2113, E_2116]: (k2_partfun1(k4_subset_1(A_2117, C_2113, '#skF_4'), '#skF_2', k1_tmap_1(A_2117, '#skF_2', C_2113, '#skF_4', E_2116, '#skF_6'), C_2113)=E_2116 | ~v1_funct_1(k1_tmap_1(A_2117, '#skF_2', C_2113, '#skF_4', E_2116, '#skF_6')) | k2_partfun1(C_2113, '#skF_2', E_2116, k9_subset_1(A_2117, C_2113, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2117, C_2113, '#skF_4')) | ~m1_subset_1(E_2116, k1_zfmisc_1(k2_zfmisc_1(C_2113, '#skF_2'))) | ~v1_funct_2(E_2116, C_2113, '#skF_2') | ~v1_funct_1(E_2116) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2117)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_2113, k1_zfmisc_1(A_2117)) | v1_xboole_0(C_2113) | v1_xboole_0('#skF_2') | v1_xboole_0(A_2117))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_14506, c_18873])).
% 41.06/30.61  tff(c_21585, plain, (![A_2359, C_2360, E_2361]: (k2_partfun1(k4_subset_1(A_2359, C_2360, '#skF_4'), '#skF_2', k1_tmap_1(A_2359, '#skF_2', C_2360, '#skF_4', E_2361, '#skF_6'), C_2360)=E_2361 | ~v1_funct_1(k1_tmap_1(A_2359, '#skF_2', C_2360, '#skF_4', E_2361, '#skF_6')) | k2_partfun1(C_2360, '#skF_2', E_2361, k9_subset_1(A_2359, C_2360, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2359, C_2360, '#skF_4')) | ~m1_subset_1(E_2361, k1_zfmisc_1(k2_zfmisc_1(C_2360, '#skF_2'))) | ~v1_funct_2(E_2361, C_2360, '#skF_2') | ~v1_funct_1(E_2361) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2359)) | ~m1_subset_1(C_2360, k1_zfmisc_1(A_2359)) | v1_xboole_0(C_2360) | v1_xboole_0(A_2359))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_18880])).
% 41.06/30.61  tff(c_21595, plain, (![A_2359]: (k2_partfun1(k4_subset_1(A_2359, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2359, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2359, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_2359, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2359, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2359)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2359)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2359))), inference(resolution, [status(thm)], [c_60, c_21585])).
% 41.06/30.61  tff(c_21606, plain, (![A_2359]: (k2_partfun1(k4_subset_1(A_2359, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2359, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2359, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2359, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2359, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2359)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2359)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_2359))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_14509, c_21595])).
% 41.06/30.61  tff(c_23367, plain, (![A_2530]: (k2_partfun1(k4_subset_1(A_2530, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_2530, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_2530, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_2530, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_2530, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_2530)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_2530)) | v1_xboole_0(A_2530))), inference(negUnitSimplification, [status(thm)], [c_74, c_21606])).
% 41.06/30.61  tff(c_864, plain, (![C_346, A_347, B_348]: (v4_relat_1(C_346, A_347) | ~m1_subset_1(C_346, k1_zfmisc_1(B_348)) | ~v4_relat_1(B_348, A_347) | ~v1_relat_1(B_348))), inference(cnfTransformation, [status(thm)], [f_54])).
% 41.06/30.61  tff(c_870, plain, (![A_347]: (v4_relat_1('#skF_5', A_347) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_347) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_60, c_864])).
% 41.06/30.61  tff(c_908, plain, (![A_350]: (v4_relat_1('#skF_5', A_350) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_350))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_870])).
% 41.06/30.61  tff(c_912, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_698, c_908])).
% 41.06/30.61  tff(c_915, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_912])).
% 41.06/30.61  tff(c_918, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_915, c_30])).
% 41.06/30.61  tff(c_921, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_918])).
% 41.06/30.61  tff(c_925, plain, (![B_20]: (k7_relat_1('#skF_5', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_921, c_28])).
% 41.06/30.61  tff(c_1019, plain, (![B_354]: (k7_relat_1('#skF_5', B_354)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_354))), inference(demodulation, [status(thm), theory('equality')], [c_658, c_925])).
% 41.06/30.61  tff(c_1034, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_1019])).
% 41.06/30.61  tff(c_868, plain, (![A_347]: (v4_relat_1('#skF_6', A_347) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_347) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_864])).
% 41.06/30.61  tff(c_884, plain, (![A_349]: (v4_relat_1('#skF_6', A_349) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_349))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_868])).
% 41.06/30.61  tff(c_888, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_698, c_884])).
% 41.06/30.61  tff(c_891, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_888])).
% 41.06/30.61  tff(c_894, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_891, c_30])).
% 41.06/30.61  tff(c_897, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_657, c_894])).
% 41.06/30.61  tff(c_901, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_897, c_28])).
% 41.06/30.61  tff(c_931, plain, (![B_351]: (k7_relat_1('#skF_6', B_351)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_351))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_901])).
% 41.06/30.61  tff(c_946, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_931])).
% 41.06/30.61  tff(c_727, plain, (![A_322, B_323]: (r1_xboole_0(A_322, B_323) | ~r1_subset_1(A_322, B_323) | v1_xboole_0(B_323) | v1_xboole_0(A_322))), inference(cnfTransformation, [status(thm)], [f_84])).
% 41.06/30.61  tff(c_849, plain, (![A_344, B_345]: (k3_xboole_0(A_344, B_345)=k1_xboole_0 | ~r1_subset_1(A_344, B_345) | v1_xboole_0(B_345) | v1_xboole_0(A_344))), inference(resolution, [status(thm)], [c_727, c_2])).
% 41.06/30.61  tff(c_855, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_849])).
% 41.06/30.61  tff(c_859, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_855])).
% 41.06/30.61  tff(c_763, plain, (![A_330, B_331, C_332]: (k9_subset_1(A_330, B_331, C_332)=k3_xboole_0(B_331, C_332) | ~m1_subset_1(C_332, k1_zfmisc_1(A_330)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 41.06/30.61  tff(c_777, plain, (![B_331]: (k9_subset_1('#skF_1', B_331, '#skF_4')=k3_xboole_0(B_331, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_763])).
% 41.06/30.61  tff(c_1186, plain, (![D_372, A_374, B_371, E_373, C_370, F_375]: (v1_funct_1(k1_tmap_1(A_374, B_371, C_370, D_372, E_373, F_375)) | ~m1_subset_1(F_375, k1_zfmisc_1(k2_zfmisc_1(D_372, B_371))) | ~v1_funct_2(F_375, D_372, B_371) | ~v1_funct_1(F_375) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_370, B_371))) | ~v1_funct_2(E_373, C_370, B_371) | ~v1_funct_1(E_373) | ~m1_subset_1(D_372, k1_zfmisc_1(A_374)) | v1_xboole_0(D_372) | ~m1_subset_1(C_370, k1_zfmisc_1(A_374)) | v1_xboole_0(C_370) | v1_xboole_0(B_371) | v1_xboole_0(A_374))), inference(cnfTransformation, [status(thm)], [f_176])).
% 41.06/30.61  tff(c_1191, plain, (![A_374, C_370, E_373]: (v1_funct_1(k1_tmap_1(A_374, '#skF_2', C_370, '#skF_4', E_373, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_370, '#skF_2'))) | ~v1_funct_2(E_373, C_370, '#skF_2') | ~v1_funct_1(E_373) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_374)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_370, k1_zfmisc_1(A_374)) | v1_xboole_0(C_370) | v1_xboole_0('#skF_2') | v1_xboole_0(A_374))), inference(resolution, [status(thm)], [c_54, c_1186])).
% 41.06/30.61  tff(c_1197, plain, (![A_374, C_370, E_373]: (v1_funct_1(k1_tmap_1(A_374, '#skF_2', C_370, '#skF_4', E_373, '#skF_6')) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(C_370, '#skF_2'))) | ~v1_funct_2(E_373, C_370, '#skF_2') | ~v1_funct_1(E_373) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_374)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_370, k1_zfmisc_1(A_374)) | v1_xboole_0(C_370) | v1_xboole_0('#skF_2') | v1_xboole_0(A_374))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1191])).
% 41.06/30.61  tff(c_1204, plain, (![A_376, C_377, E_378]: (v1_funct_1(k1_tmap_1(A_376, '#skF_2', C_377, '#skF_4', E_378, '#skF_6')) | ~m1_subset_1(E_378, k1_zfmisc_1(k2_zfmisc_1(C_377, '#skF_2'))) | ~v1_funct_2(E_378, C_377, '#skF_2') | ~v1_funct_1(E_378) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_376)) | ~m1_subset_1(C_377, k1_zfmisc_1(A_376)) | v1_xboole_0(C_377) | v1_xboole_0(A_376))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_1197])).
% 41.06/30.61  tff(c_1211, plain, (![A_376]: (v1_funct_1(k1_tmap_1(A_376, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_376)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_376)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_376))), inference(resolution, [status(thm)], [c_60, c_1204])).
% 41.06/30.61  tff(c_1219, plain, (![A_376]: (v1_funct_1(k1_tmap_1(A_376, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_376)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_376)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_376))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1211])).
% 41.06/30.61  tff(c_1557, plain, (![A_410]: (v1_funct_1(k1_tmap_1(A_410, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_410)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_410)) | v1_xboole_0(A_410))), inference(negUnitSimplification, [status(thm)], [c_74, c_1219])).
% 41.06/30.61  tff(c_1564, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_1557])).
% 41.06/30.61  tff(c_1568, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1564])).
% 41.06/30.61  tff(c_1569, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_1568])).
% 41.06/30.61  tff(c_1058, plain, (![A_358, B_359, C_360, D_361]: (k2_partfun1(A_358, B_359, C_360, D_361)=k7_relat_1(C_360, D_361) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))) | ~v1_funct_1(C_360))), inference(cnfTransformation, [status(thm)], [f_94])).
% 41.06/30.61  tff(c_1065, plain, (![D_361]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_361)=k7_relat_1('#skF_5', D_361) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_1058])).
% 41.06/30.61  tff(c_1072, plain, (![D_361]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_361)=k7_relat_1('#skF_5', D_361))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1065])).
% 41.06/30.61  tff(c_1063, plain, (![D_361]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_361)=k7_relat_1('#skF_6', D_361) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_1058])).
% 41.06/30.61  tff(c_1069, plain, (![D_361]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_361)=k7_relat_1('#skF_6', D_361))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1063])).
% 41.06/30.61  tff(c_1774, plain, (![F_449, C_450, E_447, D_451, B_448, A_446]: (k2_partfun1(k4_subset_1(A_446, C_450, D_451), B_448, k1_tmap_1(A_446, B_448, C_450, D_451, E_447, F_449), D_451)=F_449 | ~m1_subset_1(k1_tmap_1(A_446, B_448, C_450, D_451, E_447, F_449), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_446, C_450, D_451), B_448))) | ~v1_funct_2(k1_tmap_1(A_446, B_448, C_450, D_451, E_447, F_449), k4_subset_1(A_446, C_450, D_451), B_448) | ~v1_funct_1(k1_tmap_1(A_446, B_448, C_450, D_451, E_447, F_449)) | k2_partfun1(D_451, B_448, F_449, k9_subset_1(A_446, C_450, D_451))!=k2_partfun1(C_450, B_448, E_447, k9_subset_1(A_446, C_450, D_451)) | ~m1_subset_1(F_449, k1_zfmisc_1(k2_zfmisc_1(D_451, B_448))) | ~v1_funct_2(F_449, D_451, B_448) | ~v1_funct_1(F_449) | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(C_450, B_448))) | ~v1_funct_2(E_447, C_450, B_448) | ~v1_funct_1(E_447) | ~m1_subset_1(D_451, k1_zfmisc_1(A_446)) | v1_xboole_0(D_451) | ~m1_subset_1(C_450, k1_zfmisc_1(A_446)) | v1_xboole_0(C_450) | v1_xboole_0(B_448) | v1_xboole_0(A_446))), inference(cnfTransformation, [status(thm)], [f_142])).
% 41.06/30.61  tff(c_3207, plain, (![B_601, C_600, F_605, E_603, A_604, D_602]: (k2_partfun1(k4_subset_1(A_604, C_600, D_602), B_601, k1_tmap_1(A_604, B_601, C_600, D_602, E_603, F_605), D_602)=F_605 | ~v1_funct_2(k1_tmap_1(A_604, B_601, C_600, D_602, E_603, F_605), k4_subset_1(A_604, C_600, D_602), B_601) | ~v1_funct_1(k1_tmap_1(A_604, B_601, C_600, D_602, E_603, F_605)) | k2_partfun1(D_602, B_601, F_605, k9_subset_1(A_604, C_600, D_602))!=k2_partfun1(C_600, B_601, E_603, k9_subset_1(A_604, C_600, D_602)) | ~m1_subset_1(F_605, k1_zfmisc_1(k2_zfmisc_1(D_602, B_601))) | ~v1_funct_2(F_605, D_602, B_601) | ~v1_funct_1(F_605) | ~m1_subset_1(E_603, k1_zfmisc_1(k2_zfmisc_1(C_600, B_601))) | ~v1_funct_2(E_603, C_600, B_601) | ~v1_funct_1(E_603) | ~m1_subset_1(D_602, k1_zfmisc_1(A_604)) | v1_xboole_0(D_602) | ~m1_subset_1(C_600, k1_zfmisc_1(A_604)) | v1_xboole_0(C_600) | v1_xboole_0(B_601) | v1_xboole_0(A_604))), inference(resolution, [status(thm)], [c_46, c_1774])).
% 41.06/30.61  tff(c_5335, plain, (![E_824, D_823, B_822, A_825, F_826, C_821]: (k2_partfun1(k4_subset_1(A_825, C_821, D_823), B_822, k1_tmap_1(A_825, B_822, C_821, D_823, E_824, F_826), D_823)=F_826 | ~v1_funct_1(k1_tmap_1(A_825, B_822, C_821, D_823, E_824, F_826)) | k2_partfun1(D_823, B_822, F_826, k9_subset_1(A_825, C_821, D_823))!=k2_partfun1(C_821, B_822, E_824, k9_subset_1(A_825, C_821, D_823)) | ~m1_subset_1(F_826, k1_zfmisc_1(k2_zfmisc_1(D_823, B_822))) | ~v1_funct_2(F_826, D_823, B_822) | ~v1_funct_1(F_826) | ~m1_subset_1(E_824, k1_zfmisc_1(k2_zfmisc_1(C_821, B_822))) | ~v1_funct_2(E_824, C_821, B_822) | ~v1_funct_1(E_824) | ~m1_subset_1(D_823, k1_zfmisc_1(A_825)) | v1_xboole_0(D_823) | ~m1_subset_1(C_821, k1_zfmisc_1(A_825)) | v1_xboole_0(C_821) | v1_xboole_0(B_822) | v1_xboole_0(A_825))), inference(resolution, [status(thm)], [c_48, c_3207])).
% 41.06/30.61  tff(c_5342, plain, (![A_825, C_821, E_824]: (k2_partfun1(k4_subset_1(A_825, C_821, '#skF_4'), '#skF_2', k1_tmap_1(A_825, '#skF_2', C_821, '#skF_4', E_824, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_825, '#skF_2', C_821, '#skF_4', E_824, '#skF_6')) | k2_partfun1(C_821, '#skF_2', E_824, k9_subset_1(A_825, C_821, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_825, C_821, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_824, k1_zfmisc_1(k2_zfmisc_1(C_821, '#skF_2'))) | ~v1_funct_2(E_824, C_821, '#skF_2') | ~v1_funct_1(E_824) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_825)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_821, k1_zfmisc_1(A_825)) | v1_xboole_0(C_821) | v1_xboole_0('#skF_2') | v1_xboole_0(A_825))), inference(resolution, [status(thm)], [c_54, c_5335])).
% 41.06/30.61  tff(c_5349, plain, (![A_825, C_821, E_824]: (k2_partfun1(k4_subset_1(A_825, C_821, '#skF_4'), '#skF_2', k1_tmap_1(A_825, '#skF_2', C_821, '#skF_4', E_824, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_825, '#skF_2', C_821, '#skF_4', E_824, '#skF_6')) | k2_partfun1(C_821, '#skF_2', E_824, k9_subset_1(A_825, C_821, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_825, C_821, '#skF_4')) | ~m1_subset_1(E_824, k1_zfmisc_1(k2_zfmisc_1(C_821, '#skF_2'))) | ~v1_funct_2(E_824, C_821, '#skF_2') | ~v1_funct_1(E_824) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_825)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_821, k1_zfmisc_1(A_825)) | v1_xboole_0(C_821) | v1_xboole_0('#skF_2') | v1_xboole_0(A_825))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1069, c_5342])).
% 41.06/30.61  tff(c_8248, plain, (![A_1107, C_1108, E_1109]: (k2_partfun1(k4_subset_1(A_1107, C_1108, '#skF_4'), '#skF_2', k1_tmap_1(A_1107, '#skF_2', C_1108, '#skF_4', E_1109, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1107, '#skF_2', C_1108, '#skF_4', E_1109, '#skF_6')) | k2_partfun1(C_1108, '#skF_2', E_1109, k9_subset_1(A_1107, C_1108, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1107, C_1108, '#skF_4')) | ~m1_subset_1(E_1109, k1_zfmisc_1(k2_zfmisc_1(C_1108, '#skF_2'))) | ~v1_funct_2(E_1109, C_1108, '#skF_2') | ~v1_funct_1(E_1109) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1107)) | ~m1_subset_1(C_1108, k1_zfmisc_1(A_1107)) | v1_xboole_0(C_1108) | v1_xboole_0(A_1107))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_5349])).
% 41.06/30.61  tff(c_8258, plain, (![A_1107]: (k2_partfun1(k4_subset_1(A_1107, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1107, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1107, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1107, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1107, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1107)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1107)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1107))), inference(resolution, [status(thm)], [c_60, c_8248])).
% 41.06/30.61  tff(c_8269, plain, (![A_1107]: (k2_partfun1(k4_subset_1(A_1107, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1107, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1107, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1107, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1107, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1107)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1107)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1107))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1072, c_8258])).
% 41.06/30.61  tff(c_13996, plain, (![A_1591]: (k2_partfun1(k4_subset_1(A_1591, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1591, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1591, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1591, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1591, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1591)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1591)) | v1_xboole_0(A_1591))), inference(negUnitSimplification, [status(thm)], [c_74, c_8269])).
% 41.06/30.61  tff(c_144, plain, (![C_238, A_239, B_240]: (v1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 41.06/30.61  tff(c_157, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_144])).
% 41.06/30.61  tff(c_185, plain, (![B_248, A_249]: (v4_relat_1(B_248, A_249) | ~r1_tarski(k1_relat_1(B_248), A_249) | ~v1_relat_1(B_248))), inference(cnfTransformation, [status(thm)], [f_60])).
% 41.06/30.61  tff(c_194, plain, (![B_248]: (v4_relat_1(B_248, k1_relat_1(B_248)) | ~v1_relat_1(B_248))), inference(resolution, [status(thm)], [c_10, c_185])).
% 41.06/30.61  tff(c_301, plain, (![C_268, A_269, B_270]: (v4_relat_1(C_268, A_269) | ~m1_subset_1(C_268, k1_zfmisc_1(B_270)) | ~v4_relat_1(B_270, A_269) | ~v1_relat_1(B_270))), inference(cnfTransformation, [status(thm)], [f_54])).
% 41.06/30.61  tff(c_307, plain, (![A_269]: (v4_relat_1('#skF_5', A_269) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_269) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_60, c_301])).
% 41.06/30.61  tff(c_345, plain, (![A_272]: (v4_relat_1('#skF_5', A_272) | ~v4_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'), A_272))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_307])).
% 41.06/30.61  tff(c_349, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_194, c_345])).
% 41.06/30.61  tff(c_352, plain, (v4_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_349])).
% 41.06/30.61  tff(c_355, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_352, c_30])).
% 41.06/30.61  tff(c_358, plain, (k7_relat_1('#skF_5', k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_355])).
% 41.06/30.61  tff(c_362, plain, (![B_20]: (k7_relat_1('#skF_5', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_20) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_358, c_28])).
% 41.06/30.61  tff(c_543, plain, (![B_294]: (k7_relat_1('#skF_5', B_294)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2')), B_294))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_362])).
% 41.06/30.61  tff(c_558, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_543])).
% 41.06/30.61  tff(c_156, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_144])).
% 41.06/30.61  tff(c_305, plain, (![A_269]: (v4_relat_1('#skF_6', A_269) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_269) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_301])).
% 41.06/30.61  tff(c_321, plain, (![A_271]: (v4_relat_1('#skF_6', A_271) | ~v4_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'), A_271))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_305])).
% 41.06/30.61  tff(c_325, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_194, c_321])).
% 41.06/30.61  tff(c_328, plain, (v4_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_325])).
% 41.06/30.61  tff(c_331, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_328, c_30])).
% 41.06/30.61  tff(c_334, plain, (k7_relat_1('#skF_6', k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_331])).
% 41.06/30.61  tff(c_338, plain, (![B_20]: (k7_relat_1('#skF_6', B_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_20) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_334, c_28])).
% 41.06/30.61  tff(c_443, plain, (![B_285]: (k7_relat_1('#skF_6', B_285)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2')), B_285))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_338])).
% 41.06/30.61  tff(c_458, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_443])).
% 41.06/30.61  tff(c_211, plain, (![A_252, B_253]: (r1_xboole_0(A_252, B_253) | ~r1_subset_1(A_252, B_253) | v1_xboole_0(B_253) | v1_xboole_0(A_252))), inference(cnfTransformation, [status(thm)], [f_84])).
% 41.06/30.61  tff(c_585, plain, (![A_298, B_299]: (k3_xboole_0(A_298, B_299)=k1_xboole_0 | ~r1_subset_1(A_298, B_299) | v1_xboole_0(B_299) | v1_xboole_0(A_298))), inference(resolution, [status(thm)], [c_211, c_2])).
% 41.06/30.61  tff(c_588, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_585])).
% 41.06/30.61  tff(c_591, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_70, c_588])).
% 41.06/30.61  tff(c_368, plain, (![A_273, B_274, C_275, D_276]: (k2_partfun1(A_273, B_274, C_275, D_276)=k7_relat_1(C_275, D_276) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))) | ~v1_funct_1(C_275))), inference(cnfTransformation, [status(thm)], [f_94])).
% 41.06/30.61  tff(c_375, plain, (![D_276]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_276)=k7_relat_1('#skF_5', D_276) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_368])).
% 41.06/30.61  tff(c_382, plain, (![D_276]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_276)=k7_relat_1('#skF_5', D_276))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_375])).
% 41.06/30.61  tff(c_373, plain, (![D_276]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_276)=k7_relat_1('#skF_6', D_276) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_368])).
% 41.06/30.61  tff(c_379, plain, (![D_276]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_276)=k7_relat_1('#skF_6', D_276))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_373])).
% 41.06/30.61  tff(c_257, plain, (![A_262, B_263, C_264]: (k9_subset_1(A_262, B_263, C_264)=k3_xboole_0(B_263, C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(A_262)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 41.06/30.61  tff(c_271, plain, (![B_263]: (k9_subset_1('#skF_1', B_263, '#skF_4')=k3_xboole_0(B_263, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_257])).
% 41.06/30.61  tff(c_52, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.06/30.61  tff(c_96, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 41.06/30.61  tff(c_273, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_271, c_96])).
% 41.06/30.61  tff(c_410, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_379, c_273])).
% 41.06/30.61  tff(c_592, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_591, c_591, c_410])).
% 41.06/30.61  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_558, c_458, c_592])).
% 41.06/30.61  tff(c_596, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 41.06/30.61  tff(c_725, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_596])).
% 41.06/30.61  tff(c_14028, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13996, c_725])).
% 41.06/30.61  tff(c_14072, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1034, c_946, c_859, c_859, c_777, c_777, c_1569, c_14028])).
% 41.06/30.61  tff(c_14074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_14072])).
% 41.06/30.61  tff(c_14075, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_596])).
% 41.06/30.61  tff(c_23390, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23367, c_14075])).
% 41.06/30.61  tff(c_23426, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_14389, c_14301, c_14205, c_14205, c_14128, c_14128, c_15186, c_23390])).
% 41.06/30.61  tff(c_23428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_23426])).
% 41.06/30.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.06/30.61  
% 41.06/30.61  Inference rules
% 41.06/30.61  ----------------------
% 41.06/30.61  #Ref     : 0
% 41.06/30.61  #Sup     : 5187
% 41.06/30.61  #Fact    : 0
% 41.06/30.61  #Define  : 0
% 41.06/30.61  #Split   : 126
% 41.06/30.61  #Chain   : 0
% 41.06/30.61  #Close   : 0
% 41.06/30.61  
% 41.06/30.61  Ordering : KBO
% 41.06/30.61  
% 41.06/30.61  Simplification rules
% 41.06/30.61  ----------------------
% 41.06/30.61  #Subsume      : 2010
% 41.06/30.61  #Demod        : 3690
% 41.06/30.61  #Tautology    : 991
% 41.06/30.61  #SimpNegUnit  : 831
% 41.06/30.61  #BackRed      : 6
% 41.06/30.61  
% 41.06/30.61  #Partial instantiations: 0
% 41.06/30.61  #Strategies tried      : 1
% 41.06/30.61  
% 41.06/30.61  Timing (in seconds)
% 41.06/30.61  ----------------------
% 41.06/30.61  Preprocessing        : 0.45
% 41.06/30.61  Parsing              : 0.22
% 41.06/30.61  CNF conversion       : 0.07
% 41.06/30.61  Main loop            : 29.34
% 41.06/30.61  Inferencing          : 2.52
% 41.06/30.61  Reduction            : 3.37
% 41.06/30.61  Demodulation         : 2.55
% 41.06/30.61  BG Simplification    : 0.26
% 41.06/30.61  Subsumption          : 22.80
% 41.06/30.61  Abstraction          : 0.43
% 41.06/30.61  MUC search           : 0.00
% 41.06/30.61  Cooper               : 0.00
% 41.06/30.61  Total                : 29.86
% 41.06/30.61  Index Insertion      : 0.00
% 41.06/30.61  Index Deletion       : 0.00
% 41.06/30.61  Index Matching       : 0.00
% 41.06/30.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
