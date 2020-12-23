%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:18 EST 2020

% Result     : Theorem 45.50s
% Output     : CNFRefutation 45.65s
% Verified   : 
% Statistics : Number of formulae       :  385 (4286 expanded)
%              Number of leaves         :   50 (1494 expanded)
%              Depth                    :   16
%              Number of atoms          : 1084 (15605 expanded)
%              Number of equality atoms :  350 (4144 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_240,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_198,axiom,(
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

tff(f_164,axiom,(
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

tff(c_94,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [A_237,B_238] : v1_relat_1(k2_zfmisc_1(A_237,B_238)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_104])).

tff(c_14,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125191,plain,(
    ! [C_7681,A_7682,B_7683] :
      ( v4_relat_1(C_7681,A_7682)
      | ~ m1_subset_1(C_7681,k1_zfmisc_1(k2_zfmisc_1(A_7682,B_7683))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_125274,plain,(
    ! [A_7694,A_7695,B_7696] :
      ( v4_relat_1(A_7694,A_7695)
      | ~ r1_tarski(A_7694,k2_zfmisc_1(A_7695,B_7696)) ) ),
    inference(resolution,[status(thm)],[c_28,c_125191])).

tff(c_125296,plain,(
    ! [A_7697,B_7698] : v4_relat_1(k2_zfmisc_1(A_7697,B_7698),A_7697) ),
    inference(resolution,[status(thm)],[c_14,c_125274])).

tff(c_125317,plain,(
    ! [A_7699] : v4_relat_1(k1_xboole_0,A_7699) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_125296])).

tff(c_36,plain,(
    ! [B_28,A_27] :
      ( k7_relat_1(B_28,A_27) = B_28
      | ~ v4_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_125320,plain,(
    ! [A_7699] :
      ( k7_relat_1(k1_xboole_0,A_7699) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_125317,c_36])).

tff(c_125323,plain,(
    ! [A_7699] : k7_relat_1(k1_xboole_0,A_7699) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_125320])).

tff(c_125429,plain,(
    ! [B_7712,A_7713] :
      ( r1_xboole_0(k1_relat_1(B_7712),A_7713)
      | k7_relat_1(B_7712,A_7713) != k1_xboole_0
      | ~ v1_relat_1(B_7712) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125984,plain,(
    ! [A_7754,B_7755] :
      ( r1_xboole_0(A_7754,k1_relat_1(B_7755))
      | k7_relat_1(B_7755,A_7754) != k1_xboole_0
      | ~ v1_relat_1(B_7755) ) ),
    inference(resolution,[status(thm)],[c_125429,c_8])).

tff(c_30,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_125299,plain,(
    ! [A_7697,B_7698] :
      ( k7_relat_1(k2_zfmisc_1(A_7697,B_7698),A_7697) = k2_zfmisc_1(A_7697,B_7698)
      | ~ v1_relat_1(k2_zfmisc_1(A_7697,B_7698)) ) ),
    inference(resolution,[status(thm)],[c_125296,c_36])).

tff(c_125308,plain,(
    ! [A_7697,B_7698] : k7_relat_1(k2_zfmisc_1(A_7697,B_7698),A_7697) = k2_zfmisc_1(A_7697,B_7698) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125299])).

tff(c_125505,plain,(
    ! [C_7718,A_7719,B_7720] :
      ( k7_relat_1(k7_relat_1(C_7718,A_7719),B_7720) = k1_xboole_0
      | ~ r1_xboole_0(A_7719,B_7720)
      | ~ v1_relat_1(C_7718) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_125520,plain,(
    ! [A_7697,B_7698,B_7720] :
      ( k7_relat_1(k2_zfmisc_1(A_7697,B_7698),B_7720) = k1_xboole_0
      | ~ r1_xboole_0(A_7697,B_7720)
      | ~ v1_relat_1(k2_zfmisc_1(A_7697,B_7698)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125308,c_125505])).

tff(c_125922,plain,(
    ! [A_7745,B_7746,B_7747] :
      ( k7_relat_1(k2_zfmisc_1(A_7745,B_7746),B_7747) = k1_xboole_0
      | ~ r1_xboole_0(A_7745,B_7747) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125520])).

tff(c_125932,plain,(
    ! [B_7747,B_7746] :
      ( k2_zfmisc_1(B_7747,B_7746) = k1_xboole_0
      | ~ r1_xboole_0(B_7747,B_7747) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125922,c_125308])).

tff(c_127121,plain,(
    ! [B_7852,B_7853] :
      ( k2_zfmisc_1(k1_relat_1(B_7852),B_7853) = k1_xboole_0
      | k7_relat_1(B_7852,k1_relat_1(B_7852)) != k1_xboole_0
      | ~ v1_relat_1(B_7852) ) ),
    inference(resolution,[status(thm)],[c_125984,c_125932])).

tff(c_127151,plain,(
    ! [B_7853] :
      ( k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_7853) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125323,c_127121])).

tff(c_127178,plain,(
    ! [B_7854] : k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_7854) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_127151])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127243,plain,(
    ! [B_7854] :
      ( k1_xboole_0 = B_7854
      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127178,c_16])).

tff(c_127249,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_127243])).

tff(c_125404,plain,(
    ! [B_7710,A_7711] :
      ( k3_xboole_0(k1_relat_1(B_7710),A_7711) = k1_relat_1(k7_relat_1(B_7710,A_7711))
      | ~ v1_relat_1(B_7710) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_160,plain,(
    ! [A_246,B_247] :
      ( r1_xboole_0(A_246,B_247)
      | k3_xboole_0(A_246,B_247) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3488,plain,(
    ! [B_3130,A_3131] :
      ( r1_xboole_0(B_3130,A_3131)
      | k3_xboole_0(A_3131,B_3130) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_160,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3494,plain,(
    ! [B_3130,A_3131] :
      ( k3_xboole_0(B_3130,A_3131) = k1_xboole_0
      | k3_xboole_0(A_3131,B_3130) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3488,c_4])).

tff(c_125409,plain,(
    ! [A_7711,B_7710] :
      ( k3_xboole_0(A_7711,k1_relat_1(B_7710)) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_7710,A_7711)) != k1_xboole_0
      | ~ v1_relat_1(B_7710) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125404,c_3494])).

tff(c_127257,plain,(
    ! [A_7711] :
      ( k3_xboole_0(A_7711,k1_xboole_0) = k1_xboole_0
      | k1_relat_1(k7_relat_1(k1_xboole_0,A_7711)) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127249,c_125409])).

tff(c_127302,plain,(
    ! [A_7711] : k3_xboole_0(A_7711,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_127249,c_125323,c_127257])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_3496,plain,(
    ! [C_3132,A_3133,B_3134] :
      ( v1_relat_1(C_3132)
      | ~ m1_subset_1(C_3132,k1_zfmisc_1(k2_zfmisc_1(A_3133,B_3134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3513,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_3496])).

tff(c_125210,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_125191])).

tff(c_125227,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_125210,c_36])).

tff(c_125230,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3513,c_125227])).

tff(c_125526,plain,(
    ! [B_7720] :
      ( k7_relat_1('#skF_6',B_7720) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_7720)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125230,c_125505])).

tff(c_125542,plain,(
    ! [B_7721] :
      ( k7_relat_1('#skF_6',B_7721) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_7721) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3513,c_125526])).

tff(c_125566,plain,(
    ! [B_4] :
      ( k7_relat_1('#skF_6',B_4) = k1_xboole_0
      | k3_xboole_0('#skF_4',B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_125542])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_3512,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_3496])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_125211,plain,(
    ! [A_7684,B_7685] :
      ( r1_xboole_0(A_7684,B_7685)
      | ~ r1_subset_1(A_7684,B_7685)
      | v1_xboole_0(B_7685)
      | v1_xboole_0(A_7684) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_126195,plain,(
    ! [A_7775,B_7776] :
      ( k3_xboole_0(A_7775,B_7776) = k1_xboole_0
      | ~ r1_subset_1(A_7775,B_7776)
      | v1_xboole_0(B_7776)
      | v1_xboole_0(A_7775) ) ),
    inference(resolution,[status(thm)],[c_125211,c_4])).

tff(c_126201,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_126195])).

tff(c_126206,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_126201])).

tff(c_126207,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_126206])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_126019,plain,(
    ! [A_7756,B_7757,C_7758,D_7759] :
      ( k2_partfun1(A_7756,B_7757,C_7758,D_7759) = k7_relat_1(C_7758,D_7759)
      | ~ m1_subset_1(C_7758,k1_zfmisc_1(k2_zfmisc_1(A_7756,B_7757)))
      | ~ v1_funct_1(C_7758) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_126026,plain,(
    ! [D_7759] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_7759) = k7_relat_1('#skF_6',D_7759)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_126019])).

tff(c_126037,plain,(
    ! [D_7759] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_7759) = k7_relat_1('#skF_6',D_7759) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_126026])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_126024,plain,(
    ! [D_7759] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_7759) = k7_relat_1('#skF_5',D_7759)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_126019])).

tff(c_126034,plain,(
    ! [D_7759] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_7759) = k7_relat_1('#skF_5',D_7759) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_126024])).

tff(c_125659,plain,(
    ! [A_7726,B_7727,C_7728] :
      ( k9_subset_1(A_7726,B_7727,C_7728) = k3_xboole_0(B_7727,C_7728)
      | ~ m1_subset_1(C_7728,k1_zfmisc_1(A_7726)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125674,plain,(
    ! [B_7727] : k9_subset_1('#skF_1',B_7727,'#skF_4') = k3_xboole_0(B_7727,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_125659])).

tff(c_210,plain,(
    ! [C_256,A_257,B_258] :
      ( v1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_227,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_210])).

tff(c_226,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_210])).

tff(c_347,plain,(
    ! [C_283,A_284,B_285] :
      ( v4_relat_1(C_283,A_284)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_405,plain,(
    ! [A_292,A_293,B_294] :
      ( v4_relat_1(A_292,A_293)
      | ~ r1_tarski(A_292,k2_zfmisc_1(A_293,B_294)) ) ),
    inference(resolution,[status(thm)],[c_28,c_347])).

tff(c_427,plain,(
    ! [A_295,B_296] : v4_relat_1(k2_zfmisc_1(A_295,B_296),A_295) ),
    inference(resolution,[status(thm)],[c_14,c_405])).

tff(c_448,plain,(
    ! [A_297] : v4_relat_1(k1_xboole_0,A_297) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_427])).

tff(c_451,plain,(
    ! [A_297] :
      ( k7_relat_1(k1_xboole_0,A_297) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_448,c_36])).

tff(c_454,plain,(
    ! [A_297] : k7_relat_1(k1_xboole_0,A_297) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_451])).

tff(c_42,plain,(
    ! [B_32,A_31] :
      ( r1_xboole_0(k1_relat_1(B_32),A_31)
      | k7_relat_1(B_32,A_31) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_430,plain,(
    ! [A_295,B_296] :
      ( k7_relat_1(k2_zfmisc_1(A_295,B_296),A_295) = k2_zfmisc_1(A_295,B_296)
      | ~ v1_relat_1(k2_zfmisc_1(A_295,B_296)) ) ),
    inference(resolution,[status(thm)],[c_427,c_36])).

tff(c_439,plain,(
    ! [A_295,B_296] : k7_relat_1(k2_zfmisc_1(A_295,B_296),A_295) = k2_zfmisc_1(A_295,B_296) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_430])).

tff(c_741,plain,(
    ! [C_331,A_332,B_333] :
      ( k7_relat_1(k7_relat_1(C_331,A_332),B_333) = k1_xboole_0
      | ~ r1_xboole_0(A_332,B_333)
      | ~ v1_relat_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_756,plain,(
    ! [A_295,B_296,B_333] :
      ( k7_relat_1(k2_zfmisc_1(A_295,B_296),B_333) = k1_xboole_0
      | ~ r1_xboole_0(A_295,B_333)
      | ~ v1_relat_1(k2_zfmisc_1(A_295,B_296)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_741])).

tff(c_1191,plain,(
    ! [A_357,B_358,B_359] :
      ( k7_relat_1(k2_zfmisc_1(A_357,B_358),B_359) = k1_xboole_0
      | ~ r1_xboole_0(A_357,B_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_756])).

tff(c_1220,plain,(
    ! [B_360,B_361] :
      ( k2_zfmisc_1(B_360,B_361) = k1_xboole_0
      | ~ r1_xboole_0(B_360,B_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1191,c_439])).

tff(c_2116,plain,(
    ! [B_443,B_444] :
      ( k2_zfmisc_1(k1_relat_1(B_443),B_444) = k1_xboole_0
      | k7_relat_1(B_443,k1_relat_1(B_443)) != k1_xboole_0
      | ~ v1_relat_1(B_443) ) ),
    inference(resolution,[status(thm)],[c_42,c_1220])).

tff(c_2143,plain,(
    ! [B_444] :
      ( k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_444) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_2116])).

tff(c_2169,plain,(
    ! [B_445] : k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_445) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2143])).

tff(c_2234,plain,(
    ! [B_445] :
      ( k1_xboole_0 = B_445
      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2169,c_16])).

tff(c_2244,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2234])).

tff(c_397,plain,(
    ! [B_290,A_291] :
      ( r1_xboole_0(k1_relat_1(B_290),A_291)
      | k7_relat_1(B_290,A_291) != k1_xboole_0
      | ~ v1_relat_1(B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_404,plain,(
    ! [A_291,B_290] :
      ( r1_xboole_0(A_291,k1_relat_1(B_290))
      | k7_relat_1(B_290,A_291) != k1_xboole_0
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_397,c_8])).

tff(c_366,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_347])).

tff(c_375,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_366,c_36])).

tff(c_378,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_375])).

tff(c_762,plain,(
    ! [B_333] :
      ( k7_relat_1('#skF_6',B_333) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_333)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_741])).

tff(c_778,plain,(
    ! [B_334] :
      ( k7_relat_1('#skF_6',B_334) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_762])).

tff(c_802,plain,(
    ! [B_290] :
      ( k7_relat_1('#skF_6',k1_relat_1(B_290)) = k1_xboole_0
      | k7_relat_1(B_290,'#skF_4') != k1_xboole_0
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_404,c_778])).

tff(c_2261,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_802])).

tff(c_2303,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_454,c_2261])).

tff(c_365,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_347])).

tff(c_369,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_365,c_36])).

tff(c_372,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_369])).

tff(c_765,plain,(
    ! [B_333] :
      ( k7_relat_1('#skF_5',B_333) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_333)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_741])).

tff(c_808,plain,(
    ! [B_335] :
      ( k7_relat_1('#skF_5',B_335) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_765])).

tff(c_832,plain,(
    ! [B_290] :
      ( k7_relat_1('#skF_5',k1_relat_1(B_290)) = k1_xboole_0
      | k7_relat_1(B_290,'#skF_3') != k1_xboole_0
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_404,c_808])).

tff(c_2258,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_832])).

tff(c_2301,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_454,c_2258])).

tff(c_520,plain,(
    ! [A_307,B_308] :
      ( r1_xboole_0(A_307,B_308)
      | ~ r1_subset_1(A_307,B_308)
      | v1_xboole_0(B_308)
      | v1_xboole_0(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1404,plain,(
    ! [A_389,B_390] :
      ( k3_xboole_0(A_389,B_390) = k1_xboole_0
      | ~ r1_subset_1(A_389,B_390)
      | v1_xboole_0(B_390)
      | v1_xboole_0(A_389) ) ),
    inference(resolution,[status(thm)],[c_520,c_4])).

tff(c_1410,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1404])).

tff(c_1415,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1410])).

tff(c_1416,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_1415])).

tff(c_1092,plain,(
    ! [A_348,B_349,C_350,D_351] :
      ( k2_partfun1(A_348,B_349,C_350,D_351) = k7_relat_1(C_350,D_351)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_348,B_349)))
      | ~ v1_funct_1(C_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1099,plain,(
    ! [D_351] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_351) = k7_relat_1('#skF_6',D_351)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_1092])).

tff(c_1110,plain,(
    ! [D_351] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_351) = k7_relat_1('#skF_6',D_351) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1099])).

tff(c_1097,plain,(
    ! [D_351] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_351) = k7_relat_1('#skF_5',D_351)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_1092])).

tff(c_1107,plain,(
    ! [D_351] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_351) = k7_relat_1('#skF_5',D_351) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1097])).

tff(c_658,plain,(
    ! [A_319,B_320,C_321] :
      ( k9_subset_1(A_319,B_320,C_321) = k3_xboole_0(B_320,C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(A_319)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_673,plain,(
    ! [B_320] : k9_subset_1('#skF_1',B_320,'#skF_4') = k3_xboole_0(B_320,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_658])).

tff(c_68,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_201,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_683,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_673,c_201])).

tff(c_684,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_683])).

tff(c_2741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2303,c_2301,c_1416,c_1416,c_1110,c_1107,c_684])).

tff(c_2744,plain,(
    ! [B_468] : k1_xboole_0 = B_468 ),
    inference(splitRight,[status(thm)],[c_2234])).

tff(c_557,plain,(
    ! [B_311,A_312] :
      ( k3_xboole_0(k1_relat_1(B_311),A_312) = k1_relat_1(k7_relat_1(B_311,A_312))
      | ~ v1_relat_1(B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_625,plain,(
    ! [A_317,B_318] :
      ( k3_xboole_0(A_317,k1_relat_1(B_318)) = k1_relat_1(k7_relat_1(B_318,A_317))
      | ~ v1_relat_1(B_318) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_2])).

tff(c_202,plain,(
    ! [B_254,A_255] :
      ( r1_xboole_0(B_254,A_255)
      | k3_xboole_0(A_255,B_254) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_160,c_8])).

tff(c_208,plain,(
    ! [B_254,A_255] :
      ( k3_xboole_0(B_254,A_255) = k1_xboole_0
      | k3_xboole_0(A_255,B_254) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_202,c_4])).

tff(c_1836,plain,(
    ! [B_426,A_427] :
      ( k3_xboole_0(k1_relat_1(B_426),A_427) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_426,A_427)) != k1_xboole_0
      | ~ v1_relat_1(B_426) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_208])).

tff(c_537,plain,(
    ! [B_309,A_310] :
      ( k7_relat_1(B_309,A_310) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_309),A_310)
      | ~ v1_relat_1(B_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_556,plain,(
    ! [B_309,B_4] :
      ( k7_relat_1(B_309,B_4) = k1_xboole_0
      | ~ v1_relat_1(B_309)
      | k3_xboole_0(k1_relat_1(B_309),B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_537])).

tff(c_1907,plain,(
    ! [B_428,A_429] :
      ( k7_relat_1(B_428,A_429) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_428,A_429)) != k1_xboole_0
      | ~ v1_relat_1(B_428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1836,c_556])).

tff(c_1949,plain,
    ( k7_relat_1('#skF_5','#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_1907])).

tff(c_1975,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_372,c_1949])).

tff(c_2003,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1975])).

tff(c_3036,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2744,c_2003])).

tff(c_3037,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1975])).

tff(c_3038,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1975])).

tff(c_3100,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3037,c_3038])).

tff(c_3077,plain,(
    ! [A_297] : k7_relat_1('#skF_5',A_297) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3037,c_3037,c_454])).

tff(c_504,plain,(
    ! [A_305,B_306] :
      ( k7_relat_1(A_305,B_306) = k1_xboole_0
      | ~ r1_xboole_0(B_306,k1_relat_1(A_305))
      | ~ v1_relat_1(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_517,plain,(
    ! [A_305,B_32] :
      ( k7_relat_1(A_305,k1_relat_1(B_32)) = k1_xboole_0
      | ~ v1_relat_1(A_305)
      | k7_relat_1(B_32,k1_relat_1(A_305)) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_42,c_504])).

tff(c_3375,plain,(
    ! [A_3116,B_3117] :
      ( k7_relat_1(A_3116,k1_relat_1(B_3117)) = '#skF_5'
      | ~ v1_relat_1(A_3116)
      | k7_relat_1(B_3117,k1_relat_1(A_3116)) != '#skF_5'
      | ~ v1_relat_1(B_3117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3037,c_3037,c_517])).

tff(c_3378,plain,(
    ! [A_3116] :
      ( k7_relat_1(A_3116,k1_relat_1('#skF_5')) = '#skF_5'
      | ~ v1_relat_1(A_3116)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3077,c_3375])).

tff(c_3391,plain,(
    ! [A_3118] :
      ( k7_relat_1(A_3118,'#skF_5') = '#skF_5'
      | ~ v1_relat_1(A_3118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_3100,c_3378])).

tff(c_3401,plain,(
    k7_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_227,c_3391])).

tff(c_3196,plain,(
    ! [D_351] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_351) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_1107])).

tff(c_3049,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3037,c_1416])).

tff(c_3485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_3196,c_3049,c_3049,c_1110,c_684])).

tff(c_3487,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_125685,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125674,c_125674,c_3487])).

tff(c_125686,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_125685])).

tff(c_126038,plain,(
    k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) = k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126034,c_125686])).

tff(c_126057,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k7_relat_1('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126037,c_126038])).

tff(c_126208,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126207,c_126207,c_126057])).

tff(c_125450,plain,(
    ! [A_7714,B_7715] :
      ( k3_xboole_0(A_7714,k1_relat_1(B_7715)) = k1_relat_1(k7_relat_1(B_7715,A_7714))
      | ~ v1_relat_1(B_7715) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125404])).

tff(c_126792,plain,(
    ! [B_7828,A_7829] :
      ( k3_xboole_0(k1_relat_1(B_7828),A_7829) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_7828,A_7829)) != k1_xboole_0
      | ~ v1_relat_1(B_7828) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125450,c_3494])).

tff(c_125388,plain,(
    ! [B_7708,A_7709] :
      ( k7_relat_1(B_7708,A_7709) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_7708),A_7709)
      | ~ v1_relat_1(B_7708) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_125403,plain,(
    ! [B_7708,B_4] :
      ( k7_relat_1(B_7708,B_4) = k1_xboole_0
      | ~ v1_relat_1(B_7708)
      | k3_xboole_0(k1_relat_1(B_7708),B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_125388])).

tff(c_126863,plain,(
    ! [B_7830,A_7831] :
      ( k7_relat_1(B_7830,A_7831) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_7830,A_7831)) != k1_xboole_0
      | ~ v1_relat_1(B_7830) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126792,c_125403])).

tff(c_126875,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_126208,c_126863])).

tff(c_126917,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_126208,c_126875])).

tff(c_126968,plain,(
    k1_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126917])).

tff(c_126986,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k3_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_125566,c_126968])).

tff(c_126991,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126986])).

tff(c_127452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127302,c_126991])).

tff(c_127455,plain,(
    ! [B_7865] : k1_xboole_0 = B_7865 ),
    inference(splitRight,[status(thm)],[c_127243])).

tff(c_127815,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_127455,c_126991])).

tff(c_127816,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126986])).

tff(c_125951,plain,(
    ! [B_7748,B_7749] :
      ( k2_zfmisc_1(B_7748,B_7749) = k1_xboole_0
      | ~ r1_xboole_0(B_7748,B_7748) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125922,c_125308])).

tff(c_127981,plain,(
    ! [B_10692,B_10693] :
      ( k2_zfmisc_1(k1_relat_1(B_10692),B_10693) = k1_xboole_0
      | k7_relat_1(B_10692,k1_relat_1(B_10692)) != k1_xboole_0
      | ~ v1_relat_1(B_10692) ) ),
    inference(resolution,[status(thm)],[c_42,c_125951])).

tff(c_128011,plain,(
    ! [B_10693] :
      ( k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_10693) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125323,c_127981])).

tff(c_128038,plain,(
    ! [B_10694] : k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_10694) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_128011])).

tff(c_128086,plain,(
    ! [B_10694] :
      ( k1_xboole_0 = B_10694
      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128038,c_16])).

tff(c_128110,plain,(
    ! [B_10695] : k1_xboole_0 = B_10695 ),
    inference(negUnitSimplification,[status(thm)],[c_127816,c_128086])).

tff(c_128470,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_128110,c_127816])).

tff(c_128471,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126917])).

tff(c_128472,plain,(
    k1_relat_1(k7_relat_1('#skF_6',k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126917])).

tff(c_128551,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128471,c_128472])).

tff(c_126352,plain,(
    ! [B_7791,A_7792] :
      ( k3_xboole_0(k1_relat_1(B_7791),A_7792) = k1_xboole_0
      | k7_relat_1(B_7791,A_7792) != k1_xboole_0
      | ~ v1_relat_1(B_7791) ) ),
    inference(resolution,[status(thm)],[c_125429,c_4])).

tff(c_126394,plain,(
    ! [B_2,B_7791] :
      ( k3_xboole_0(B_2,k1_relat_1(B_7791)) = k1_xboole_0
      | k7_relat_1(B_7791,B_2) != k1_xboole_0
      | ~ v1_relat_1(B_7791) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126352])).

tff(c_128564,plain,(
    ! [B_2] :
      ( k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0
      | k7_relat_1(k1_xboole_0,B_2) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128551,c_126394])).

tff(c_128601,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_125323,c_128564])).

tff(c_167,plain,(
    ! [B_247,A_246] :
      ( r1_xboole_0(B_247,A_246)
      | k3_xboole_0(A_246,B_247) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_160,c_8])).

tff(c_125209,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_125191])).

tff(c_125221,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_125209,c_36])).

tff(c_125224,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_125221])).

tff(c_125529,plain,(
    ! [B_7720] :
      ( k7_relat_1('#skF_5',B_7720) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_7720)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125224,c_125505])).

tff(c_125567,plain,(
    ! [B_7722] :
      ( k7_relat_1('#skF_5',B_7722) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_7722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_125529])).

tff(c_125590,plain,(
    ! [A_246] :
      ( k7_relat_1('#skF_5',A_246) = k1_xboole_0
      | k3_xboole_0(A_246,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_167,c_125567])).

tff(c_126244,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_126208,c_125590])).

tff(c_126259,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_126244])).

tff(c_126264,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126259])).

tff(c_128746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128601,c_126264])).

tff(c_128747,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126259])).

tff(c_125673,plain,(
    ! [B_7727] : k9_subset_1('#skF_1',B_7727,'#skF_3') = k3_xboole_0(B_7727,'#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_125659])).

tff(c_125778,plain,(
    ! [A_7735,C_7736,B_7737] :
      ( k9_subset_1(A_7735,C_7736,B_7737) = k9_subset_1(A_7735,B_7737,C_7736)
      | ~ m1_subset_1(C_7736,k1_zfmisc_1(A_7735)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125786,plain,(
    ! [B_7737] : k9_subset_1('#skF_1',B_7737,'#skF_3') = k9_subset_1('#skF_1','#skF_3',B_7737) ),
    inference(resolution,[status(thm)],[c_88,c_125778])).

tff(c_125795,plain,(
    ! [B_7737] : k9_subset_1('#skF_1','#skF_3',B_7737) = k3_xboole_0(B_7737,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125673,c_125786])).

tff(c_128749,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128747,c_126208])).

tff(c_78,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_126173,plain,(
    ! [F_7773,E_7770,D_7771,A_7772,C_7774,B_7769] :
      ( v1_funct_1(k1_tmap_1(A_7772,B_7769,C_7774,D_7771,E_7770,F_7773))
      | ~ m1_subset_1(F_7773,k1_zfmisc_1(k2_zfmisc_1(D_7771,B_7769)))
      | ~ v1_funct_2(F_7773,D_7771,B_7769)
      | ~ v1_funct_1(F_7773)
      | ~ m1_subset_1(E_7770,k1_zfmisc_1(k2_zfmisc_1(C_7774,B_7769)))
      | ~ v1_funct_2(E_7770,C_7774,B_7769)
      | ~ v1_funct_1(E_7770)
      | ~ m1_subset_1(D_7771,k1_zfmisc_1(A_7772))
      | v1_xboole_0(D_7771)
      | ~ m1_subset_1(C_7774,k1_zfmisc_1(A_7772))
      | v1_xboole_0(C_7774)
      | v1_xboole_0(B_7769)
      | v1_xboole_0(A_7772) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_126180,plain,(
    ! [A_7772,C_7774,E_7770] :
      ( v1_funct_1(k1_tmap_1(A_7772,'#skF_2',C_7774,'#skF_4',E_7770,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_7770,k1_zfmisc_1(k2_zfmisc_1(C_7774,'#skF_2')))
      | ~ v1_funct_2(E_7770,C_7774,'#skF_2')
      | ~ v1_funct_1(E_7770)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7772))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_7774,k1_zfmisc_1(A_7772))
      | v1_xboole_0(C_7774)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_7772) ) ),
    inference(resolution,[status(thm)],[c_70,c_126173])).

tff(c_126192,plain,(
    ! [A_7772,C_7774,E_7770] :
      ( v1_funct_1(k1_tmap_1(A_7772,'#skF_2',C_7774,'#skF_4',E_7770,'#skF_6'))
      | ~ m1_subset_1(E_7770,k1_zfmisc_1(k2_zfmisc_1(C_7774,'#skF_2')))
      | ~ v1_funct_2(E_7770,C_7774,'#skF_2')
      | ~ v1_funct_1(E_7770)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7772))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_7774,k1_zfmisc_1(A_7772))
      | v1_xboole_0(C_7774)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_7772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_126180])).

tff(c_129277,plain,(
    ! [A_13561,C_13562,E_13563] :
      ( v1_funct_1(k1_tmap_1(A_13561,'#skF_2',C_13562,'#skF_4',E_13563,'#skF_6'))
      | ~ m1_subset_1(E_13563,k1_zfmisc_1(k2_zfmisc_1(C_13562,'#skF_2')))
      | ~ v1_funct_2(E_13563,C_13562,'#skF_2')
      | ~ v1_funct_1(E_13563)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_13561))
      | ~ m1_subset_1(C_13562,k1_zfmisc_1(A_13561))
      | v1_xboole_0(C_13562)
      | v1_xboole_0(A_13561) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_126192])).

tff(c_129285,plain,(
    ! [A_13561] :
      ( v1_funct_1(k1_tmap_1(A_13561,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_13561))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_13561))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_13561) ) ),
    inference(resolution,[status(thm)],[c_76,c_129277])).

tff(c_129297,plain,(
    ! [A_13561] :
      ( v1_funct_1(k1_tmap_1(A_13561,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_13561))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_13561))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_13561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_129285])).

tff(c_129918,plain,(
    ! [A_13584] :
      ( v1_funct_1(k1_tmap_1(A_13584,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_13584))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_13584))
      | v1_xboole_0(A_13584) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_129297])).

tff(c_129925,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_129918])).

tff(c_129929,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_129925])).

tff(c_129930,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_129929])).

tff(c_64,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_62,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_129225,plain,(
    ! [B_13557,C_13556,A_13554,F_13558,D_13553,E_13555] :
      ( k2_partfun1(k4_subset_1(A_13554,C_13556,D_13553),B_13557,k1_tmap_1(A_13554,B_13557,C_13556,D_13553,E_13555,F_13558),C_13556) = E_13555
      | ~ m1_subset_1(k1_tmap_1(A_13554,B_13557,C_13556,D_13553,E_13555,F_13558),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_13554,C_13556,D_13553),B_13557)))
      | ~ v1_funct_2(k1_tmap_1(A_13554,B_13557,C_13556,D_13553,E_13555,F_13558),k4_subset_1(A_13554,C_13556,D_13553),B_13557)
      | ~ v1_funct_1(k1_tmap_1(A_13554,B_13557,C_13556,D_13553,E_13555,F_13558))
      | k2_partfun1(D_13553,B_13557,F_13558,k9_subset_1(A_13554,C_13556,D_13553)) != k2_partfun1(C_13556,B_13557,E_13555,k9_subset_1(A_13554,C_13556,D_13553))
      | ~ m1_subset_1(F_13558,k1_zfmisc_1(k2_zfmisc_1(D_13553,B_13557)))
      | ~ v1_funct_2(F_13558,D_13553,B_13557)
      | ~ v1_funct_1(F_13558)
      | ~ m1_subset_1(E_13555,k1_zfmisc_1(k2_zfmisc_1(C_13556,B_13557)))
      | ~ v1_funct_2(E_13555,C_13556,B_13557)
      | ~ v1_funct_1(E_13555)
      | ~ m1_subset_1(D_13553,k1_zfmisc_1(A_13554))
      | v1_xboole_0(D_13553)
      | ~ m1_subset_1(C_13556,k1_zfmisc_1(A_13554))
      | v1_xboole_0(C_13556)
      | v1_xboole_0(B_13557)
      | v1_xboole_0(A_13554) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_188242,plain,(
    ! [C_14438,B_14433,D_14435,E_14434,A_14436,F_14437] :
      ( k2_partfun1(k4_subset_1(A_14436,C_14438,D_14435),B_14433,k1_tmap_1(A_14436,B_14433,C_14438,D_14435,E_14434,F_14437),C_14438) = E_14434
      | ~ v1_funct_2(k1_tmap_1(A_14436,B_14433,C_14438,D_14435,E_14434,F_14437),k4_subset_1(A_14436,C_14438,D_14435),B_14433)
      | ~ v1_funct_1(k1_tmap_1(A_14436,B_14433,C_14438,D_14435,E_14434,F_14437))
      | k2_partfun1(D_14435,B_14433,F_14437,k9_subset_1(A_14436,C_14438,D_14435)) != k2_partfun1(C_14438,B_14433,E_14434,k9_subset_1(A_14436,C_14438,D_14435))
      | ~ m1_subset_1(F_14437,k1_zfmisc_1(k2_zfmisc_1(D_14435,B_14433)))
      | ~ v1_funct_2(F_14437,D_14435,B_14433)
      | ~ v1_funct_1(F_14437)
      | ~ m1_subset_1(E_14434,k1_zfmisc_1(k2_zfmisc_1(C_14438,B_14433)))
      | ~ v1_funct_2(E_14434,C_14438,B_14433)
      | ~ v1_funct_1(E_14434)
      | ~ m1_subset_1(D_14435,k1_zfmisc_1(A_14436))
      | v1_xboole_0(D_14435)
      | ~ m1_subset_1(C_14438,k1_zfmisc_1(A_14436))
      | v1_xboole_0(C_14438)
      | v1_xboole_0(B_14433)
      | v1_xboole_0(A_14436) ) ),
    inference(resolution,[status(thm)],[c_62,c_129225])).

tff(c_207184,plain,(
    ! [E_14722,C_14726,B_14721,F_14725,D_14723,A_14724] :
      ( k2_partfun1(k4_subset_1(A_14724,C_14726,D_14723),B_14721,k1_tmap_1(A_14724,B_14721,C_14726,D_14723,E_14722,F_14725),C_14726) = E_14722
      | ~ v1_funct_1(k1_tmap_1(A_14724,B_14721,C_14726,D_14723,E_14722,F_14725))
      | k2_partfun1(D_14723,B_14721,F_14725,k9_subset_1(A_14724,C_14726,D_14723)) != k2_partfun1(C_14726,B_14721,E_14722,k9_subset_1(A_14724,C_14726,D_14723))
      | ~ m1_subset_1(F_14725,k1_zfmisc_1(k2_zfmisc_1(D_14723,B_14721)))
      | ~ v1_funct_2(F_14725,D_14723,B_14721)
      | ~ v1_funct_1(F_14725)
      | ~ m1_subset_1(E_14722,k1_zfmisc_1(k2_zfmisc_1(C_14726,B_14721)))
      | ~ v1_funct_2(E_14722,C_14726,B_14721)
      | ~ v1_funct_1(E_14722)
      | ~ m1_subset_1(D_14723,k1_zfmisc_1(A_14724))
      | v1_xboole_0(D_14723)
      | ~ m1_subset_1(C_14726,k1_zfmisc_1(A_14724))
      | v1_xboole_0(C_14726)
      | v1_xboole_0(B_14721)
      | v1_xboole_0(A_14724) ) ),
    inference(resolution,[status(thm)],[c_64,c_188242])).

tff(c_207205,plain,(
    ! [A_14724,C_14726,E_14722] :
      ( k2_partfun1(k4_subset_1(A_14724,C_14726,'#skF_4'),'#skF_2',k1_tmap_1(A_14724,'#skF_2',C_14726,'#skF_4',E_14722,'#skF_6'),C_14726) = E_14722
      | ~ v1_funct_1(k1_tmap_1(A_14724,'#skF_2',C_14726,'#skF_4',E_14722,'#skF_6'))
      | k2_partfun1(C_14726,'#skF_2',E_14722,k9_subset_1(A_14724,C_14726,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_14724,C_14726,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_14722,k1_zfmisc_1(k2_zfmisc_1(C_14726,'#skF_2')))
      | ~ v1_funct_2(E_14722,C_14726,'#skF_2')
      | ~ v1_funct_1(E_14722)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_14724))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_14726,k1_zfmisc_1(A_14724))
      | v1_xboole_0(C_14726)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_14724) ) ),
    inference(resolution,[status(thm)],[c_70,c_207184])).

tff(c_207218,plain,(
    ! [A_14724,C_14726,E_14722] :
      ( k2_partfun1(k4_subset_1(A_14724,C_14726,'#skF_4'),'#skF_2',k1_tmap_1(A_14724,'#skF_2',C_14726,'#skF_4',E_14722,'#skF_6'),C_14726) = E_14722
      | ~ v1_funct_1(k1_tmap_1(A_14724,'#skF_2',C_14726,'#skF_4',E_14722,'#skF_6'))
      | k2_partfun1(C_14726,'#skF_2',E_14722,k9_subset_1(A_14724,C_14726,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_14724,C_14726,'#skF_4'))
      | ~ m1_subset_1(E_14722,k1_zfmisc_1(k2_zfmisc_1(C_14726,'#skF_2')))
      | ~ v1_funct_2(E_14722,C_14726,'#skF_2')
      | ~ v1_funct_1(E_14722)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_14724))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_14726,k1_zfmisc_1(A_14724))
      | v1_xboole_0(C_14726)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_14724) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_126037,c_207205])).

tff(c_228136,plain,(
    ! [A_14933,C_14934,E_14935] :
      ( k2_partfun1(k4_subset_1(A_14933,C_14934,'#skF_4'),'#skF_2',k1_tmap_1(A_14933,'#skF_2',C_14934,'#skF_4',E_14935,'#skF_6'),C_14934) = E_14935
      | ~ v1_funct_1(k1_tmap_1(A_14933,'#skF_2',C_14934,'#skF_4',E_14935,'#skF_6'))
      | k2_partfun1(C_14934,'#skF_2',E_14935,k9_subset_1(A_14933,C_14934,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_14933,C_14934,'#skF_4'))
      | ~ m1_subset_1(E_14935,k1_zfmisc_1(k2_zfmisc_1(C_14934,'#skF_2')))
      | ~ v1_funct_2(E_14935,C_14934,'#skF_2')
      | ~ v1_funct_1(E_14935)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_14933))
      | ~ m1_subset_1(C_14934,k1_zfmisc_1(A_14933))
      | v1_xboole_0(C_14934)
      | v1_xboole_0(A_14933) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_207218])).

tff(c_228171,plain,(
    ! [A_14933] :
      ( k2_partfun1(k4_subset_1(A_14933,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_14933,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_14933,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_14933,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_14933,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_14933))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_14933))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_14933) ) ),
    inference(resolution,[status(thm)],[c_76,c_228136])).

tff(c_228183,plain,(
    ! [A_14933] :
      ( k2_partfun1(k4_subset_1(A_14933,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_14933,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_14933,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_14933,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_14933,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_14933))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_14933))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_14933) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_126034,c_228171])).

tff(c_228291,plain,(
    ! [A_14938] :
      ( k2_partfun1(k4_subset_1(A_14938,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_14938,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_14938,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_14938,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_14938,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_14938))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_14938))
      | v1_xboole_0(A_14938) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_228183])).

tff(c_3644,plain,(
    ! [C_3161,A_3162,B_3163] :
      ( v4_relat_1(C_3161,A_3162)
      | ~ m1_subset_1(C_3161,k1_zfmisc_1(k2_zfmisc_1(A_3162,B_3163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3730,plain,(
    ! [A_3174,A_3175,B_3176] :
      ( v4_relat_1(A_3174,A_3175)
      | ~ r1_tarski(A_3174,k2_zfmisc_1(A_3175,B_3176)) ) ),
    inference(resolution,[status(thm)],[c_28,c_3644])).

tff(c_3752,plain,(
    ! [A_3177,B_3178] : v4_relat_1(k2_zfmisc_1(A_3177,B_3178),A_3177) ),
    inference(resolution,[status(thm)],[c_14,c_3730])).

tff(c_3773,plain,(
    ! [A_3179] : v4_relat_1(k1_xboole_0,A_3179) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3752])).

tff(c_3776,plain,(
    ! [A_3179] :
      ( k7_relat_1(k1_xboole_0,A_3179) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3773,c_36])).

tff(c_3779,plain,(
    ! [A_3179] : k7_relat_1(k1_xboole_0,A_3179) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3776])).

tff(c_3878,plain,(
    ! [A_3192,B_3193] :
      ( k7_relat_1(A_3192,B_3193) = k1_xboole_0
      | ~ r1_xboole_0(B_3193,k1_relat_1(A_3192))
      | ~ v1_relat_1(A_3192) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5446,plain,(
    ! [A_3325,B_3326] :
      ( k7_relat_1(A_3325,k1_relat_1(B_3326)) = k1_xboole_0
      | ~ v1_relat_1(A_3325)
      | k7_relat_1(B_3326,k1_relat_1(A_3325)) != k1_xboole_0
      | ~ v1_relat_1(B_3326) ) ),
    inference(resolution,[status(thm)],[c_42,c_3878])).

tff(c_5474,plain,(
    ! [A_3325] :
      ( k7_relat_1(A_3325,k1_relat_1(k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_3325)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3779,c_5446])).

tff(c_5502,plain,(
    ! [A_3327] :
      ( k7_relat_1(A_3327,k1_relat_1(k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_3327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_5474])).

tff(c_3755,plain,(
    ! [A_3177,B_3178] :
      ( k7_relat_1(k2_zfmisc_1(A_3177,B_3178),A_3177) = k2_zfmisc_1(A_3177,B_3178)
      | ~ v1_relat_1(k2_zfmisc_1(A_3177,B_3178)) ) ),
    inference(resolution,[status(thm)],[c_3752,c_36])).

tff(c_3764,plain,(
    ! [A_3177,B_3178] : k7_relat_1(k2_zfmisc_1(A_3177,B_3178),A_3177) = k2_zfmisc_1(A_3177,B_3178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3755])).

tff(c_5549,plain,(
    ! [B_3178] :
      ( k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_3178) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_3178)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5502,c_3764])).

tff(c_5657,plain,(
    ! [B_3328] : k2_zfmisc_1(k1_relat_1(k1_xboole_0),B_3328) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5549])).

tff(c_5722,plain,(
    ! [B_3328] :
      ( k1_xboole_0 = B_3328
      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5657,c_16])).

tff(c_5729,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5722])).

tff(c_3792,plain,(
    ! [B_3181,A_3182] :
      ( r1_xboole_0(k1_relat_1(B_3181),A_3182)
      | k7_relat_1(B_3181,A_3182) != k1_xboole_0
      | ~ v1_relat_1(B_3181) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3803,plain,(
    ! [A_3182,B_3181] :
      ( r1_xboole_0(A_3182,k1_relat_1(B_3181))
      | k7_relat_1(B_3181,A_3182) != k1_xboole_0
      | ~ v1_relat_1(B_3181) ) ),
    inference(resolution,[status(thm)],[c_3792,c_8])).

tff(c_3662,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3644])).

tff(c_3674,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3662,c_36])).

tff(c_3677,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3674])).

tff(c_3942,plain,(
    ! [C_3198,A_3199,B_3200] :
      ( k7_relat_1(k7_relat_1(C_3198,A_3199),B_3200) = k1_xboole_0
      | ~ r1_xboole_0(A_3199,B_3200)
      | ~ v1_relat_1(C_3198) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3966,plain,(
    ! [B_3200] :
      ( k7_relat_1('#skF_5',B_3200) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_3200)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3677,c_3942])).

tff(c_4009,plain,(
    ! [B_3202] :
      ( k7_relat_1('#skF_5',B_3202) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_3202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3966])).

tff(c_4033,plain,(
    ! [B_3181] :
      ( k7_relat_1('#skF_5',k1_relat_1(B_3181)) = k1_xboole_0
      | k7_relat_1(B_3181,'#skF_3') != k1_xboole_0
      | ~ v1_relat_1(B_3181) ) ),
    inference(resolution,[status(thm)],[c_3803,c_4009])).

tff(c_5744,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5729,c_4033])).

tff(c_5787,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3779,c_5744])).

tff(c_3663,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3644])).

tff(c_3680,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3663,c_36])).

tff(c_3683,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3513,c_3680])).

tff(c_3963,plain,(
    ! [B_3200] :
      ( k7_relat_1('#skF_6',B_3200) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_3200)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3683,c_3942])).

tff(c_3979,plain,(
    ! [B_3201] :
      ( k7_relat_1('#skF_6',B_3201) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_3201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3513,c_3963])).

tff(c_4003,plain,(
    ! [B_3181] :
      ( k7_relat_1('#skF_6',k1_relat_1(B_3181)) = k1_xboole_0
      | k7_relat_1(B_3181,'#skF_4') != k1_xboole_0
      | ~ v1_relat_1(B_3181) ) ),
    inference(resolution,[status(thm)],[c_3803,c_3979])).

tff(c_5747,plain,
    ( k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5729,c_4003])).

tff(c_5789,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3779,c_5747])).

tff(c_3664,plain,(
    ! [A_3164,B_3165] :
      ( r1_xboole_0(A_3164,B_3165)
      | ~ r1_subset_1(A_3164,B_3165)
      | v1_xboole_0(B_3165)
      | v1_xboole_0(A_3164) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4765,plain,(
    ! [A_3273,B_3274] :
      ( k3_xboole_0(A_3273,B_3274) = k1_xboole_0
      | ~ r1_subset_1(A_3273,B_3274)
      | v1_xboole_0(B_3274)
      | v1_xboole_0(A_3273) ) ),
    inference(resolution,[status(thm)],[c_3664,c_4])).

tff(c_4774,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_4765])).

tff(c_4780,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4774])).

tff(c_4781,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_86,c_4780])).

tff(c_4122,plain,(
    ! [A_3206,B_3207,C_3208] :
      ( k9_subset_1(A_3206,B_3207,C_3208) = k3_xboole_0(B_3207,C_3208)
      | ~ m1_subset_1(C_3208,k1_zfmisc_1(A_3206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4137,plain,(
    ! [B_3207] : k9_subset_1('#skF_1',B_3207,'#skF_4') = k3_xboole_0(B_3207,'#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_4122])).

tff(c_4485,plain,(
    ! [E_3244,A_3246,D_3245,C_3248,B_3243,F_3247] :
      ( v1_funct_1(k1_tmap_1(A_3246,B_3243,C_3248,D_3245,E_3244,F_3247))
      | ~ m1_subset_1(F_3247,k1_zfmisc_1(k2_zfmisc_1(D_3245,B_3243)))
      | ~ v1_funct_2(F_3247,D_3245,B_3243)
      | ~ v1_funct_1(F_3247)
      | ~ m1_subset_1(E_3244,k1_zfmisc_1(k2_zfmisc_1(C_3248,B_3243)))
      | ~ v1_funct_2(E_3244,C_3248,B_3243)
      | ~ v1_funct_1(E_3244)
      | ~ m1_subset_1(D_3245,k1_zfmisc_1(A_3246))
      | v1_xboole_0(D_3245)
      | ~ m1_subset_1(C_3248,k1_zfmisc_1(A_3246))
      | v1_xboole_0(C_3248)
      | v1_xboole_0(B_3243)
      | v1_xboole_0(A_3246) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_4492,plain,(
    ! [A_3246,C_3248,E_3244] :
      ( v1_funct_1(k1_tmap_1(A_3246,'#skF_2',C_3248,'#skF_4',E_3244,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3244,k1_zfmisc_1(k2_zfmisc_1(C_3248,'#skF_2')))
      | ~ v1_funct_2(E_3244,C_3248,'#skF_2')
      | ~ v1_funct_1(E_3244)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3246))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3248,k1_zfmisc_1(A_3246))
      | v1_xboole_0(C_3248)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3246) ) ),
    inference(resolution,[status(thm)],[c_70,c_4485])).

tff(c_4504,plain,(
    ! [A_3246,C_3248,E_3244] :
      ( v1_funct_1(k1_tmap_1(A_3246,'#skF_2',C_3248,'#skF_4',E_3244,'#skF_6'))
      | ~ m1_subset_1(E_3244,k1_zfmisc_1(k2_zfmisc_1(C_3248,'#skF_2')))
      | ~ v1_funct_2(E_3244,C_3248,'#skF_2')
      | ~ v1_funct_1(E_3244)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3246))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3248,k1_zfmisc_1(A_3246))
      | v1_xboole_0(C_3248)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4492])).

tff(c_4592,plain,(
    ! [A_3253,C_3254,E_3255] :
      ( v1_funct_1(k1_tmap_1(A_3253,'#skF_2',C_3254,'#skF_4',E_3255,'#skF_6'))
      | ~ m1_subset_1(E_3255,k1_zfmisc_1(k2_zfmisc_1(C_3254,'#skF_2')))
      | ~ v1_funct_2(E_3255,C_3254,'#skF_2')
      | ~ v1_funct_1(E_3255)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3253))
      | ~ m1_subset_1(C_3254,k1_zfmisc_1(A_3253))
      | v1_xboole_0(C_3254)
      | v1_xboole_0(A_3253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_4504])).

tff(c_4597,plain,(
    ! [A_3253] :
      ( v1_funct_1(k1_tmap_1(A_3253,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3253))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3253))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3253) ) ),
    inference(resolution,[status(thm)],[c_76,c_4592])).

tff(c_4606,plain,(
    ! [A_3253] :
      ( v1_funct_1(k1_tmap_1(A_3253,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3253))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3253))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_3253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_4597])).

tff(c_4995,plain,(
    ! [A_3288] :
      ( v1_funct_1(k1_tmap_1(A_3288,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3288))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_3288))
      | v1_xboole_0(A_3288) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_4606])).

tff(c_5002,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_4995])).

tff(c_5006,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5002])).

tff(c_5007,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5006])).

tff(c_4398,plain,(
    ! [A_3228,B_3229,C_3230,D_3231] :
      ( k2_partfun1(A_3228,B_3229,C_3230,D_3231) = k7_relat_1(C_3230,D_3231)
      | ~ m1_subset_1(C_3230,k1_zfmisc_1(k2_zfmisc_1(A_3228,B_3229)))
      | ~ v1_funct_1(C_3230) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4403,plain,(
    ! [D_3231] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_3231) = k7_relat_1('#skF_5',D_3231)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_4398])).

tff(c_4413,plain,(
    ! [D_3231] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_3231) = k7_relat_1('#skF_5',D_3231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4403])).

tff(c_4405,plain,(
    ! [D_3231] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_3231) = k7_relat_1('#skF_6',D_3231)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_4398])).

tff(c_4416,plain,(
    ! [D_3231] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_3231) = k7_relat_1('#skF_6',D_3231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4405])).

tff(c_5065,plain,(
    ! [A_3294,B_3297,D_3293,C_3296,E_3295,F_3298] :
      ( k2_partfun1(k4_subset_1(A_3294,C_3296,D_3293),B_3297,k1_tmap_1(A_3294,B_3297,C_3296,D_3293,E_3295,F_3298),D_3293) = F_3298
      | ~ m1_subset_1(k1_tmap_1(A_3294,B_3297,C_3296,D_3293,E_3295,F_3298),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3294,C_3296,D_3293),B_3297)))
      | ~ v1_funct_2(k1_tmap_1(A_3294,B_3297,C_3296,D_3293,E_3295,F_3298),k4_subset_1(A_3294,C_3296,D_3293),B_3297)
      | ~ v1_funct_1(k1_tmap_1(A_3294,B_3297,C_3296,D_3293,E_3295,F_3298))
      | k2_partfun1(D_3293,B_3297,F_3298,k9_subset_1(A_3294,C_3296,D_3293)) != k2_partfun1(C_3296,B_3297,E_3295,k9_subset_1(A_3294,C_3296,D_3293))
      | ~ m1_subset_1(F_3298,k1_zfmisc_1(k2_zfmisc_1(D_3293,B_3297)))
      | ~ v1_funct_2(F_3298,D_3293,B_3297)
      | ~ v1_funct_1(F_3298)
      | ~ m1_subset_1(E_3295,k1_zfmisc_1(k2_zfmisc_1(C_3296,B_3297)))
      | ~ v1_funct_2(E_3295,C_3296,B_3297)
      | ~ v1_funct_1(E_3295)
      | ~ m1_subset_1(D_3293,k1_zfmisc_1(A_3294))
      | v1_xboole_0(D_3293)
      | ~ m1_subset_1(C_3296,k1_zfmisc_1(A_3294))
      | v1_xboole_0(C_3296)
      | v1_xboole_0(B_3297)
      | v1_xboole_0(A_3294) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_12393,plain,(
    ! [B_3505,E_3506,F_3509,A_3508,D_3507,C_3510] :
      ( k2_partfun1(k4_subset_1(A_3508,C_3510,D_3507),B_3505,k1_tmap_1(A_3508,B_3505,C_3510,D_3507,E_3506,F_3509),D_3507) = F_3509
      | ~ v1_funct_2(k1_tmap_1(A_3508,B_3505,C_3510,D_3507,E_3506,F_3509),k4_subset_1(A_3508,C_3510,D_3507),B_3505)
      | ~ v1_funct_1(k1_tmap_1(A_3508,B_3505,C_3510,D_3507,E_3506,F_3509))
      | k2_partfun1(D_3507,B_3505,F_3509,k9_subset_1(A_3508,C_3510,D_3507)) != k2_partfun1(C_3510,B_3505,E_3506,k9_subset_1(A_3508,C_3510,D_3507))
      | ~ m1_subset_1(F_3509,k1_zfmisc_1(k2_zfmisc_1(D_3507,B_3505)))
      | ~ v1_funct_2(F_3509,D_3507,B_3505)
      | ~ v1_funct_1(F_3509)
      | ~ m1_subset_1(E_3506,k1_zfmisc_1(k2_zfmisc_1(C_3510,B_3505)))
      | ~ v1_funct_2(E_3506,C_3510,B_3505)
      | ~ v1_funct_1(E_3506)
      | ~ m1_subset_1(D_3507,k1_zfmisc_1(A_3508))
      | v1_xboole_0(D_3507)
      | ~ m1_subset_1(C_3510,k1_zfmisc_1(A_3508))
      | v1_xboole_0(C_3510)
      | v1_xboole_0(B_3505)
      | v1_xboole_0(A_3508) ) ),
    inference(resolution,[status(thm)],[c_62,c_5065])).

tff(c_30263,plain,(
    ! [D_3769,C_3772,B_3767,E_3768,A_3770,F_3771] :
      ( k2_partfun1(k4_subset_1(A_3770,C_3772,D_3769),B_3767,k1_tmap_1(A_3770,B_3767,C_3772,D_3769,E_3768,F_3771),D_3769) = F_3771
      | ~ v1_funct_1(k1_tmap_1(A_3770,B_3767,C_3772,D_3769,E_3768,F_3771))
      | k2_partfun1(D_3769,B_3767,F_3771,k9_subset_1(A_3770,C_3772,D_3769)) != k2_partfun1(C_3772,B_3767,E_3768,k9_subset_1(A_3770,C_3772,D_3769))
      | ~ m1_subset_1(F_3771,k1_zfmisc_1(k2_zfmisc_1(D_3769,B_3767)))
      | ~ v1_funct_2(F_3771,D_3769,B_3767)
      | ~ v1_funct_1(F_3771)
      | ~ m1_subset_1(E_3768,k1_zfmisc_1(k2_zfmisc_1(C_3772,B_3767)))
      | ~ v1_funct_2(E_3768,C_3772,B_3767)
      | ~ v1_funct_1(E_3768)
      | ~ m1_subset_1(D_3769,k1_zfmisc_1(A_3770))
      | v1_xboole_0(D_3769)
      | ~ m1_subset_1(C_3772,k1_zfmisc_1(A_3770))
      | v1_xboole_0(C_3772)
      | v1_xboole_0(B_3767)
      | v1_xboole_0(A_3770) ) ),
    inference(resolution,[status(thm)],[c_64,c_12393])).

tff(c_30284,plain,(
    ! [A_3770,C_3772,E_3768] :
      ( k2_partfun1(k4_subset_1(A_3770,C_3772,'#skF_4'),'#skF_2',k1_tmap_1(A_3770,'#skF_2',C_3772,'#skF_4',E_3768,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3770,'#skF_2',C_3772,'#skF_4',E_3768,'#skF_6'))
      | k2_partfun1(C_3772,'#skF_2',E_3768,k9_subset_1(A_3770,C_3772,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_3770,C_3772,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3768,k1_zfmisc_1(k2_zfmisc_1(C_3772,'#skF_2')))
      | ~ v1_funct_2(E_3768,C_3772,'#skF_2')
      | ~ v1_funct_1(E_3768)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3770))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3772,k1_zfmisc_1(A_3770))
      | v1_xboole_0(C_3772)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3770) ) ),
    inference(resolution,[status(thm)],[c_70,c_30263])).

tff(c_30297,plain,(
    ! [A_3770,C_3772,E_3768] :
      ( k2_partfun1(k4_subset_1(A_3770,C_3772,'#skF_4'),'#skF_2',k1_tmap_1(A_3770,'#skF_2',C_3772,'#skF_4',E_3768,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_3770,'#skF_2',C_3772,'#skF_4',E_3768,'#skF_6'))
      | k2_partfun1(C_3772,'#skF_2',E_3768,k9_subset_1(A_3770,C_3772,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_3770,C_3772,'#skF_4'))
      | ~ m1_subset_1(E_3768,k1_zfmisc_1(k2_zfmisc_1(C_3772,'#skF_2')))
      | ~ v1_funct_2(E_3768,C_3772,'#skF_2')
      | ~ v1_funct_1(E_3768)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_3770))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_3772,k1_zfmisc_1(A_3770))
      | v1_xboole_0(C_3772)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_3770) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4416,c_30284])).

tff(c_61566,plain,(
    ! [A_4042,C_4043,E_4044] :
      ( k2_partfun1(k4_subset_1(A_4042,C_4043,'#skF_4'),'#skF_2',k1_tmap_1(A_4042,'#skF_2',C_4043,'#skF_4',E_4044,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4042,'#skF_2',C_4043,'#skF_4',E_4044,'#skF_6'))
      | k2_partfun1(C_4043,'#skF_2',E_4044,k9_subset_1(A_4042,C_4043,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4042,C_4043,'#skF_4'))
      | ~ m1_subset_1(E_4044,k1_zfmisc_1(k2_zfmisc_1(C_4043,'#skF_2')))
      | ~ v1_funct_2(E_4044,C_4043,'#skF_2')
      | ~ v1_funct_1(E_4044)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4042))
      | ~ m1_subset_1(C_4043,k1_zfmisc_1(A_4042))
      | v1_xboole_0(C_4043)
      | v1_xboole_0(A_4042) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_30297])).

tff(c_61598,plain,(
    ! [A_4042] :
      ( k2_partfun1(k4_subset_1(A_4042,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4042,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4042,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_4042,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4042,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4042))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4042))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4042) ) ),
    inference(resolution,[status(thm)],[c_76,c_61566])).

tff(c_61610,plain,(
    ! [A_4042] :
      ( k2_partfun1(k4_subset_1(A_4042,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4042,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4042,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4042,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4042,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4042))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4042))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_4042) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_4413,c_61598])).

tff(c_63171,plain,(
    ! [A_4051] :
      ( k2_partfun1(k4_subset_1(A_4051,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_4051,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_4051,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_4051,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_4051,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4051))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_4051))
      | v1_xboole_0(A_4051) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_61610])).

tff(c_3486,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3629,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3486])).

tff(c_63188,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_63171,c_3629])).

tff(c_63210,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_5787,c_5789,c_4781,c_4781,c_2,c_4137,c_2,c_4137,c_5007,c_63188])).

tff(c_63212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_63210])).

tff(c_63215,plain,(
    ! [B_4052] : k1_xboole_0 = B_4052 ),
    inference(splitRight,[status(thm)],[c_5722])).

tff(c_3853,plain,(
    ! [B_3190,A_3191] :
      ( k3_xboole_0(k1_relat_1(B_3190),A_3191) = k1_relat_1(k7_relat_1(B_3190,A_3191))
      | ~ v1_relat_1(B_3190) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4556,plain,(
    ! [B_3251,B_3252] :
      ( k3_xboole_0(B_3251,k1_relat_1(B_3252)) = k1_relat_1(k7_relat_1(B_3252,B_3251))
      | ~ v1_relat_1(B_3252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3853])).

tff(c_5179,plain,(
    ! [B_3310,B_3311] :
      ( k3_xboole_0(k1_relat_1(B_3310),B_3311) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_3310,B_3311)) != k1_xboole_0
      | ~ v1_relat_1(B_3310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4556,c_3494])).

tff(c_3709,plain,(
    ! [B_3170,A_3171] :
      ( k7_relat_1(B_3170,A_3171) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_3170),A_3171)
      | ~ v1_relat_1(B_3170) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3724,plain,(
    ! [B_3170,B_4] :
      ( k7_relat_1(B_3170,B_4) = k1_xboole_0
      | ~ v1_relat_1(B_3170)
      | k3_xboole_0(k1_relat_1(B_3170),B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_3709])).

tff(c_5262,plain,(
    ! [B_3313,B_3314] :
      ( k7_relat_1(B_3313,B_3314) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_3313,B_3314)) != k1_xboole_0
      | ~ v1_relat_1(B_3313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5179,c_3724])).

tff(c_5304,plain,
    ( k7_relat_1('#skF_5','#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3677,c_5262])).

tff(c_5330,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_3677,c_5304])).

tff(c_5332,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5330])).

tff(c_63514,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_63215,c_5332])).

tff(c_63515,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5330])).

tff(c_63555,plain,(
    ! [A_3179] : k7_relat_1('#skF_5',A_3179) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63515,c_63515,c_3779])).

tff(c_63767,plain,(
    ! [D_3231] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_3231) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63555,c_4413])).

tff(c_63526,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63515,c_4781])).

tff(c_4147,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_4137,c_3487])).

tff(c_4148,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_4','#skF_3')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_4147])).

tff(c_63788,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5','#skF_5') = k7_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63526,c_63526,c_4416,c_4148])).

tff(c_63802,plain,(
    k7_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63767,c_63788])).

tff(c_4136,plain,(
    ! [B_3207] : k9_subset_1('#skF_1',B_3207,'#skF_3') = k3_xboole_0(B_3207,'#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_4122])).

tff(c_4225,plain,(
    ! [A_3215,C_3216,B_3217] :
      ( k9_subset_1(A_3215,C_3216,B_3217) = k9_subset_1(A_3215,B_3217,C_3216)
      | ~ m1_subset_1(C_3216,k1_zfmisc_1(A_3215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4233,plain,(
    ! [B_3217] : k9_subset_1('#skF_1',B_3217,'#skF_3') = k9_subset_1('#skF_1','#skF_3',B_3217) ),
    inference(resolution,[status(thm)],[c_88,c_4225])).

tff(c_4242,plain,(
    ! [B_3217] : k9_subset_1('#skF_1','#skF_3',B_3217) = k3_xboole_0(B_3217,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4136,c_4233])).

tff(c_66629,plain,(
    ! [A_6910,F_6911,C_6912,E_6908,B_6907,D_6909] :
      ( k2_partfun1(k4_subset_1(A_6910,C_6912,D_6909),B_6907,k1_tmap_1(A_6910,B_6907,C_6912,D_6909,E_6908,F_6911),D_6909) = F_6911
      | ~ v1_funct_2(k1_tmap_1(A_6910,B_6907,C_6912,D_6909,E_6908,F_6911),k4_subset_1(A_6910,C_6912,D_6909),B_6907)
      | ~ v1_funct_1(k1_tmap_1(A_6910,B_6907,C_6912,D_6909,E_6908,F_6911))
      | k2_partfun1(D_6909,B_6907,F_6911,k9_subset_1(A_6910,C_6912,D_6909)) != k2_partfun1(C_6912,B_6907,E_6908,k9_subset_1(A_6910,C_6912,D_6909))
      | ~ m1_subset_1(F_6911,k1_zfmisc_1(k2_zfmisc_1(D_6909,B_6907)))
      | ~ v1_funct_2(F_6911,D_6909,B_6907)
      | ~ v1_funct_1(F_6911)
      | ~ m1_subset_1(E_6908,k1_zfmisc_1(k2_zfmisc_1(C_6912,B_6907)))
      | ~ v1_funct_2(E_6908,C_6912,B_6907)
      | ~ v1_funct_1(E_6908)
      | ~ m1_subset_1(D_6909,k1_zfmisc_1(A_6910))
      | v1_xboole_0(D_6909)
      | ~ m1_subset_1(C_6912,k1_zfmisc_1(A_6910))
      | v1_xboole_0(C_6912)
      | v1_xboole_0(B_6907)
      | v1_xboole_0(A_6910) ) ),
    inference(resolution,[status(thm)],[c_62,c_5065])).

tff(c_83133,plain,(
    ! [E_7226,B_7225,A_7228,D_7227,C_7230,F_7229] :
      ( k2_partfun1(k4_subset_1(A_7228,C_7230,D_7227),B_7225,k1_tmap_1(A_7228,B_7225,C_7230,D_7227,E_7226,F_7229),D_7227) = F_7229
      | ~ v1_funct_1(k1_tmap_1(A_7228,B_7225,C_7230,D_7227,E_7226,F_7229))
      | k2_partfun1(D_7227,B_7225,F_7229,k9_subset_1(A_7228,C_7230,D_7227)) != k2_partfun1(C_7230,B_7225,E_7226,k9_subset_1(A_7228,C_7230,D_7227))
      | ~ m1_subset_1(F_7229,k1_zfmisc_1(k2_zfmisc_1(D_7227,B_7225)))
      | ~ v1_funct_2(F_7229,D_7227,B_7225)
      | ~ v1_funct_1(F_7229)
      | ~ m1_subset_1(E_7226,k1_zfmisc_1(k2_zfmisc_1(C_7230,B_7225)))
      | ~ v1_funct_2(E_7226,C_7230,B_7225)
      | ~ v1_funct_1(E_7226)
      | ~ m1_subset_1(D_7227,k1_zfmisc_1(A_7228))
      | v1_xboole_0(D_7227)
      | ~ m1_subset_1(C_7230,k1_zfmisc_1(A_7228))
      | v1_xboole_0(C_7230)
      | v1_xboole_0(B_7225)
      | v1_xboole_0(A_7228) ) ),
    inference(resolution,[status(thm)],[c_64,c_66629])).

tff(c_83158,plain,(
    ! [A_7228,C_7230,E_7226] :
      ( k2_partfun1(k4_subset_1(A_7228,C_7230,'#skF_4'),'#skF_2',k1_tmap_1(A_7228,'#skF_2',C_7230,'#skF_4',E_7226,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_7228,'#skF_2',C_7230,'#skF_4',E_7226,'#skF_6'))
      | k2_partfun1(C_7230,'#skF_2',E_7226,k9_subset_1(A_7228,C_7230,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_7228,C_7230,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_7226,k1_zfmisc_1(k2_zfmisc_1(C_7230,'#skF_2')))
      | ~ v1_funct_2(E_7226,C_7230,'#skF_2')
      | ~ v1_funct_1(E_7226)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7228))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_7230,k1_zfmisc_1(A_7228))
      | v1_xboole_0(C_7230)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_7228) ) ),
    inference(resolution,[status(thm)],[c_70,c_83133])).

tff(c_83169,plain,(
    ! [A_7228,C_7230,E_7226] :
      ( k2_partfun1(k4_subset_1(A_7228,C_7230,'#skF_4'),'#skF_2',k1_tmap_1(A_7228,'#skF_2',C_7230,'#skF_4',E_7226,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_7228,'#skF_2',C_7230,'#skF_4',E_7226,'#skF_6'))
      | k2_partfun1(C_7230,'#skF_2',E_7226,k9_subset_1(A_7228,C_7230,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_7228,C_7230,'#skF_4'))
      | ~ m1_subset_1(E_7226,k1_zfmisc_1(k2_zfmisc_1(C_7230,'#skF_2')))
      | ~ v1_funct_2(E_7226,C_7230,'#skF_2')
      | ~ v1_funct_1(E_7226)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7228))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_7230,k1_zfmisc_1(A_7228))
      | v1_xboole_0(C_7230)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_7228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4416,c_83158])).

tff(c_112657,plain,(
    ! [A_7547,C_7548,E_7549] :
      ( k2_partfun1(k4_subset_1(A_7547,C_7548,'#skF_4'),'#skF_2',k1_tmap_1(A_7547,'#skF_2',C_7548,'#skF_4',E_7549,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_7547,'#skF_2',C_7548,'#skF_4',E_7549,'#skF_6'))
      | k2_partfun1(C_7548,'#skF_2',E_7549,k9_subset_1(A_7547,C_7548,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_7547,C_7548,'#skF_4'))
      | ~ m1_subset_1(E_7549,k1_zfmisc_1(k2_zfmisc_1(C_7548,'#skF_2')))
      | ~ v1_funct_2(E_7549,C_7548,'#skF_2')
      | ~ v1_funct_1(E_7549)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7547))
      | ~ m1_subset_1(C_7548,k1_zfmisc_1(A_7547))
      | v1_xboole_0(C_7548)
      | v1_xboole_0(A_7547) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_83169])).

tff(c_112692,plain,(
    ! [A_7547] :
      ( k2_partfun1(k4_subset_1(A_7547,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_7547,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_7547,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_7547,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_7547,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7547))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_7547))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_7547) ) ),
    inference(resolution,[status(thm)],[c_76,c_112657])).

tff(c_112702,plain,(
    ! [A_7547] :
      ( k2_partfun1(k4_subset_1(A_7547,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_7547,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_7547,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_6',k9_subset_1(A_7547,'#skF_3','#skF_4')) != '#skF_5'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7547))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_7547))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_7547) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_63767,c_112692])).

tff(c_125113,plain,(
    ! [A_7675] :
      ( k2_partfun1(k4_subset_1(A_7675,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_7675,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_7675,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_6',k9_subset_1(A_7675,'#skF_3','#skF_4')) != '#skF_5'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_7675))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_7675))
      | v1_xboole_0(A_7675) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_112702])).

tff(c_125136,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) != '#skF_5'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_125113,c_3629])).

tff(c_125172,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_63802,c_63526,c_4242,c_5007,c_125136])).

tff(c_125174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_125172])).

tff(c_125175,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3486])).

tff(c_228311,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_228291,c_125175])).

tff(c_228336,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_128747,c_126207,c_125795,c_128749,c_126207,c_125795,c_129930,c_228311])).

tff(c_228338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_228336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 45.50/32.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.65/32.86  
% 45.65/32.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.65/32.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 45.65/32.86  
% 45.65/32.86  %Foreground sorts:
% 45.65/32.86  
% 45.65/32.86  
% 45.65/32.86  %Background operators:
% 45.65/32.86  
% 45.65/32.86  
% 45.65/32.86  %Foreground operators:
% 45.65/32.86  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 45.65/32.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 45.65/32.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 45.65/32.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 45.65/32.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 45.65/32.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 45.65/32.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 45.65/32.86  tff('#skF_5', type, '#skF_5': $i).
% 45.65/32.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 45.65/32.86  tff('#skF_6', type, '#skF_6': $i).
% 45.65/32.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 45.65/32.86  tff('#skF_2', type, '#skF_2': $i).
% 45.65/32.86  tff('#skF_3', type, '#skF_3': $i).
% 45.65/32.86  tff('#skF_1', type, '#skF_1': $i).
% 45.65/32.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 45.65/32.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 45.65/32.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 45.65/32.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 45.65/32.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 45.65/32.86  tff('#skF_4', type, '#skF_4': $i).
% 45.65/32.86  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 45.65/32.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 45.65/32.86  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 45.65/32.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 45.65/32.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 45.65/32.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 45.65/32.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 45.65/32.86  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 45.65/32.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 45.65/32.86  
% 45.65/32.90  tff(f_240, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 45.65/32.90  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 45.65/32.90  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 45.65/32.90  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 45.65/32.90  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 45.65/32.90  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 45.65/32.90  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 45.65/32.90  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 45.65/32.90  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 45.65/32.90  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 45.65/32.90  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 45.65/32.90  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 45.65/32.90  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 45.65/32.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 45.65/32.90  tff(f_100, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 45.65/32.90  tff(f_116, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 45.65/32.90  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 45.65/32.90  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 45.65/32.90  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 45.65/32.90  tff(f_198, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 45.65/32.90  tff(f_164, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 45.65/32.90  tff(c_94, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.90  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.90  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.90  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 45.65/32.90  tff(c_104, plain, (![A_237, B_238]: (v1_relat_1(k2_zfmisc_1(A_237, B_238)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 45.65/32.90  tff(c_106, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_104])).
% 45.65/32.90  tff(c_14, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 45.65/32.90  tff(c_28, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 45.65/32.90  tff(c_125191, plain, (![C_7681, A_7682, B_7683]: (v4_relat_1(C_7681, A_7682) | ~m1_subset_1(C_7681, k1_zfmisc_1(k2_zfmisc_1(A_7682, B_7683))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 45.65/32.90  tff(c_125274, plain, (![A_7694, A_7695, B_7696]: (v4_relat_1(A_7694, A_7695) | ~r1_tarski(A_7694, k2_zfmisc_1(A_7695, B_7696)))), inference(resolution, [status(thm)], [c_28, c_125191])).
% 45.65/32.90  tff(c_125296, plain, (![A_7697, B_7698]: (v4_relat_1(k2_zfmisc_1(A_7697, B_7698), A_7697))), inference(resolution, [status(thm)], [c_14, c_125274])).
% 45.65/32.90  tff(c_125317, plain, (![A_7699]: (v4_relat_1(k1_xboole_0, A_7699))), inference(superposition, [status(thm), theory('equality')], [c_18, c_125296])).
% 45.65/32.91  tff(c_36, plain, (![B_28, A_27]: (k7_relat_1(B_28, A_27)=B_28 | ~v4_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 45.65/32.91  tff(c_125320, plain, (![A_7699]: (k7_relat_1(k1_xboole_0, A_7699)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_125317, c_36])).
% 45.65/32.91  tff(c_125323, plain, (![A_7699]: (k7_relat_1(k1_xboole_0, A_7699)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_125320])).
% 45.65/32.91  tff(c_125429, plain, (![B_7712, A_7713]: (r1_xboole_0(k1_relat_1(B_7712), A_7713) | k7_relat_1(B_7712, A_7713)!=k1_xboole_0 | ~v1_relat_1(B_7712))), inference(cnfTransformation, [status(thm)], [f_90])).
% 45.65/32.91  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 45.65/32.91  tff(c_125984, plain, (![A_7754, B_7755]: (r1_xboole_0(A_7754, k1_relat_1(B_7755)) | k7_relat_1(B_7755, A_7754)!=k1_xboole_0 | ~v1_relat_1(B_7755))), inference(resolution, [status(thm)], [c_125429, c_8])).
% 45.65/32.91  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 45.65/32.91  tff(c_125299, plain, (![A_7697, B_7698]: (k7_relat_1(k2_zfmisc_1(A_7697, B_7698), A_7697)=k2_zfmisc_1(A_7697, B_7698) | ~v1_relat_1(k2_zfmisc_1(A_7697, B_7698)))), inference(resolution, [status(thm)], [c_125296, c_36])).
% 45.65/32.91  tff(c_125308, plain, (![A_7697, B_7698]: (k7_relat_1(k2_zfmisc_1(A_7697, B_7698), A_7697)=k2_zfmisc_1(A_7697, B_7698))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_125299])).
% 45.65/32.91  tff(c_125505, plain, (![C_7718, A_7719, B_7720]: (k7_relat_1(k7_relat_1(C_7718, A_7719), B_7720)=k1_xboole_0 | ~r1_xboole_0(A_7719, B_7720) | ~v1_relat_1(C_7718))), inference(cnfTransformation, [status(thm)], [f_74])).
% 45.65/32.91  tff(c_125520, plain, (![A_7697, B_7698, B_7720]: (k7_relat_1(k2_zfmisc_1(A_7697, B_7698), B_7720)=k1_xboole_0 | ~r1_xboole_0(A_7697, B_7720) | ~v1_relat_1(k2_zfmisc_1(A_7697, B_7698)))), inference(superposition, [status(thm), theory('equality')], [c_125308, c_125505])).
% 45.65/32.91  tff(c_125922, plain, (![A_7745, B_7746, B_7747]: (k7_relat_1(k2_zfmisc_1(A_7745, B_7746), B_7747)=k1_xboole_0 | ~r1_xboole_0(A_7745, B_7747))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_125520])).
% 45.65/32.91  tff(c_125932, plain, (![B_7747, B_7746]: (k2_zfmisc_1(B_7747, B_7746)=k1_xboole_0 | ~r1_xboole_0(B_7747, B_7747))), inference(superposition, [status(thm), theory('equality')], [c_125922, c_125308])).
% 45.65/32.91  tff(c_127121, plain, (![B_7852, B_7853]: (k2_zfmisc_1(k1_relat_1(B_7852), B_7853)=k1_xboole_0 | k7_relat_1(B_7852, k1_relat_1(B_7852))!=k1_xboole_0 | ~v1_relat_1(B_7852))), inference(resolution, [status(thm)], [c_125984, c_125932])).
% 45.65/32.91  tff(c_127151, plain, (![B_7853]: (k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_7853)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_125323, c_127121])).
% 45.65/32.91  tff(c_127178, plain, (![B_7854]: (k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_7854)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_127151])).
% 45.65/32.91  tff(c_16, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 45.65/32.91  tff(c_127243, plain, (![B_7854]: (k1_xboole_0=B_7854 | k1_relat_1(k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127178, c_16])).
% 45.65/32.91  tff(c_127249, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_127243])).
% 45.65/32.91  tff(c_125404, plain, (![B_7710, A_7711]: (k3_xboole_0(k1_relat_1(B_7710), A_7711)=k1_relat_1(k7_relat_1(B_7710, A_7711)) | ~v1_relat_1(B_7710))), inference(cnfTransformation, [status(thm)], [f_84])).
% 45.65/32.91  tff(c_160, plain, (![A_246, B_247]: (r1_xboole_0(A_246, B_247) | k3_xboole_0(A_246, B_247)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 45.65/32.91  tff(c_3488, plain, (![B_3130, A_3131]: (r1_xboole_0(B_3130, A_3131) | k3_xboole_0(A_3131, B_3130)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_8])).
% 45.65/32.91  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 45.65/32.91  tff(c_3494, plain, (![B_3130, A_3131]: (k3_xboole_0(B_3130, A_3131)=k1_xboole_0 | k3_xboole_0(A_3131, B_3130)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3488, c_4])).
% 45.65/32.91  tff(c_125409, plain, (![A_7711, B_7710]: (k3_xboole_0(A_7711, k1_relat_1(B_7710))=k1_xboole_0 | k1_relat_1(k7_relat_1(B_7710, A_7711))!=k1_xboole_0 | ~v1_relat_1(B_7710))), inference(superposition, [status(thm), theory('equality')], [c_125404, c_3494])).
% 45.65/32.91  tff(c_127257, plain, (![A_7711]: (k3_xboole_0(A_7711, k1_xboole_0)=k1_xboole_0 | k1_relat_1(k7_relat_1(k1_xboole_0, A_7711))!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_127249, c_125409])).
% 45.65/32.91  tff(c_127302, plain, (![A_7711]: (k3_xboole_0(A_7711, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_127249, c_125323, c_127257])).
% 45.65/32.91  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 45.65/32.91  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_3496, plain, (![C_3132, A_3133, B_3134]: (v1_relat_1(C_3132) | ~m1_subset_1(C_3132, k1_zfmisc_1(k2_zfmisc_1(A_3133, B_3134))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 45.65/32.91  tff(c_3513, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_3496])).
% 45.65/32.91  tff(c_125210, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_125191])).
% 45.65/32.91  tff(c_125227, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_125210, c_36])).
% 45.65/32.91  tff(c_125230, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3513, c_125227])).
% 45.65/32.91  tff(c_125526, plain, (![B_7720]: (k7_relat_1('#skF_6', B_7720)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_7720) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_125230, c_125505])).
% 45.65/32.91  tff(c_125542, plain, (![B_7721]: (k7_relat_1('#skF_6', B_7721)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_7721))), inference(demodulation, [status(thm), theory('equality')], [c_3513, c_125526])).
% 45.65/32.91  tff(c_125566, plain, (![B_4]: (k7_relat_1('#skF_6', B_4)=k1_xboole_0 | k3_xboole_0('#skF_4', B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_125542])).
% 45.65/32.91  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_3512, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_3496])).
% 45.65/32.91  tff(c_90, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_86, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 45.65/32.91  tff(c_82, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_125211, plain, (![A_7684, B_7685]: (r1_xboole_0(A_7684, B_7685) | ~r1_subset_1(A_7684, B_7685) | v1_xboole_0(B_7685) | v1_xboole_0(A_7684))), inference(cnfTransformation, [status(thm)], [f_100])).
% 45.65/32.91  tff(c_126195, plain, (![A_7775, B_7776]: (k3_xboole_0(A_7775, B_7776)=k1_xboole_0 | ~r1_subset_1(A_7775, B_7776) | v1_xboole_0(B_7776) | v1_xboole_0(A_7775))), inference(resolution, [status(thm)], [c_125211, c_4])).
% 45.65/32.91  tff(c_126201, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_126195])).
% 45.65/32.91  tff(c_126206, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_126201])).
% 45.65/32.91  tff(c_126207, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_126206])).
% 45.65/32.91  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_126019, plain, (![A_7756, B_7757, C_7758, D_7759]: (k2_partfun1(A_7756, B_7757, C_7758, D_7759)=k7_relat_1(C_7758, D_7759) | ~m1_subset_1(C_7758, k1_zfmisc_1(k2_zfmisc_1(A_7756, B_7757))) | ~v1_funct_1(C_7758))), inference(cnfTransformation, [status(thm)], [f_116])).
% 45.65/32.91  tff(c_126026, plain, (![D_7759]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_7759)=k7_relat_1('#skF_6', D_7759) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_126019])).
% 45.65/32.91  tff(c_126037, plain, (![D_7759]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_7759)=k7_relat_1('#skF_6', D_7759))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_126026])).
% 45.65/32.91  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_126024, plain, (![D_7759]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_7759)=k7_relat_1('#skF_5', D_7759) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_126019])).
% 45.65/32.91  tff(c_126034, plain, (![D_7759]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_7759)=k7_relat_1('#skF_5', D_7759))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_126024])).
% 45.65/32.91  tff(c_125659, plain, (![A_7726, B_7727, C_7728]: (k9_subset_1(A_7726, B_7727, C_7728)=k3_xboole_0(B_7727, C_7728) | ~m1_subset_1(C_7728, k1_zfmisc_1(A_7726)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 45.65/32.91  tff(c_125674, plain, (![B_7727]: (k9_subset_1('#skF_1', B_7727, '#skF_4')=k3_xboole_0(B_7727, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_125659])).
% 45.65/32.91  tff(c_210, plain, (![C_256, A_257, B_258]: (v1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 45.65/32.91  tff(c_227, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_210])).
% 45.65/32.91  tff(c_226, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_210])).
% 45.65/32.91  tff(c_347, plain, (![C_283, A_284, B_285]: (v4_relat_1(C_283, A_284) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 45.65/32.91  tff(c_405, plain, (![A_292, A_293, B_294]: (v4_relat_1(A_292, A_293) | ~r1_tarski(A_292, k2_zfmisc_1(A_293, B_294)))), inference(resolution, [status(thm)], [c_28, c_347])).
% 45.65/32.91  tff(c_427, plain, (![A_295, B_296]: (v4_relat_1(k2_zfmisc_1(A_295, B_296), A_295))), inference(resolution, [status(thm)], [c_14, c_405])).
% 45.65/32.91  tff(c_448, plain, (![A_297]: (v4_relat_1(k1_xboole_0, A_297))), inference(superposition, [status(thm), theory('equality')], [c_18, c_427])).
% 45.65/32.91  tff(c_451, plain, (![A_297]: (k7_relat_1(k1_xboole_0, A_297)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_448, c_36])).
% 45.65/32.91  tff(c_454, plain, (![A_297]: (k7_relat_1(k1_xboole_0, A_297)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_451])).
% 45.65/32.91  tff(c_42, plain, (![B_32, A_31]: (r1_xboole_0(k1_relat_1(B_32), A_31) | k7_relat_1(B_32, A_31)!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_90])).
% 45.65/32.91  tff(c_430, plain, (![A_295, B_296]: (k7_relat_1(k2_zfmisc_1(A_295, B_296), A_295)=k2_zfmisc_1(A_295, B_296) | ~v1_relat_1(k2_zfmisc_1(A_295, B_296)))), inference(resolution, [status(thm)], [c_427, c_36])).
% 45.65/32.91  tff(c_439, plain, (![A_295, B_296]: (k7_relat_1(k2_zfmisc_1(A_295, B_296), A_295)=k2_zfmisc_1(A_295, B_296))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_430])).
% 45.65/32.91  tff(c_741, plain, (![C_331, A_332, B_333]: (k7_relat_1(k7_relat_1(C_331, A_332), B_333)=k1_xboole_0 | ~r1_xboole_0(A_332, B_333) | ~v1_relat_1(C_331))), inference(cnfTransformation, [status(thm)], [f_74])).
% 45.65/32.91  tff(c_756, plain, (![A_295, B_296, B_333]: (k7_relat_1(k2_zfmisc_1(A_295, B_296), B_333)=k1_xboole_0 | ~r1_xboole_0(A_295, B_333) | ~v1_relat_1(k2_zfmisc_1(A_295, B_296)))), inference(superposition, [status(thm), theory('equality')], [c_439, c_741])).
% 45.65/32.91  tff(c_1191, plain, (![A_357, B_358, B_359]: (k7_relat_1(k2_zfmisc_1(A_357, B_358), B_359)=k1_xboole_0 | ~r1_xboole_0(A_357, B_359))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_756])).
% 45.65/32.91  tff(c_1220, plain, (![B_360, B_361]: (k2_zfmisc_1(B_360, B_361)=k1_xboole_0 | ~r1_xboole_0(B_360, B_360))), inference(superposition, [status(thm), theory('equality')], [c_1191, c_439])).
% 45.65/32.91  tff(c_2116, plain, (![B_443, B_444]: (k2_zfmisc_1(k1_relat_1(B_443), B_444)=k1_xboole_0 | k7_relat_1(B_443, k1_relat_1(B_443))!=k1_xboole_0 | ~v1_relat_1(B_443))), inference(resolution, [status(thm)], [c_42, c_1220])).
% 45.65/32.91  tff(c_2143, plain, (![B_444]: (k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_444)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_454, c_2116])).
% 45.65/32.91  tff(c_2169, plain, (![B_445]: (k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_445)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2143])).
% 45.65/32.91  tff(c_2234, plain, (![B_445]: (k1_xboole_0=B_445 | k1_relat_1(k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2169, c_16])).
% 45.65/32.91  tff(c_2244, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2234])).
% 45.65/32.91  tff(c_397, plain, (![B_290, A_291]: (r1_xboole_0(k1_relat_1(B_290), A_291) | k7_relat_1(B_290, A_291)!=k1_xboole_0 | ~v1_relat_1(B_290))), inference(cnfTransformation, [status(thm)], [f_90])).
% 45.65/32.91  tff(c_404, plain, (![A_291, B_290]: (r1_xboole_0(A_291, k1_relat_1(B_290)) | k7_relat_1(B_290, A_291)!=k1_xboole_0 | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_397, c_8])).
% 45.65/32.91  tff(c_366, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_347])).
% 45.65/32.91  tff(c_375, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_366, c_36])).
% 45.65/32.91  tff(c_378, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_375])).
% 45.65/32.91  tff(c_762, plain, (![B_333]: (k7_relat_1('#skF_6', B_333)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_333) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_741])).
% 45.65/32.91  tff(c_778, plain, (![B_334]: (k7_relat_1('#skF_6', B_334)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_334))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_762])).
% 45.65/32.91  tff(c_802, plain, (![B_290]: (k7_relat_1('#skF_6', k1_relat_1(B_290))=k1_xboole_0 | k7_relat_1(B_290, '#skF_4')!=k1_xboole_0 | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_404, c_778])).
% 45.65/32.91  tff(c_2261, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2244, c_802])).
% 45.65/32.91  tff(c_2303, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_454, c_2261])).
% 45.65/32.91  tff(c_365, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_347])).
% 45.65/32.91  tff(c_369, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_365, c_36])).
% 45.65/32.91  tff(c_372, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_369])).
% 45.65/32.91  tff(c_765, plain, (![B_333]: (k7_relat_1('#skF_5', B_333)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_333) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_372, c_741])).
% 45.65/32.91  tff(c_808, plain, (![B_335]: (k7_relat_1('#skF_5', B_335)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_335))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_765])).
% 45.65/32.91  tff(c_832, plain, (![B_290]: (k7_relat_1('#skF_5', k1_relat_1(B_290))=k1_xboole_0 | k7_relat_1(B_290, '#skF_3')!=k1_xboole_0 | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_404, c_808])).
% 45.65/32.91  tff(c_2258, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2244, c_832])).
% 45.65/32.91  tff(c_2301, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_454, c_2258])).
% 45.65/32.91  tff(c_520, plain, (![A_307, B_308]: (r1_xboole_0(A_307, B_308) | ~r1_subset_1(A_307, B_308) | v1_xboole_0(B_308) | v1_xboole_0(A_307))), inference(cnfTransformation, [status(thm)], [f_100])).
% 45.65/32.91  tff(c_1404, plain, (![A_389, B_390]: (k3_xboole_0(A_389, B_390)=k1_xboole_0 | ~r1_subset_1(A_389, B_390) | v1_xboole_0(B_390) | v1_xboole_0(A_389))), inference(resolution, [status(thm)], [c_520, c_4])).
% 45.65/32.91  tff(c_1410, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1404])).
% 45.65/32.91  tff(c_1415, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1410])).
% 45.65/32.91  tff(c_1416, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_1415])).
% 45.65/32.91  tff(c_1092, plain, (![A_348, B_349, C_350, D_351]: (k2_partfun1(A_348, B_349, C_350, D_351)=k7_relat_1(C_350, D_351) | ~m1_subset_1(C_350, k1_zfmisc_1(k2_zfmisc_1(A_348, B_349))) | ~v1_funct_1(C_350))), inference(cnfTransformation, [status(thm)], [f_116])).
% 45.65/32.91  tff(c_1099, plain, (![D_351]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_351)=k7_relat_1('#skF_6', D_351) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_1092])).
% 45.65/32.91  tff(c_1110, plain, (![D_351]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_351)=k7_relat_1('#skF_6', D_351))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1099])).
% 45.65/32.91  tff(c_1097, plain, (![D_351]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_351)=k7_relat_1('#skF_5', D_351) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_1092])).
% 45.65/32.91  tff(c_1107, plain, (![D_351]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_351)=k7_relat_1('#skF_5', D_351))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1097])).
% 45.65/32.91  tff(c_658, plain, (![A_319, B_320, C_321]: (k9_subset_1(A_319, B_320, C_321)=k3_xboole_0(B_320, C_321) | ~m1_subset_1(C_321, k1_zfmisc_1(A_319)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 45.65/32.91  tff(c_673, plain, (![B_320]: (k9_subset_1('#skF_1', B_320, '#skF_4')=k3_xboole_0(B_320, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_658])).
% 45.65/32.91  tff(c_68, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_201, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 45.65/32.91  tff(c_683, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_673, c_673, c_201])).
% 45.65/32.91  tff(c_684, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_683])).
% 45.65/32.91  tff(c_2741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2303, c_2301, c_1416, c_1416, c_1110, c_1107, c_684])).
% 45.65/32.91  tff(c_2744, plain, (![B_468]: (k1_xboole_0=B_468)), inference(splitRight, [status(thm)], [c_2234])).
% 45.65/32.91  tff(c_557, plain, (![B_311, A_312]: (k3_xboole_0(k1_relat_1(B_311), A_312)=k1_relat_1(k7_relat_1(B_311, A_312)) | ~v1_relat_1(B_311))), inference(cnfTransformation, [status(thm)], [f_84])).
% 45.65/32.91  tff(c_625, plain, (![A_317, B_318]: (k3_xboole_0(A_317, k1_relat_1(B_318))=k1_relat_1(k7_relat_1(B_318, A_317)) | ~v1_relat_1(B_318))), inference(superposition, [status(thm), theory('equality')], [c_557, c_2])).
% 45.65/32.91  tff(c_202, plain, (![B_254, A_255]: (r1_xboole_0(B_254, A_255) | k3_xboole_0(A_255, B_254)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_8])).
% 45.65/32.91  tff(c_208, plain, (![B_254, A_255]: (k3_xboole_0(B_254, A_255)=k1_xboole_0 | k3_xboole_0(A_255, B_254)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_202, c_4])).
% 45.65/32.91  tff(c_1836, plain, (![B_426, A_427]: (k3_xboole_0(k1_relat_1(B_426), A_427)=k1_xboole_0 | k1_relat_1(k7_relat_1(B_426, A_427))!=k1_xboole_0 | ~v1_relat_1(B_426))), inference(superposition, [status(thm), theory('equality')], [c_625, c_208])).
% 45.65/32.91  tff(c_537, plain, (![B_309, A_310]: (k7_relat_1(B_309, A_310)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_309), A_310) | ~v1_relat_1(B_309))), inference(cnfTransformation, [status(thm)], [f_90])).
% 45.65/32.91  tff(c_556, plain, (![B_309, B_4]: (k7_relat_1(B_309, B_4)=k1_xboole_0 | ~v1_relat_1(B_309) | k3_xboole_0(k1_relat_1(B_309), B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_537])).
% 45.65/32.91  tff(c_1907, plain, (![B_428, A_429]: (k7_relat_1(B_428, A_429)=k1_xboole_0 | k1_relat_1(k7_relat_1(B_428, A_429))!=k1_xboole_0 | ~v1_relat_1(B_428))), inference(superposition, [status(thm), theory('equality')], [c_1836, c_556])).
% 45.65/32.91  tff(c_1949, plain, (k7_relat_1('#skF_5', '#skF_3')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_372, c_1907])).
% 45.65/32.91  tff(c_1975, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_226, c_372, c_1949])).
% 45.65/32.91  tff(c_2003, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1975])).
% 45.65/32.91  tff(c_3036, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2744, c_2003])).
% 45.65/32.91  tff(c_3037, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1975])).
% 45.65/32.91  tff(c_3038, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1975])).
% 45.65/32.91  tff(c_3100, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3037, c_3038])).
% 45.65/32.91  tff(c_3077, plain, (![A_297]: (k7_relat_1('#skF_5', A_297)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3037, c_3037, c_454])).
% 45.65/32.91  tff(c_504, plain, (![A_305, B_306]: (k7_relat_1(A_305, B_306)=k1_xboole_0 | ~r1_xboole_0(B_306, k1_relat_1(A_305)) | ~v1_relat_1(A_305))), inference(cnfTransformation, [status(thm)], [f_68])).
% 45.65/32.91  tff(c_517, plain, (![A_305, B_32]: (k7_relat_1(A_305, k1_relat_1(B_32))=k1_xboole_0 | ~v1_relat_1(A_305) | k7_relat_1(B_32, k1_relat_1(A_305))!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_42, c_504])).
% 45.65/32.91  tff(c_3375, plain, (![A_3116, B_3117]: (k7_relat_1(A_3116, k1_relat_1(B_3117))='#skF_5' | ~v1_relat_1(A_3116) | k7_relat_1(B_3117, k1_relat_1(A_3116))!='#skF_5' | ~v1_relat_1(B_3117))), inference(demodulation, [status(thm), theory('equality')], [c_3037, c_3037, c_517])).
% 45.65/32.91  tff(c_3378, plain, (![A_3116]: (k7_relat_1(A_3116, k1_relat_1('#skF_5'))='#skF_5' | ~v1_relat_1(A_3116) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3077, c_3375])).
% 45.65/32.91  tff(c_3391, plain, (![A_3118]: (k7_relat_1(A_3118, '#skF_5')='#skF_5' | ~v1_relat_1(A_3118))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_3100, c_3378])).
% 45.65/32.91  tff(c_3401, plain, (k7_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_227, c_3391])).
% 45.65/32.91  tff(c_3196, plain, (![D_351]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_351)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3077, c_1107])).
% 45.65/32.91  tff(c_3049, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3037, c_1416])).
% 45.65/32.91  tff(c_3485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3401, c_3196, c_3049, c_3049, c_1110, c_684])).
% 45.65/32.91  tff(c_3487, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 45.65/32.91  tff(c_125685, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125674, c_125674, c_3487])).
% 45.65/32.91  tff(c_125686, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_125685])).
% 45.65/32.91  tff(c_126038, plain, (k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))=k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126034, c_125686])).
% 45.65/32.91  tff(c_126057, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))=k7_relat_1('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126037, c_126038])).
% 45.65/32.91  tff(c_126208, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_126207, c_126207, c_126057])).
% 45.65/32.91  tff(c_125450, plain, (![A_7714, B_7715]: (k3_xboole_0(A_7714, k1_relat_1(B_7715))=k1_relat_1(k7_relat_1(B_7715, A_7714)) | ~v1_relat_1(B_7715))), inference(superposition, [status(thm), theory('equality')], [c_2, c_125404])).
% 45.65/32.91  tff(c_126792, plain, (![B_7828, A_7829]: (k3_xboole_0(k1_relat_1(B_7828), A_7829)=k1_xboole_0 | k1_relat_1(k7_relat_1(B_7828, A_7829))!=k1_xboole_0 | ~v1_relat_1(B_7828))), inference(superposition, [status(thm), theory('equality')], [c_125450, c_3494])).
% 45.65/32.91  tff(c_125388, plain, (![B_7708, A_7709]: (k7_relat_1(B_7708, A_7709)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_7708), A_7709) | ~v1_relat_1(B_7708))), inference(cnfTransformation, [status(thm)], [f_90])).
% 45.65/32.91  tff(c_125403, plain, (![B_7708, B_4]: (k7_relat_1(B_7708, B_4)=k1_xboole_0 | ~v1_relat_1(B_7708) | k3_xboole_0(k1_relat_1(B_7708), B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_125388])).
% 45.65/32.91  tff(c_126863, plain, (![B_7830, A_7831]: (k7_relat_1(B_7830, A_7831)=k1_xboole_0 | k1_relat_1(k7_relat_1(B_7830, A_7831))!=k1_xboole_0 | ~v1_relat_1(B_7830))), inference(superposition, [status(thm), theory('equality')], [c_126792, c_125403])).
% 45.65/32.91  tff(c_126875, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k1_relat_1(k7_relat_1('#skF_6', k1_xboole_0))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_126208, c_126863])).
% 45.65/32.91  tff(c_126917, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k1_relat_1(k7_relat_1('#skF_6', k1_xboole_0))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_126208, c_126875])).
% 45.65/32.91  tff(c_126968, plain, (k1_relat_1(k7_relat_1('#skF_6', k1_xboole_0))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126917])).
% 45.65/32.91  tff(c_126986, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0 | k3_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_125566, c_126968])).
% 45.65/32.91  tff(c_126991, plain, (k3_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126986])).
% 45.65/32.91  tff(c_127452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127302, c_126991])).
% 45.65/32.91  tff(c_127455, plain, (![B_7865]: (k1_xboole_0=B_7865)), inference(splitRight, [status(thm)], [c_127243])).
% 45.65/32.91  tff(c_127815, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_127455, c_126991])).
% 45.65/32.91  tff(c_127816, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_126986])).
% 45.65/32.91  tff(c_125951, plain, (![B_7748, B_7749]: (k2_zfmisc_1(B_7748, B_7749)=k1_xboole_0 | ~r1_xboole_0(B_7748, B_7748))), inference(superposition, [status(thm), theory('equality')], [c_125922, c_125308])).
% 45.65/32.91  tff(c_127981, plain, (![B_10692, B_10693]: (k2_zfmisc_1(k1_relat_1(B_10692), B_10693)=k1_xboole_0 | k7_relat_1(B_10692, k1_relat_1(B_10692))!=k1_xboole_0 | ~v1_relat_1(B_10692))), inference(resolution, [status(thm)], [c_42, c_125951])).
% 45.65/32.91  tff(c_128011, plain, (![B_10693]: (k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_10693)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_125323, c_127981])).
% 45.65/32.91  tff(c_128038, plain, (![B_10694]: (k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_10694)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_128011])).
% 45.65/32.91  tff(c_128086, plain, (![B_10694]: (k1_xboole_0=B_10694 | k1_relat_1(k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128038, c_16])).
% 45.65/32.91  tff(c_128110, plain, (![B_10695]: (k1_xboole_0=B_10695)), inference(negUnitSimplification, [status(thm)], [c_127816, c_128086])).
% 45.65/32.91  tff(c_128470, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_128110, c_127816])).
% 45.65/32.91  tff(c_128471, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_126917])).
% 45.65/32.91  tff(c_128472, plain, (k1_relat_1(k7_relat_1('#skF_6', k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_126917])).
% 45.65/32.91  tff(c_128551, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_128471, c_128472])).
% 45.65/32.91  tff(c_126352, plain, (![B_7791, A_7792]: (k3_xboole_0(k1_relat_1(B_7791), A_7792)=k1_xboole_0 | k7_relat_1(B_7791, A_7792)!=k1_xboole_0 | ~v1_relat_1(B_7791))), inference(resolution, [status(thm)], [c_125429, c_4])).
% 45.65/32.91  tff(c_126394, plain, (![B_2, B_7791]: (k3_xboole_0(B_2, k1_relat_1(B_7791))=k1_xboole_0 | k7_relat_1(B_7791, B_2)!=k1_xboole_0 | ~v1_relat_1(B_7791))), inference(superposition, [status(thm), theory('equality')], [c_2, c_126352])).
% 45.65/32.91  tff(c_128564, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, B_2)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128551, c_126394])).
% 45.65/32.91  tff(c_128601, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_125323, c_128564])).
% 45.65/32.91  tff(c_167, plain, (![B_247, A_246]: (r1_xboole_0(B_247, A_246) | k3_xboole_0(A_246, B_247)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_8])).
% 45.65/32.91  tff(c_125209, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_125191])).
% 45.65/32.91  tff(c_125221, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_125209, c_36])).
% 45.65/32.91  tff(c_125224, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_125221])).
% 45.65/32.91  tff(c_125529, plain, (![B_7720]: (k7_relat_1('#skF_5', B_7720)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_7720) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_125224, c_125505])).
% 45.65/32.91  tff(c_125567, plain, (![B_7722]: (k7_relat_1('#skF_5', B_7722)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_7722))), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_125529])).
% 45.65/32.91  tff(c_125590, plain, (![A_246]: (k7_relat_1('#skF_5', A_246)=k1_xboole_0 | k3_xboole_0(A_246, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_167, c_125567])).
% 45.65/32.91  tff(c_126244, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_126208, c_125590])).
% 45.65/32.91  tff(c_126259, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_126244])).
% 45.65/32.91  tff(c_126264, plain, (k3_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126259])).
% 45.65/32.91  tff(c_128746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128601, c_126264])).
% 45.65/32.91  tff(c_128747, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_126259])).
% 45.65/32.91  tff(c_125673, plain, (![B_7727]: (k9_subset_1('#skF_1', B_7727, '#skF_3')=k3_xboole_0(B_7727, '#skF_3'))), inference(resolution, [status(thm)], [c_88, c_125659])).
% 45.65/32.91  tff(c_125778, plain, (![A_7735, C_7736, B_7737]: (k9_subset_1(A_7735, C_7736, B_7737)=k9_subset_1(A_7735, B_7737, C_7736) | ~m1_subset_1(C_7736, k1_zfmisc_1(A_7735)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 45.65/32.91  tff(c_125786, plain, (![B_7737]: (k9_subset_1('#skF_1', B_7737, '#skF_3')=k9_subset_1('#skF_1', '#skF_3', B_7737))), inference(resolution, [status(thm)], [c_88, c_125778])).
% 45.65/32.91  tff(c_125795, plain, (![B_7737]: (k9_subset_1('#skF_1', '#skF_3', B_7737)=k3_xboole_0(B_7737, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125673, c_125786])).
% 45.65/32.91  tff(c_128749, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_128747, c_126208])).
% 45.65/32.91  tff(c_78, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_92, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_240])).
% 45.65/32.91  tff(c_126173, plain, (![F_7773, E_7770, D_7771, A_7772, C_7774, B_7769]: (v1_funct_1(k1_tmap_1(A_7772, B_7769, C_7774, D_7771, E_7770, F_7773)) | ~m1_subset_1(F_7773, k1_zfmisc_1(k2_zfmisc_1(D_7771, B_7769))) | ~v1_funct_2(F_7773, D_7771, B_7769) | ~v1_funct_1(F_7773) | ~m1_subset_1(E_7770, k1_zfmisc_1(k2_zfmisc_1(C_7774, B_7769))) | ~v1_funct_2(E_7770, C_7774, B_7769) | ~v1_funct_1(E_7770) | ~m1_subset_1(D_7771, k1_zfmisc_1(A_7772)) | v1_xboole_0(D_7771) | ~m1_subset_1(C_7774, k1_zfmisc_1(A_7772)) | v1_xboole_0(C_7774) | v1_xboole_0(B_7769) | v1_xboole_0(A_7772))), inference(cnfTransformation, [status(thm)], [f_198])).
% 45.65/32.91  tff(c_126180, plain, (![A_7772, C_7774, E_7770]: (v1_funct_1(k1_tmap_1(A_7772, '#skF_2', C_7774, '#skF_4', E_7770, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_7770, k1_zfmisc_1(k2_zfmisc_1(C_7774, '#skF_2'))) | ~v1_funct_2(E_7770, C_7774, '#skF_2') | ~v1_funct_1(E_7770) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7772)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_7774, k1_zfmisc_1(A_7772)) | v1_xboole_0(C_7774) | v1_xboole_0('#skF_2') | v1_xboole_0(A_7772))), inference(resolution, [status(thm)], [c_70, c_126173])).
% 45.65/32.91  tff(c_126192, plain, (![A_7772, C_7774, E_7770]: (v1_funct_1(k1_tmap_1(A_7772, '#skF_2', C_7774, '#skF_4', E_7770, '#skF_6')) | ~m1_subset_1(E_7770, k1_zfmisc_1(k2_zfmisc_1(C_7774, '#skF_2'))) | ~v1_funct_2(E_7770, C_7774, '#skF_2') | ~v1_funct_1(E_7770) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7772)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_7774, k1_zfmisc_1(A_7772)) | v1_xboole_0(C_7774) | v1_xboole_0('#skF_2') | v1_xboole_0(A_7772))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_126180])).
% 45.65/32.91  tff(c_129277, plain, (![A_13561, C_13562, E_13563]: (v1_funct_1(k1_tmap_1(A_13561, '#skF_2', C_13562, '#skF_4', E_13563, '#skF_6')) | ~m1_subset_1(E_13563, k1_zfmisc_1(k2_zfmisc_1(C_13562, '#skF_2'))) | ~v1_funct_2(E_13563, C_13562, '#skF_2') | ~v1_funct_1(E_13563) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_13561)) | ~m1_subset_1(C_13562, k1_zfmisc_1(A_13561)) | v1_xboole_0(C_13562) | v1_xboole_0(A_13561))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_126192])).
% 45.65/32.91  tff(c_129285, plain, (![A_13561]: (v1_funct_1(k1_tmap_1(A_13561, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_13561)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_13561)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_13561))), inference(resolution, [status(thm)], [c_76, c_129277])).
% 45.65/32.91  tff(c_129297, plain, (![A_13561]: (v1_funct_1(k1_tmap_1(A_13561, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_13561)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_13561)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_13561))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_129285])).
% 45.65/32.91  tff(c_129918, plain, (![A_13584]: (v1_funct_1(k1_tmap_1(A_13584, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_13584)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_13584)) | v1_xboole_0(A_13584))), inference(negUnitSimplification, [status(thm)], [c_90, c_129297])).
% 45.65/32.91  tff(c_129925, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_129918])).
% 45.65/32.91  tff(c_129929, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_129925])).
% 45.65/32.91  tff(c_129930, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_94, c_129929])).
% 45.65/32.91  tff(c_64, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (v1_funct_2(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k4_subset_1(A_172, C_174, D_175), B_173) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_198])).
% 45.65/32.91  tff(c_62, plain, (![F_177, D_175, A_172, C_174, E_176, B_173]: (m1_subset_1(k1_tmap_1(A_172, B_173, C_174, D_175, E_176, F_177), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_172, C_174, D_175), B_173))) | ~m1_subset_1(F_177, k1_zfmisc_1(k2_zfmisc_1(D_175, B_173))) | ~v1_funct_2(F_177, D_175, B_173) | ~v1_funct_1(F_177) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(C_174, B_173))) | ~v1_funct_2(E_176, C_174, B_173) | ~v1_funct_1(E_176) | ~m1_subset_1(D_175, k1_zfmisc_1(A_172)) | v1_xboole_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(A_172)) | v1_xboole_0(C_174) | v1_xboole_0(B_173) | v1_xboole_0(A_172))), inference(cnfTransformation, [status(thm)], [f_198])).
% 45.65/32.91  tff(c_129225, plain, (![B_13557, C_13556, A_13554, F_13558, D_13553, E_13555]: (k2_partfun1(k4_subset_1(A_13554, C_13556, D_13553), B_13557, k1_tmap_1(A_13554, B_13557, C_13556, D_13553, E_13555, F_13558), C_13556)=E_13555 | ~m1_subset_1(k1_tmap_1(A_13554, B_13557, C_13556, D_13553, E_13555, F_13558), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_13554, C_13556, D_13553), B_13557))) | ~v1_funct_2(k1_tmap_1(A_13554, B_13557, C_13556, D_13553, E_13555, F_13558), k4_subset_1(A_13554, C_13556, D_13553), B_13557) | ~v1_funct_1(k1_tmap_1(A_13554, B_13557, C_13556, D_13553, E_13555, F_13558)) | k2_partfun1(D_13553, B_13557, F_13558, k9_subset_1(A_13554, C_13556, D_13553))!=k2_partfun1(C_13556, B_13557, E_13555, k9_subset_1(A_13554, C_13556, D_13553)) | ~m1_subset_1(F_13558, k1_zfmisc_1(k2_zfmisc_1(D_13553, B_13557))) | ~v1_funct_2(F_13558, D_13553, B_13557) | ~v1_funct_1(F_13558) | ~m1_subset_1(E_13555, k1_zfmisc_1(k2_zfmisc_1(C_13556, B_13557))) | ~v1_funct_2(E_13555, C_13556, B_13557) | ~v1_funct_1(E_13555) | ~m1_subset_1(D_13553, k1_zfmisc_1(A_13554)) | v1_xboole_0(D_13553) | ~m1_subset_1(C_13556, k1_zfmisc_1(A_13554)) | v1_xboole_0(C_13556) | v1_xboole_0(B_13557) | v1_xboole_0(A_13554))), inference(cnfTransformation, [status(thm)], [f_164])).
% 45.65/32.91  tff(c_188242, plain, (![C_14438, B_14433, D_14435, E_14434, A_14436, F_14437]: (k2_partfun1(k4_subset_1(A_14436, C_14438, D_14435), B_14433, k1_tmap_1(A_14436, B_14433, C_14438, D_14435, E_14434, F_14437), C_14438)=E_14434 | ~v1_funct_2(k1_tmap_1(A_14436, B_14433, C_14438, D_14435, E_14434, F_14437), k4_subset_1(A_14436, C_14438, D_14435), B_14433) | ~v1_funct_1(k1_tmap_1(A_14436, B_14433, C_14438, D_14435, E_14434, F_14437)) | k2_partfun1(D_14435, B_14433, F_14437, k9_subset_1(A_14436, C_14438, D_14435))!=k2_partfun1(C_14438, B_14433, E_14434, k9_subset_1(A_14436, C_14438, D_14435)) | ~m1_subset_1(F_14437, k1_zfmisc_1(k2_zfmisc_1(D_14435, B_14433))) | ~v1_funct_2(F_14437, D_14435, B_14433) | ~v1_funct_1(F_14437) | ~m1_subset_1(E_14434, k1_zfmisc_1(k2_zfmisc_1(C_14438, B_14433))) | ~v1_funct_2(E_14434, C_14438, B_14433) | ~v1_funct_1(E_14434) | ~m1_subset_1(D_14435, k1_zfmisc_1(A_14436)) | v1_xboole_0(D_14435) | ~m1_subset_1(C_14438, k1_zfmisc_1(A_14436)) | v1_xboole_0(C_14438) | v1_xboole_0(B_14433) | v1_xboole_0(A_14436))), inference(resolution, [status(thm)], [c_62, c_129225])).
% 45.65/32.91  tff(c_207184, plain, (![E_14722, C_14726, B_14721, F_14725, D_14723, A_14724]: (k2_partfun1(k4_subset_1(A_14724, C_14726, D_14723), B_14721, k1_tmap_1(A_14724, B_14721, C_14726, D_14723, E_14722, F_14725), C_14726)=E_14722 | ~v1_funct_1(k1_tmap_1(A_14724, B_14721, C_14726, D_14723, E_14722, F_14725)) | k2_partfun1(D_14723, B_14721, F_14725, k9_subset_1(A_14724, C_14726, D_14723))!=k2_partfun1(C_14726, B_14721, E_14722, k9_subset_1(A_14724, C_14726, D_14723)) | ~m1_subset_1(F_14725, k1_zfmisc_1(k2_zfmisc_1(D_14723, B_14721))) | ~v1_funct_2(F_14725, D_14723, B_14721) | ~v1_funct_1(F_14725) | ~m1_subset_1(E_14722, k1_zfmisc_1(k2_zfmisc_1(C_14726, B_14721))) | ~v1_funct_2(E_14722, C_14726, B_14721) | ~v1_funct_1(E_14722) | ~m1_subset_1(D_14723, k1_zfmisc_1(A_14724)) | v1_xboole_0(D_14723) | ~m1_subset_1(C_14726, k1_zfmisc_1(A_14724)) | v1_xboole_0(C_14726) | v1_xboole_0(B_14721) | v1_xboole_0(A_14724))), inference(resolution, [status(thm)], [c_64, c_188242])).
% 45.65/32.91  tff(c_207205, plain, (![A_14724, C_14726, E_14722]: (k2_partfun1(k4_subset_1(A_14724, C_14726, '#skF_4'), '#skF_2', k1_tmap_1(A_14724, '#skF_2', C_14726, '#skF_4', E_14722, '#skF_6'), C_14726)=E_14722 | ~v1_funct_1(k1_tmap_1(A_14724, '#skF_2', C_14726, '#skF_4', E_14722, '#skF_6')) | k2_partfun1(C_14726, '#skF_2', E_14722, k9_subset_1(A_14724, C_14726, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_14724, C_14726, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_14722, k1_zfmisc_1(k2_zfmisc_1(C_14726, '#skF_2'))) | ~v1_funct_2(E_14722, C_14726, '#skF_2') | ~v1_funct_1(E_14722) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_14724)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_14726, k1_zfmisc_1(A_14724)) | v1_xboole_0(C_14726) | v1_xboole_0('#skF_2') | v1_xboole_0(A_14724))), inference(resolution, [status(thm)], [c_70, c_207184])).
% 45.65/32.91  tff(c_207218, plain, (![A_14724, C_14726, E_14722]: (k2_partfun1(k4_subset_1(A_14724, C_14726, '#skF_4'), '#skF_2', k1_tmap_1(A_14724, '#skF_2', C_14726, '#skF_4', E_14722, '#skF_6'), C_14726)=E_14722 | ~v1_funct_1(k1_tmap_1(A_14724, '#skF_2', C_14726, '#skF_4', E_14722, '#skF_6')) | k2_partfun1(C_14726, '#skF_2', E_14722, k9_subset_1(A_14724, C_14726, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_14724, C_14726, '#skF_4')) | ~m1_subset_1(E_14722, k1_zfmisc_1(k2_zfmisc_1(C_14726, '#skF_2'))) | ~v1_funct_2(E_14722, C_14726, '#skF_2') | ~v1_funct_1(E_14722) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_14724)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_14726, k1_zfmisc_1(A_14724)) | v1_xboole_0(C_14726) | v1_xboole_0('#skF_2') | v1_xboole_0(A_14724))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_126037, c_207205])).
% 45.65/32.91  tff(c_228136, plain, (![A_14933, C_14934, E_14935]: (k2_partfun1(k4_subset_1(A_14933, C_14934, '#skF_4'), '#skF_2', k1_tmap_1(A_14933, '#skF_2', C_14934, '#skF_4', E_14935, '#skF_6'), C_14934)=E_14935 | ~v1_funct_1(k1_tmap_1(A_14933, '#skF_2', C_14934, '#skF_4', E_14935, '#skF_6')) | k2_partfun1(C_14934, '#skF_2', E_14935, k9_subset_1(A_14933, C_14934, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_14933, C_14934, '#skF_4')) | ~m1_subset_1(E_14935, k1_zfmisc_1(k2_zfmisc_1(C_14934, '#skF_2'))) | ~v1_funct_2(E_14935, C_14934, '#skF_2') | ~v1_funct_1(E_14935) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_14933)) | ~m1_subset_1(C_14934, k1_zfmisc_1(A_14933)) | v1_xboole_0(C_14934) | v1_xboole_0(A_14933))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_207218])).
% 45.65/32.91  tff(c_228171, plain, (![A_14933]: (k2_partfun1(k4_subset_1(A_14933, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_14933, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_14933, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_14933, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_14933, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_14933)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_14933)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_14933))), inference(resolution, [status(thm)], [c_76, c_228136])).
% 45.65/32.91  tff(c_228183, plain, (![A_14933]: (k2_partfun1(k4_subset_1(A_14933, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_14933, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_14933, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_14933, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_14933, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_14933)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_14933)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_14933))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_126034, c_228171])).
% 45.65/32.91  tff(c_228291, plain, (![A_14938]: (k2_partfun1(k4_subset_1(A_14938, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_14938, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_14938, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_14938, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_14938, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_14938)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_14938)) | v1_xboole_0(A_14938))), inference(negUnitSimplification, [status(thm)], [c_90, c_228183])).
% 45.65/32.91  tff(c_3644, plain, (![C_3161, A_3162, B_3163]: (v4_relat_1(C_3161, A_3162) | ~m1_subset_1(C_3161, k1_zfmisc_1(k2_zfmisc_1(A_3162, B_3163))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 45.65/32.91  tff(c_3730, plain, (![A_3174, A_3175, B_3176]: (v4_relat_1(A_3174, A_3175) | ~r1_tarski(A_3174, k2_zfmisc_1(A_3175, B_3176)))), inference(resolution, [status(thm)], [c_28, c_3644])).
% 45.65/32.91  tff(c_3752, plain, (![A_3177, B_3178]: (v4_relat_1(k2_zfmisc_1(A_3177, B_3178), A_3177))), inference(resolution, [status(thm)], [c_14, c_3730])).
% 45.65/32.91  tff(c_3773, plain, (![A_3179]: (v4_relat_1(k1_xboole_0, A_3179))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3752])).
% 45.65/32.91  tff(c_3776, plain, (![A_3179]: (k7_relat_1(k1_xboole_0, A_3179)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_3773, c_36])).
% 45.65/32.91  tff(c_3779, plain, (![A_3179]: (k7_relat_1(k1_xboole_0, A_3179)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3776])).
% 45.65/32.91  tff(c_3878, plain, (![A_3192, B_3193]: (k7_relat_1(A_3192, B_3193)=k1_xboole_0 | ~r1_xboole_0(B_3193, k1_relat_1(A_3192)) | ~v1_relat_1(A_3192))), inference(cnfTransformation, [status(thm)], [f_68])).
% 45.65/32.91  tff(c_5446, plain, (![A_3325, B_3326]: (k7_relat_1(A_3325, k1_relat_1(B_3326))=k1_xboole_0 | ~v1_relat_1(A_3325) | k7_relat_1(B_3326, k1_relat_1(A_3325))!=k1_xboole_0 | ~v1_relat_1(B_3326))), inference(resolution, [status(thm)], [c_42, c_3878])).
% 45.65/32.91  tff(c_5474, plain, (![A_3325]: (k7_relat_1(A_3325, k1_relat_1(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_3325) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3779, c_5446])).
% 45.65/32.91  tff(c_5502, plain, (![A_3327]: (k7_relat_1(A_3327, k1_relat_1(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_3327))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_5474])).
% 45.65/32.91  tff(c_3755, plain, (![A_3177, B_3178]: (k7_relat_1(k2_zfmisc_1(A_3177, B_3178), A_3177)=k2_zfmisc_1(A_3177, B_3178) | ~v1_relat_1(k2_zfmisc_1(A_3177, B_3178)))), inference(resolution, [status(thm)], [c_3752, c_36])).
% 45.65/32.91  tff(c_3764, plain, (![A_3177, B_3178]: (k7_relat_1(k2_zfmisc_1(A_3177, B_3178), A_3177)=k2_zfmisc_1(A_3177, B_3178))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3755])).
% 45.65/32.91  tff(c_5549, plain, (![B_3178]: (k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_3178)=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_3178)))), inference(superposition, [status(thm), theory('equality')], [c_5502, c_3764])).
% 45.65/32.91  tff(c_5657, plain, (![B_3328]: (k2_zfmisc_1(k1_relat_1(k1_xboole_0), B_3328)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5549])).
% 45.65/32.91  tff(c_5722, plain, (![B_3328]: (k1_xboole_0=B_3328 | k1_relat_1(k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5657, c_16])).
% 45.65/32.91  tff(c_5729, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5722])).
% 45.65/32.91  tff(c_3792, plain, (![B_3181, A_3182]: (r1_xboole_0(k1_relat_1(B_3181), A_3182) | k7_relat_1(B_3181, A_3182)!=k1_xboole_0 | ~v1_relat_1(B_3181))), inference(cnfTransformation, [status(thm)], [f_90])).
% 45.65/32.91  tff(c_3803, plain, (![A_3182, B_3181]: (r1_xboole_0(A_3182, k1_relat_1(B_3181)) | k7_relat_1(B_3181, A_3182)!=k1_xboole_0 | ~v1_relat_1(B_3181))), inference(resolution, [status(thm)], [c_3792, c_8])).
% 45.65/32.91  tff(c_3662, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_3644])).
% 45.65/32.91  tff(c_3674, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3662, c_36])).
% 45.65/32.91  tff(c_3677, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_3674])).
% 45.65/32.91  tff(c_3942, plain, (![C_3198, A_3199, B_3200]: (k7_relat_1(k7_relat_1(C_3198, A_3199), B_3200)=k1_xboole_0 | ~r1_xboole_0(A_3199, B_3200) | ~v1_relat_1(C_3198))), inference(cnfTransformation, [status(thm)], [f_74])).
% 45.65/32.91  tff(c_3966, plain, (![B_3200]: (k7_relat_1('#skF_5', B_3200)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_3200) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3677, c_3942])).
% 45.65/32.91  tff(c_4009, plain, (![B_3202]: (k7_relat_1('#skF_5', B_3202)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_3202))), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_3966])).
% 45.65/32.91  tff(c_4033, plain, (![B_3181]: (k7_relat_1('#skF_5', k1_relat_1(B_3181))=k1_xboole_0 | k7_relat_1(B_3181, '#skF_3')!=k1_xboole_0 | ~v1_relat_1(B_3181))), inference(resolution, [status(thm)], [c_3803, c_4009])).
% 45.65/32.91  tff(c_5744, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5729, c_4033])).
% 45.65/32.91  tff(c_5787, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3779, c_5744])).
% 45.65/32.91  tff(c_3663, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_3644])).
% 45.65/32.91  tff(c_3680, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3663, c_36])).
% 45.65/32.91  tff(c_3683, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3513, c_3680])).
% 45.65/32.91  tff(c_3963, plain, (![B_3200]: (k7_relat_1('#skF_6', B_3200)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_3200) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3683, c_3942])).
% 45.65/32.91  tff(c_3979, plain, (![B_3201]: (k7_relat_1('#skF_6', B_3201)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_3201))), inference(demodulation, [status(thm), theory('equality')], [c_3513, c_3963])).
% 45.65/32.91  tff(c_4003, plain, (![B_3181]: (k7_relat_1('#skF_6', k1_relat_1(B_3181))=k1_xboole_0 | k7_relat_1(B_3181, '#skF_4')!=k1_xboole_0 | ~v1_relat_1(B_3181))), inference(resolution, [status(thm)], [c_3803, c_3979])).
% 45.65/32.91  tff(c_5747, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5729, c_4003])).
% 45.65/32.91  tff(c_5789, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_3779, c_5747])).
% 45.65/32.91  tff(c_3664, plain, (![A_3164, B_3165]: (r1_xboole_0(A_3164, B_3165) | ~r1_subset_1(A_3164, B_3165) | v1_xboole_0(B_3165) | v1_xboole_0(A_3164))), inference(cnfTransformation, [status(thm)], [f_100])).
% 45.65/32.91  tff(c_4765, plain, (![A_3273, B_3274]: (k3_xboole_0(A_3273, B_3274)=k1_xboole_0 | ~r1_subset_1(A_3273, B_3274) | v1_xboole_0(B_3274) | v1_xboole_0(A_3273))), inference(resolution, [status(thm)], [c_3664, c_4])).
% 45.65/32.91  tff(c_4774, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_82, c_4765])).
% 45.65/32.91  tff(c_4780, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4774])).
% 45.65/32.91  tff(c_4781, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_86, c_4780])).
% 45.65/32.91  tff(c_4122, plain, (![A_3206, B_3207, C_3208]: (k9_subset_1(A_3206, B_3207, C_3208)=k3_xboole_0(B_3207, C_3208) | ~m1_subset_1(C_3208, k1_zfmisc_1(A_3206)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 45.65/32.91  tff(c_4137, plain, (![B_3207]: (k9_subset_1('#skF_1', B_3207, '#skF_4')=k3_xboole_0(B_3207, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_4122])).
% 45.65/32.91  tff(c_4485, plain, (![E_3244, A_3246, D_3245, C_3248, B_3243, F_3247]: (v1_funct_1(k1_tmap_1(A_3246, B_3243, C_3248, D_3245, E_3244, F_3247)) | ~m1_subset_1(F_3247, k1_zfmisc_1(k2_zfmisc_1(D_3245, B_3243))) | ~v1_funct_2(F_3247, D_3245, B_3243) | ~v1_funct_1(F_3247) | ~m1_subset_1(E_3244, k1_zfmisc_1(k2_zfmisc_1(C_3248, B_3243))) | ~v1_funct_2(E_3244, C_3248, B_3243) | ~v1_funct_1(E_3244) | ~m1_subset_1(D_3245, k1_zfmisc_1(A_3246)) | v1_xboole_0(D_3245) | ~m1_subset_1(C_3248, k1_zfmisc_1(A_3246)) | v1_xboole_0(C_3248) | v1_xboole_0(B_3243) | v1_xboole_0(A_3246))), inference(cnfTransformation, [status(thm)], [f_198])).
% 45.65/32.91  tff(c_4492, plain, (![A_3246, C_3248, E_3244]: (v1_funct_1(k1_tmap_1(A_3246, '#skF_2', C_3248, '#skF_4', E_3244, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3244, k1_zfmisc_1(k2_zfmisc_1(C_3248, '#skF_2'))) | ~v1_funct_2(E_3244, C_3248, '#skF_2') | ~v1_funct_1(E_3244) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3246)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3248, k1_zfmisc_1(A_3246)) | v1_xboole_0(C_3248) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3246))), inference(resolution, [status(thm)], [c_70, c_4485])).
% 45.65/32.91  tff(c_4504, plain, (![A_3246, C_3248, E_3244]: (v1_funct_1(k1_tmap_1(A_3246, '#skF_2', C_3248, '#skF_4', E_3244, '#skF_6')) | ~m1_subset_1(E_3244, k1_zfmisc_1(k2_zfmisc_1(C_3248, '#skF_2'))) | ~v1_funct_2(E_3244, C_3248, '#skF_2') | ~v1_funct_1(E_3244) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3246)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3248, k1_zfmisc_1(A_3246)) | v1_xboole_0(C_3248) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3246))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4492])).
% 45.65/32.91  tff(c_4592, plain, (![A_3253, C_3254, E_3255]: (v1_funct_1(k1_tmap_1(A_3253, '#skF_2', C_3254, '#skF_4', E_3255, '#skF_6')) | ~m1_subset_1(E_3255, k1_zfmisc_1(k2_zfmisc_1(C_3254, '#skF_2'))) | ~v1_funct_2(E_3255, C_3254, '#skF_2') | ~v1_funct_1(E_3255) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3253)) | ~m1_subset_1(C_3254, k1_zfmisc_1(A_3253)) | v1_xboole_0(C_3254) | v1_xboole_0(A_3253))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_4504])).
% 45.65/32.91  tff(c_4597, plain, (![A_3253]: (v1_funct_1(k1_tmap_1(A_3253, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3253)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3253)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3253))), inference(resolution, [status(thm)], [c_76, c_4592])).
% 45.65/32.91  tff(c_4606, plain, (![A_3253]: (v1_funct_1(k1_tmap_1(A_3253, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3253)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3253)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_3253))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_4597])).
% 45.65/32.91  tff(c_4995, plain, (![A_3288]: (v1_funct_1(k1_tmap_1(A_3288, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3288)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_3288)) | v1_xboole_0(A_3288))), inference(negUnitSimplification, [status(thm)], [c_90, c_4606])).
% 45.65/32.91  tff(c_5002, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_4995])).
% 45.65/32.91  tff(c_5006, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5002])).
% 45.65/32.91  tff(c_5007, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_94, c_5006])).
% 45.65/32.91  tff(c_4398, plain, (![A_3228, B_3229, C_3230, D_3231]: (k2_partfun1(A_3228, B_3229, C_3230, D_3231)=k7_relat_1(C_3230, D_3231) | ~m1_subset_1(C_3230, k1_zfmisc_1(k2_zfmisc_1(A_3228, B_3229))) | ~v1_funct_1(C_3230))), inference(cnfTransformation, [status(thm)], [f_116])).
% 45.65/32.91  tff(c_4403, plain, (![D_3231]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_3231)=k7_relat_1('#skF_5', D_3231) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_4398])).
% 45.65/32.91  tff(c_4413, plain, (![D_3231]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_3231)=k7_relat_1('#skF_5', D_3231))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4403])).
% 45.65/32.91  tff(c_4405, plain, (![D_3231]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_3231)=k7_relat_1('#skF_6', D_3231) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_70, c_4398])).
% 45.65/32.91  tff(c_4416, plain, (![D_3231]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_3231)=k7_relat_1('#skF_6', D_3231))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4405])).
% 45.65/32.91  tff(c_5065, plain, (![A_3294, B_3297, D_3293, C_3296, E_3295, F_3298]: (k2_partfun1(k4_subset_1(A_3294, C_3296, D_3293), B_3297, k1_tmap_1(A_3294, B_3297, C_3296, D_3293, E_3295, F_3298), D_3293)=F_3298 | ~m1_subset_1(k1_tmap_1(A_3294, B_3297, C_3296, D_3293, E_3295, F_3298), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_3294, C_3296, D_3293), B_3297))) | ~v1_funct_2(k1_tmap_1(A_3294, B_3297, C_3296, D_3293, E_3295, F_3298), k4_subset_1(A_3294, C_3296, D_3293), B_3297) | ~v1_funct_1(k1_tmap_1(A_3294, B_3297, C_3296, D_3293, E_3295, F_3298)) | k2_partfun1(D_3293, B_3297, F_3298, k9_subset_1(A_3294, C_3296, D_3293))!=k2_partfun1(C_3296, B_3297, E_3295, k9_subset_1(A_3294, C_3296, D_3293)) | ~m1_subset_1(F_3298, k1_zfmisc_1(k2_zfmisc_1(D_3293, B_3297))) | ~v1_funct_2(F_3298, D_3293, B_3297) | ~v1_funct_1(F_3298) | ~m1_subset_1(E_3295, k1_zfmisc_1(k2_zfmisc_1(C_3296, B_3297))) | ~v1_funct_2(E_3295, C_3296, B_3297) | ~v1_funct_1(E_3295) | ~m1_subset_1(D_3293, k1_zfmisc_1(A_3294)) | v1_xboole_0(D_3293) | ~m1_subset_1(C_3296, k1_zfmisc_1(A_3294)) | v1_xboole_0(C_3296) | v1_xboole_0(B_3297) | v1_xboole_0(A_3294))), inference(cnfTransformation, [status(thm)], [f_164])).
% 45.65/32.91  tff(c_12393, plain, (![B_3505, E_3506, F_3509, A_3508, D_3507, C_3510]: (k2_partfun1(k4_subset_1(A_3508, C_3510, D_3507), B_3505, k1_tmap_1(A_3508, B_3505, C_3510, D_3507, E_3506, F_3509), D_3507)=F_3509 | ~v1_funct_2(k1_tmap_1(A_3508, B_3505, C_3510, D_3507, E_3506, F_3509), k4_subset_1(A_3508, C_3510, D_3507), B_3505) | ~v1_funct_1(k1_tmap_1(A_3508, B_3505, C_3510, D_3507, E_3506, F_3509)) | k2_partfun1(D_3507, B_3505, F_3509, k9_subset_1(A_3508, C_3510, D_3507))!=k2_partfun1(C_3510, B_3505, E_3506, k9_subset_1(A_3508, C_3510, D_3507)) | ~m1_subset_1(F_3509, k1_zfmisc_1(k2_zfmisc_1(D_3507, B_3505))) | ~v1_funct_2(F_3509, D_3507, B_3505) | ~v1_funct_1(F_3509) | ~m1_subset_1(E_3506, k1_zfmisc_1(k2_zfmisc_1(C_3510, B_3505))) | ~v1_funct_2(E_3506, C_3510, B_3505) | ~v1_funct_1(E_3506) | ~m1_subset_1(D_3507, k1_zfmisc_1(A_3508)) | v1_xboole_0(D_3507) | ~m1_subset_1(C_3510, k1_zfmisc_1(A_3508)) | v1_xboole_0(C_3510) | v1_xboole_0(B_3505) | v1_xboole_0(A_3508))), inference(resolution, [status(thm)], [c_62, c_5065])).
% 45.65/32.91  tff(c_30263, plain, (![D_3769, C_3772, B_3767, E_3768, A_3770, F_3771]: (k2_partfun1(k4_subset_1(A_3770, C_3772, D_3769), B_3767, k1_tmap_1(A_3770, B_3767, C_3772, D_3769, E_3768, F_3771), D_3769)=F_3771 | ~v1_funct_1(k1_tmap_1(A_3770, B_3767, C_3772, D_3769, E_3768, F_3771)) | k2_partfun1(D_3769, B_3767, F_3771, k9_subset_1(A_3770, C_3772, D_3769))!=k2_partfun1(C_3772, B_3767, E_3768, k9_subset_1(A_3770, C_3772, D_3769)) | ~m1_subset_1(F_3771, k1_zfmisc_1(k2_zfmisc_1(D_3769, B_3767))) | ~v1_funct_2(F_3771, D_3769, B_3767) | ~v1_funct_1(F_3771) | ~m1_subset_1(E_3768, k1_zfmisc_1(k2_zfmisc_1(C_3772, B_3767))) | ~v1_funct_2(E_3768, C_3772, B_3767) | ~v1_funct_1(E_3768) | ~m1_subset_1(D_3769, k1_zfmisc_1(A_3770)) | v1_xboole_0(D_3769) | ~m1_subset_1(C_3772, k1_zfmisc_1(A_3770)) | v1_xboole_0(C_3772) | v1_xboole_0(B_3767) | v1_xboole_0(A_3770))), inference(resolution, [status(thm)], [c_64, c_12393])).
% 45.65/32.91  tff(c_30284, plain, (![A_3770, C_3772, E_3768]: (k2_partfun1(k4_subset_1(A_3770, C_3772, '#skF_4'), '#skF_2', k1_tmap_1(A_3770, '#skF_2', C_3772, '#skF_4', E_3768, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3770, '#skF_2', C_3772, '#skF_4', E_3768, '#skF_6')) | k2_partfun1(C_3772, '#skF_2', E_3768, k9_subset_1(A_3770, C_3772, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_3770, C_3772, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3768, k1_zfmisc_1(k2_zfmisc_1(C_3772, '#skF_2'))) | ~v1_funct_2(E_3768, C_3772, '#skF_2') | ~v1_funct_1(E_3768) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3770)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3772, k1_zfmisc_1(A_3770)) | v1_xboole_0(C_3772) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3770))), inference(resolution, [status(thm)], [c_70, c_30263])).
% 45.65/32.91  tff(c_30297, plain, (![A_3770, C_3772, E_3768]: (k2_partfun1(k4_subset_1(A_3770, C_3772, '#skF_4'), '#skF_2', k1_tmap_1(A_3770, '#skF_2', C_3772, '#skF_4', E_3768, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_3770, '#skF_2', C_3772, '#skF_4', E_3768, '#skF_6')) | k2_partfun1(C_3772, '#skF_2', E_3768, k9_subset_1(A_3770, C_3772, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_3770, C_3772, '#skF_4')) | ~m1_subset_1(E_3768, k1_zfmisc_1(k2_zfmisc_1(C_3772, '#skF_2'))) | ~v1_funct_2(E_3768, C_3772, '#skF_2') | ~v1_funct_1(E_3768) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_3770)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_3772, k1_zfmisc_1(A_3770)) | v1_xboole_0(C_3772) | v1_xboole_0('#skF_2') | v1_xboole_0(A_3770))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4416, c_30284])).
% 45.65/32.91  tff(c_61566, plain, (![A_4042, C_4043, E_4044]: (k2_partfun1(k4_subset_1(A_4042, C_4043, '#skF_4'), '#skF_2', k1_tmap_1(A_4042, '#skF_2', C_4043, '#skF_4', E_4044, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4042, '#skF_2', C_4043, '#skF_4', E_4044, '#skF_6')) | k2_partfun1(C_4043, '#skF_2', E_4044, k9_subset_1(A_4042, C_4043, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4042, C_4043, '#skF_4')) | ~m1_subset_1(E_4044, k1_zfmisc_1(k2_zfmisc_1(C_4043, '#skF_2'))) | ~v1_funct_2(E_4044, C_4043, '#skF_2') | ~v1_funct_1(E_4044) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4042)) | ~m1_subset_1(C_4043, k1_zfmisc_1(A_4042)) | v1_xboole_0(C_4043) | v1_xboole_0(A_4042))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_30297])).
% 45.65/32.91  tff(c_61598, plain, (![A_4042]: (k2_partfun1(k4_subset_1(A_4042, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4042, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4042, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_4042, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4042, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4042)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4042)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4042))), inference(resolution, [status(thm)], [c_76, c_61566])).
% 45.65/32.91  tff(c_61610, plain, (![A_4042]: (k2_partfun1(k4_subset_1(A_4042, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4042, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4042, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4042, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4042, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4042)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4042)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_4042))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_4413, c_61598])).
% 45.65/32.91  tff(c_63171, plain, (![A_4051]: (k2_partfun1(k4_subset_1(A_4051, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_4051, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_4051, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_4051, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_4051, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4051)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_4051)) | v1_xboole_0(A_4051))), inference(negUnitSimplification, [status(thm)], [c_90, c_61610])).
% 45.65/32.91  tff(c_3486, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_68])).
% 45.65/32.91  tff(c_3629, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_3486])).
% 45.65/32.91  tff(c_63188, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_63171, c_3629])).
% 45.65/32.91  tff(c_63210, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_5787, c_5789, c_4781, c_4781, c_2, c_4137, c_2, c_4137, c_5007, c_63188])).
% 45.65/32.91  tff(c_63212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_63210])).
% 45.65/32.91  tff(c_63215, plain, (![B_4052]: (k1_xboole_0=B_4052)), inference(splitRight, [status(thm)], [c_5722])).
% 45.65/32.91  tff(c_3853, plain, (![B_3190, A_3191]: (k3_xboole_0(k1_relat_1(B_3190), A_3191)=k1_relat_1(k7_relat_1(B_3190, A_3191)) | ~v1_relat_1(B_3190))), inference(cnfTransformation, [status(thm)], [f_84])).
% 45.65/32.91  tff(c_4556, plain, (![B_3251, B_3252]: (k3_xboole_0(B_3251, k1_relat_1(B_3252))=k1_relat_1(k7_relat_1(B_3252, B_3251)) | ~v1_relat_1(B_3252))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3853])).
% 45.65/32.91  tff(c_5179, plain, (![B_3310, B_3311]: (k3_xboole_0(k1_relat_1(B_3310), B_3311)=k1_xboole_0 | k1_relat_1(k7_relat_1(B_3310, B_3311))!=k1_xboole_0 | ~v1_relat_1(B_3310))), inference(superposition, [status(thm), theory('equality')], [c_4556, c_3494])).
% 45.65/32.91  tff(c_3709, plain, (![B_3170, A_3171]: (k7_relat_1(B_3170, A_3171)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_3170), A_3171) | ~v1_relat_1(B_3170))), inference(cnfTransformation, [status(thm)], [f_90])).
% 45.65/32.91  tff(c_3724, plain, (![B_3170, B_4]: (k7_relat_1(B_3170, B_4)=k1_xboole_0 | ~v1_relat_1(B_3170) | k3_xboole_0(k1_relat_1(B_3170), B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_3709])).
% 45.65/32.91  tff(c_5262, plain, (![B_3313, B_3314]: (k7_relat_1(B_3313, B_3314)=k1_xboole_0 | k1_relat_1(k7_relat_1(B_3313, B_3314))!=k1_xboole_0 | ~v1_relat_1(B_3313))), inference(superposition, [status(thm), theory('equality')], [c_5179, c_3724])).
% 45.65/32.91  tff(c_5304, plain, (k7_relat_1('#skF_5', '#skF_3')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3677, c_5262])).
% 45.65/32.91  tff(c_5330, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3512, c_3677, c_5304])).
% 45.65/32.91  tff(c_5332, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5330])).
% 45.65/32.91  tff(c_63514, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_63215, c_5332])).
% 45.65/32.91  tff(c_63515, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_5330])).
% 45.65/32.91  tff(c_63555, plain, (![A_3179]: (k7_relat_1('#skF_5', A_3179)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63515, c_63515, c_3779])).
% 45.65/32.91  tff(c_63767, plain, (![D_3231]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_3231)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63555, c_4413])).
% 45.65/32.91  tff(c_63526, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_63515, c_4781])).
% 45.65/32.91  tff(c_4147, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_4137, c_3487])).
% 45.65/32.91  tff(c_4148, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_4', '#skF_3'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_4147])).
% 45.65/32.91  tff(c_63788, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', '#skF_5')=k7_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63526, c_63526, c_4416, c_4148])).
% 45.65/32.91  tff(c_63802, plain, (k7_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_63767, c_63788])).
% 45.65/32.91  tff(c_4136, plain, (![B_3207]: (k9_subset_1('#skF_1', B_3207, '#skF_3')=k3_xboole_0(B_3207, '#skF_3'))), inference(resolution, [status(thm)], [c_88, c_4122])).
% 45.65/32.91  tff(c_4225, plain, (![A_3215, C_3216, B_3217]: (k9_subset_1(A_3215, C_3216, B_3217)=k9_subset_1(A_3215, B_3217, C_3216) | ~m1_subset_1(C_3216, k1_zfmisc_1(A_3215)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 45.65/32.91  tff(c_4233, plain, (![B_3217]: (k9_subset_1('#skF_1', B_3217, '#skF_3')=k9_subset_1('#skF_1', '#skF_3', B_3217))), inference(resolution, [status(thm)], [c_88, c_4225])).
% 45.65/32.91  tff(c_4242, plain, (![B_3217]: (k9_subset_1('#skF_1', '#skF_3', B_3217)=k3_xboole_0(B_3217, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4136, c_4233])).
% 45.65/32.91  tff(c_66629, plain, (![A_6910, F_6911, C_6912, E_6908, B_6907, D_6909]: (k2_partfun1(k4_subset_1(A_6910, C_6912, D_6909), B_6907, k1_tmap_1(A_6910, B_6907, C_6912, D_6909, E_6908, F_6911), D_6909)=F_6911 | ~v1_funct_2(k1_tmap_1(A_6910, B_6907, C_6912, D_6909, E_6908, F_6911), k4_subset_1(A_6910, C_6912, D_6909), B_6907) | ~v1_funct_1(k1_tmap_1(A_6910, B_6907, C_6912, D_6909, E_6908, F_6911)) | k2_partfun1(D_6909, B_6907, F_6911, k9_subset_1(A_6910, C_6912, D_6909))!=k2_partfun1(C_6912, B_6907, E_6908, k9_subset_1(A_6910, C_6912, D_6909)) | ~m1_subset_1(F_6911, k1_zfmisc_1(k2_zfmisc_1(D_6909, B_6907))) | ~v1_funct_2(F_6911, D_6909, B_6907) | ~v1_funct_1(F_6911) | ~m1_subset_1(E_6908, k1_zfmisc_1(k2_zfmisc_1(C_6912, B_6907))) | ~v1_funct_2(E_6908, C_6912, B_6907) | ~v1_funct_1(E_6908) | ~m1_subset_1(D_6909, k1_zfmisc_1(A_6910)) | v1_xboole_0(D_6909) | ~m1_subset_1(C_6912, k1_zfmisc_1(A_6910)) | v1_xboole_0(C_6912) | v1_xboole_0(B_6907) | v1_xboole_0(A_6910))), inference(resolution, [status(thm)], [c_62, c_5065])).
% 45.65/32.91  tff(c_83133, plain, (![E_7226, B_7225, A_7228, D_7227, C_7230, F_7229]: (k2_partfun1(k4_subset_1(A_7228, C_7230, D_7227), B_7225, k1_tmap_1(A_7228, B_7225, C_7230, D_7227, E_7226, F_7229), D_7227)=F_7229 | ~v1_funct_1(k1_tmap_1(A_7228, B_7225, C_7230, D_7227, E_7226, F_7229)) | k2_partfun1(D_7227, B_7225, F_7229, k9_subset_1(A_7228, C_7230, D_7227))!=k2_partfun1(C_7230, B_7225, E_7226, k9_subset_1(A_7228, C_7230, D_7227)) | ~m1_subset_1(F_7229, k1_zfmisc_1(k2_zfmisc_1(D_7227, B_7225))) | ~v1_funct_2(F_7229, D_7227, B_7225) | ~v1_funct_1(F_7229) | ~m1_subset_1(E_7226, k1_zfmisc_1(k2_zfmisc_1(C_7230, B_7225))) | ~v1_funct_2(E_7226, C_7230, B_7225) | ~v1_funct_1(E_7226) | ~m1_subset_1(D_7227, k1_zfmisc_1(A_7228)) | v1_xboole_0(D_7227) | ~m1_subset_1(C_7230, k1_zfmisc_1(A_7228)) | v1_xboole_0(C_7230) | v1_xboole_0(B_7225) | v1_xboole_0(A_7228))), inference(resolution, [status(thm)], [c_64, c_66629])).
% 45.65/32.91  tff(c_83158, plain, (![A_7228, C_7230, E_7226]: (k2_partfun1(k4_subset_1(A_7228, C_7230, '#skF_4'), '#skF_2', k1_tmap_1(A_7228, '#skF_2', C_7230, '#skF_4', E_7226, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_7228, '#skF_2', C_7230, '#skF_4', E_7226, '#skF_6')) | k2_partfun1(C_7230, '#skF_2', E_7226, k9_subset_1(A_7228, C_7230, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_7228, C_7230, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_7226, k1_zfmisc_1(k2_zfmisc_1(C_7230, '#skF_2'))) | ~v1_funct_2(E_7226, C_7230, '#skF_2') | ~v1_funct_1(E_7226) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7228)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_7230, k1_zfmisc_1(A_7228)) | v1_xboole_0(C_7230) | v1_xboole_0('#skF_2') | v1_xboole_0(A_7228))), inference(resolution, [status(thm)], [c_70, c_83133])).
% 45.65/32.91  tff(c_83169, plain, (![A_7228, C_7230, E_7226]: (k2_partfun1(k4_subset_1(A_7228, C_7230, '#skF_4'), '#skF_2', k1_tmap_1(A_7228, '#skF_2', C_7230, '#skF_4', E_7226, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_7228, '#skF_2', C_7230, '#skF_4', E_7226, '#skF_6')) | k2_partfun1(C_7230, '#skF_2', E_7226, k9_subset_1(A_7228, C_7230, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_7228, C_7230, '#skF_4')) | ~m1_subset_1(E_7226, k1_zfmisc_1(k2_zfmisc_1(C_7230, '#skF_2'))) | ~v1_funct_2(E_7226, C_7230, '#skF_2') | ~v1_funct_1(E_7226) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7228)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_7230, k1_zfmisc_1(A_7228)) | v1_xboole_0(C_7230) | v1_xboole_0('#skF_2') | v1_xboole_0(A_7228))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4416, c_83158])).
% 45.65/32.91  tff(c_112657, plain, (![A_7547, C_7548, E_7549]: (k2_partfun1(k4_subset_1(A_7547, C_7548, '#skF_4'), '#skF_2', k1_tmap_1(A_7547, '#skF_2', C_7548, '#skF_4', E_7549, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_7547, '#skF_2', C_7548, '#skF_4', E_7549, '#skF_6')) | k2_partfun1(C_7548, '#skF_2', E_7549, k9_subset_1(A_7547, C_7548, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_7547, C_7548, '#skF_4')) | ~m1_subset_1(E_7549, k1_zfmisc_1(k2_zfmisc_1(C_7548, '#skF_2'))) | ~v1_funct_2(E_7549, C_7548, '#skF_2') | ~v1_funct_1(E_7549) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7547)) | ~m1_subset_1(C_7548, k1_zfmisc_1(A_7547)) | v1_xboole_0(C_7548) | v1_xboole_0(A_7547))), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_83169])).
% 45.65/32.91  tff(c_112692, plain, (![A_7547]: (k2_partfun1(k4_subset_1(A_7547, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_7547, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_7547, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_7547, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_7547, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7547)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_7547)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_7547))), inference(resolution, [status(thm)], [c_76, c_112657])).
% 45.65/32.91  tff(c_112702, plain, (![A_7547]: (k2_partfun1(k4_subset_1(A_7547, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_7547, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_7547, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_6', k9_subset_1(A_7547, '#skF_3', '#skF_4'))!='#skF_5' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7547)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_7547)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_7547))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_63767, c_112692])).
% 45.65/32.91  tff(c_125113, plain, (![A_7675]: (k2_partfun1(k4_subset_1(A_7675, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_7675, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_7675, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_6', k9_subset_1(A_7675, '#skF_3', '#skF_4'))!='#skF_5' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_7675)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_7675)) | v1_xboole_0(A_7675))), inference(negUnitSimplification, [status(thm)], [c_90, c_112702])).
% 45.65/32.91  tff(c_125136, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!='#skF_5' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_125113, c_3629])).
% 45.65/32.91  tff(c_125172, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_63802, c_63526, c_4242, c_5007, c_125136])).
% 45.65/32.91  tff(c_125174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_125172])).
% 45.65/32.91  tff(c_125175, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_3486])).
% 45.65/32.91  tff(c_228311, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_228291, c_125175])).
% 45.65/32.91  tff(c_228336, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_128747, c_126207, c_125795, c_128749, c_126207, c_125795, c_129930, c_228311])).
% 45.65/32.91  tff(c_228338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_228336])).
% 45.65/32.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.65/32.91  
% 45.65/32.91  Inference rules
% 45.65/32.91  ----------------------
% 45.65/32.91  #Ref     : 0
% 45.65/32.91  #Sup     : 49056
% 45.65/32.91  #Fact    : 0
% 45.65/32.91  #Define  : 0
% 45.65/32.91  #Split   : 93
% 45.65/32.91  #Chain   : 0
% 45.65/32.91  #Close   : 0
% 45.65/32.91  
% 45.65/32.91  Ordering : KBO
% 45.65/32.91  
% 45.65/32.91  Simplification rules
% 45.65/32.91  ----------------------
% 45.65/32.91  #Subsume      : 10708
% 45.65/32.91  #Demod        : 78036
% 45.65/32.91  #Tautology    : 23776
% 45.65/32.91  #SimpNegUnit  : 1068
% 45.65/32.91  #BackRed      : 135
% 45.65/32.91  
% 45.65/32.91  #Partial instantiations: 2706
% 45.65/32.91  #Strategies tried      : 1
% 45.65/32.91  
% 45.65/32.91  Timing (in seconds)
% 45.65/32.91  ----------------------
% 45.65/32.91  Preprocessing        : 0.58
% 45.65/32.91  Parsing              : 0.31
% 45.65/32.91  CNF conversion       : 0.07
% 45.65/32.91  Main loop            : 31.34
% 45.65/32.91  Inferencing          : 5.32
% 45.65/32.91  Reduction            : 13.78
% 45.65/32.91  Demodulation         : 11.36
% 45.65/32.91  BG Simplification    : 0.64
% 45.65/32.91  Subsumption          : 10.37
% 45.65/32.91  Abstraction          : 0.99
% 45.65/32.91  MUC search           : 0.00
% 45.65/32.91  Cooper               : 0.00
% 45.65/32.91  Total                : 32.06
% 45.65/32.91  Index Insertion      : 0.00
% 45.65/32.91  Index Deletion       : 0.00
% 45.65/32.91  Index Matching       : 0.00
% 45.65/32.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
