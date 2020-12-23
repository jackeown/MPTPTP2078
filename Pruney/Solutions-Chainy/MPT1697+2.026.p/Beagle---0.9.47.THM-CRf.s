%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:13 EST 2020

% Result     : Theorem 10.20s
% Output     : CNFRefutation 10.57s
% Verified   : 
% Statistics : Number of formulae       :  275 (2476 expanded)
%              Number of leaves         :   45 ( 841 expanded)
%              Depth                    :   20
%              Number of atoms          :  806 (10440 expanded)
%              Number of equality atoms :  208 (2190 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

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

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_10539,plain,(
    ! [A_956,B_957,C_958,D_959] :
      ( k2_partfun1(A_956,B_957,C_958,D_959) = k7_relat_1(C_958,D_959)
      | ~ m1_subset_1(C_958,k1_zfmisc_1(k2_zfmisc_1(A_956,B_957)))
      | ~ v1_funct_1(C_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10543,plain,(
    ! [D_959] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_959) = k7_relat_1('#skF_5',D_959)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_10539])).

tff(c_10565,plain,(
    ! [D_961] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_961) = k7_relat_1('#skF_5',D_961) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10543])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_66,plain,(
    r1_subset_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | ~ r1_subset_1(A_16,B_17)
      | v1_xboole_0(B_17)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_93,plain,(
    ! [C_228,A_229,B_230] :
      ( v1_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_100,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_1770,plain,(
    ! [C_390,A_391,B_392] :
      ( v4_relat_1(C_390,A_391)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_391,B_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1777,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1770])).

tff(c_1829,plain,(
    ! [B_402,A_403] :
      ( k1_relat_1(B_402) = A_403
      | ~ v1_partfun1(B_402,A_403)
      | ~ v4_relat_1(B_402,A_403)
      | ~ v1_relat_1(B_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1835,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1777,c_1829])).

tff(c_1841,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1835])).

tff(c_9666,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1841])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_10077,plain,(
    ! [C_929,A_930,B_931] :
      ( v1_partfun1(C_929,A_930)
      | ~ v1_funct_2(C_929,A_930,B_931)
      | ~ v1_funct_1(C_929)
      | ~ m1_subset_1(C_929,k1_zfmisc_1(k2_zfmisc_1(A_930,B_931)))
      | v1_xboole_0(B_931) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10080,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_10077])).

tff(c_10086,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_10080])).

tff(c_10088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9666,c_10086])).

tff(c_10089,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1841])).

tff(c_10,plain,(
    ! [A_9,B_11] :
      ( k7_relat_1(A_9,B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,k1_relat_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10100,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_6',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10089,c_10])).

tff(c_10134,plain,(
    ! [B_933] :
      ( k7_relat_1('#skF_6',B_933) = k1_xboole_0
      | ~ r1_xboole_0(B_933,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_10100])).

tff(c_10138,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_10134])).

tff(c_10264,plain,(
    ! [A_948] :
      ( k7_relat_1('#skF_6',A_948) = k1_xboole_0
      | ~ r1_subset_1(A_948,'#skF_4')
      | v1_xboole_0(A_948) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_10138])).

tff(c_10267,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_10264])).

tff(c_10270,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10267])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k1_relat_1(B_15),A_14) = k1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10097,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10089,c_18])).

tff(c_10106,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_10097])).

tff(c_10344,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10270,c_10106])).

tff(c_10351,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10344])).

tff(c_10271,plain,(
    ! [B_949,A_950] :
      ( k7_relat_1(B_949,k3_xboole_0(k1_relat_1(B_949),A_950)) = k7_relat_1(B_949,A_950)
      | ~ v1_relat_1(B_949) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10310,plain,(
    ! [A_950] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_950)) = k7_relat_1('#skF_6',A_950)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10089,c_10271])).

tff(c_10374,plain,(
    ! [A_951] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_951)) = k7_relat_1('#skF_6',A_951) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_10310])).

tff(c_10389,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10351,c_10374])).

tff(c_10396,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10270,c_10389])).

tff(c_10541,plain,(
    ! [D_959] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_959) = k7_relat_1('#skF_6',D_959)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_10539])).

tff(c_10546,plain,(
    ! [D_959] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_959) = k7_relat_1('#skF_6',D_959) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10541])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_1778,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1770])).

tff(c_1832,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1778,c_1829])).

tff(c_1838,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1832])).

tff(c_1842,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1838])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_2514,plain,(
    ! [C_464,A_465,B_466] :
      ( v1_partfun1(C_464,A_465)
      | ~ v1_funct_2(C_464,A_465,B_466)
      | ~ v1_funct_1(C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_465,B_466)))
      | v1_xboole_0(B_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2520,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2514])).

tff(c_2527,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2520])).

tff(c_2529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1842,c_2527])).

tff(c_2530,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1838])).

tff(c_2541,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_5',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2530,c_10])).

tff(c_10166,plain,(
    ! [B_935] :
      ( k7_relat_1('#skF_5',B_935) = k1_xboole_0
      | ~ r1_xboole_0(B_935,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2541])).

tff(c_10224,plain,(
    ! [A_942] :
      ( k7_relat_1('#skF_5',A_942) = k1_xboole_0
      | k3_xboole_0(A_942,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_10166])).

tff(c_2538,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2530,c_18])).

tff(c_2547,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2538])).

tff(c_10230,plain,(
    ! [A_942] :
      ( k3_xboole_0('#skF_3',A_942) = k1_relat_1(k1_xboole_0)
      | k3_xboole_0(A_942,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10224,c_2547])).

tff(c_10235,plain,(
    ! [A_942] :
      ( k3_xboole_0('#skF_3',A_942) = k1_xboole_0
      | k3_xboole_0(A_942,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10230])).

tff(c_10359,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10351,c_10235])).

tff(c_10192,plain,(
    ! [A_937,B_938,C_939] :
      ( k9_subset_1(A_937,B_938,C_939) = k3_xboole_0(B_938,C_939)
      | ~ m1_subset_1(C_939,k1_zfmisc_1(A_937)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10204,plain,(
    ! [B_938] : k9_subset_1('#skF_1',B_938,'#skF_4') = k3_xboole_0(B_938,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_10192])).

tff(c_133,plain,(
    ! [C_236,A_237,B_238] :
      ( v4_relat_1(C_236,A_237)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_140,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_133])).

tff(c_235,plain,(
    ! [B_255,A_256] :
      ( k1_relat_1(B_255) = A_256
      | ~ v1_partfun1(B_255,A_256)
      | ~ v4_relat_1(B_255,A_256)
      | ~ v1_relat_1(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_241,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_140,c_235])).

tff(c_247,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_241])).

tff(c_573,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_729,plain,(
    ! [C_310,A_311,B_312] :
      ( v1_partfun1(C_310,A_311)
      | ~ v1_funct_2(C_310,A_311,B_312)
      | ~ v1_funct_1(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312)))
      | v1_xboole_0(B_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_732,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_729])).

tff(c_738,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_732])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_573,c_738])).

tff(c_741,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_749,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_6',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_10])).

tff(c_818,plain,(
    ! [B_316] :
      ( k7_relat_1('#skF_6',B_316) = k1_xboole_0
      | ~ r1_xboole_0(B_316,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_749])).

tff(c_822,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_818])).

tff(c_914,plain,(
    ! [A_326] :
      ( k7_relat_1('#skF_6',A_326) = k1_xboole_0
      | ~ r1_subset_1(A_326,'#skF_4')
      | v1_xboole_0(A_326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_822])).

tff(c_917,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_914])).

tff(c_920,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_917])).

tff(c_752,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_18])).

tff(c_763,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_752])).

tff(c_924,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_763])).

tff(c_927,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_924])).

tff(c_141,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_133])).

tff(c_238,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_141,c_235])).

tff(c_244,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_238])).

tff(c_248,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_521,plain,(
    ! [C_291,A_292,B_293] :
      ( v1_partfun1(C_291,A_292)
      | ~ v1_funct_2(C_291,A_292,B_293)
      | ~ v1_funct_1(C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293)))
      | v1_xboole_0(B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_527,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_521])).

tff(c_534,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_527])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_248,c_534])).

tff(c_537,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_545,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_5',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_10])).

tff(c_805,plain,(
    ! [B_315] :
      ( k7_relat_1('#skF_5',B_315) = k1_xboole_0
      | ~ r1_xboole_0(B_315,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_545])).

tff(c_1067,plain,(
    ! [A_334] :
      ( k7_relat_1('#skF_5',A_334) = k1_xboole_0
      | k3_xboole_0(A_334,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_805])).

tff(c_548,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_18])).

tff(c_559,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_5',A_14)) = k3_xboole_0('#skF_3',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_548])).

tff(c_1076,plain,(
    ! [A_334] :
      ( k3_xboole_0('#skF_3',A_334) = k1_relat_1(k1_xboole_0)
      | k3_xboole_0(A_334,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_559])).

tff(c_1103,plain,(
    ! [A_336] :
      ( k3_xboole_0('#skF_3',A_336) = k1_xboole_0
      | k3_xboole_0(A_336,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1076])).

tff(c_1109,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_1103])).

tff(c_998,plain,(
    ! [A_331] :
      ( k7_relat_1('#skF_6',A_331) = k1_xboole_0
      | k3_xboole_0(A_331,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_818])).

tff(c_1013,plain,(
    ! [A_331] :
      ( k3_xboole_0('#skF_4',A_331) = k1_relat_1(k1_xboole_0)
      | k3_xboole_0(A_331,'#skF_4') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_763])).

tff(c_1099,plain,(
    ! [A_335] :
      ( k3_xboole_0('#skF_4',A_335) = k1_xboole_0
      | k3_xboole_0(A_335,'#skF_4') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1013])).

tff(c_1295,plain,(
    ! [B_367] :
      ( k3_xboole_0('#skF_4',k1_relat_1(B_367)) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_367,'#skF_4')) != k1_xboole_0
      | ~ v1_relat_1(B_367) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1099])).

tff(c_165,plain,(
    ! [A_244,B_245] :
      ( k7_relat_1(A_244,B_245) = k1_xboole_0
      | ~ r1_xboole_0(B_245,k1_relat_1(A_244))
      | ~ v1_relat_1(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,(
    ! [A_244,A_1] :
      ( k7_relat_1(A_244,A_1) = k1_xboole_0
      | ~ v1_relat_1(A_244)
      | k3_xboole_0(A_1,k1_relat_1(A_244)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_1340,plain,(
    ! [B_368] :
      ( k7_relat_1(B_368,'#skF_4') = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_368,'#skF_4')) != k1_xboole_0
      | ~ v1_relat_1(B_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1295,c_178])).

tff(c_1352,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_1340])).

tff(c_1362,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1109,c_1352])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,k3_xboole_0(k1_relat_1(B_13),A_12)) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_746,plain,(
    ! [A_12] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_12)) = k7_relat_1('#skF_6',A_12)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_12])).

tff(c_759,plain,(
    ! [A_12] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_12)) = k7_relat_1('#skF_6',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_746])).

tff(c_932,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_759])).

tff(c_935,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_932])).

tff(c_542,plain,(
    ! [A_12] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_12)) = k7_relat_1('#skF_5',A_12)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_12])).

tff(c_555,plain,(
    ! [A_12] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_12)) = k7_relat_1('#skF_5',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_542])).

tff(c_872,plain,(
    ! [A_319,B_320,C_321,D_322] :
      ( k2_partfun1(A_319,B_320,C_321,D_322) = k7_relat_1(C_321,D_322)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320)))
      | ~ v1_funct_1(C_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_876,plain,(
    ! [D_322] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_322) = k7_relat_1('#skF_5',D_322)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_872])).

tff(c_882,plain,(
    ! [D_322] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_322) = k7_relat_1('#skF_5',D_322) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_876])).

tff(c_874,plain,(
    ! [D_322] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_322) = k7_relat_1('#skF_6',D_322)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_872])).

tff(c_879,plain,(
    ! [D_322] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_322) = k7_relat_1('#skF_6',D_322) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_874])).

tff(c_203,plain,(
    ! [A_250,B_251,C_252] :
      ( k9_subset_1(A_250,B_251,C_252) = k3_xboole_0(B_251,C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(A_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_215,plain,(
    ! [B_251] : k9_subset_1('#skF_1',B_251,'#skF_4') = k3_xboole_0(B_251,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_203])).

tff(c_52,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_102,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_225,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_215,c_102])).

tff(c_1737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_935,c_1109,c_555,c_882,c_879,c_225])).

tff(c_1739,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10214,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10204,c_10204,c_1739])).

tff(c_10369,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k2_partfun1('#skF_4','#skF_2','#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10359,c_10359,c_10214])).

tff(c_10550,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k7_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10546,c_10369])).

tff(c_10551,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10396,c_10550])).

tff(c_10571,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10565,c_10551])).

tff(c_10763,plain,(
    ! [F_980,B_975,E_979,D_976,C_977,A_978] :
      ( v1_funct_1(k1_tmap_1(A_978,B_975,C_977,D_976,E_979,F_980))
      | ~ m1_subset_1(F_980,k1_zfmisc_1(k2_zfmisc_1(D_976,B_975)))
      | ~ v1_funct_2(F_980,D_976,B_975)
      | ~ v1_funct_1(F_980)
      | ~ m1_subset_1(E_979,k1_zfmisc_1(k2_zfmisc_1(C_977,B_975)))
      | ~ v1_funct_2(E_979,C_977,B_975)
      | ~ v1_funct_1(E_979)
      | ~ m1_subset_1(D_976,k1_zfmisc_1(A_978))
      | v1_xboole_0(D_976)
      | ~ m1_subset_1(C_977,k1_zfmisc_1(A_978))
      | v1_xboole_0(C_977)
      | v1_xboole_0(B_975)
      | v1_xboole_0(A_978) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_10765,plain,(
    ! [A_978,C_977,E_979] :
      ( v1_funct_1(k1_tmap_1(A_978,'#skF_2',C_977,'#skF_4',E_979,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_979,k1_zfmisc_1(k2_zfmisc_1(C_977,'#skF_2')))
      | ~ v1_funct_2(E_979,C_977,'#skF_2')
      | ~ v1_funct_1(E_979)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_978))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_977,k1_zfmisc_1(A_978))
      | v1_xboole_0(C_977)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_978) ) ),
    inference(resolution,[status(thm)],[c_54,c_10763])).

tff(c_10770,plain,(
    ! [A_978,C_977,E_979] :
      ( v1_funct_1(k1_tmap_1(A_978,'#skF_2',C_977,'#skF_4',E_979,'#skF_6'))
      | ~ m1_subset_1(E_979,k1_zfmisc_1(k2_zfmisc_1(C_977,'#skF_2')))
      | ~ v1_funct_2(E_979,C_977,'#skF_2')
      | ~ v1_funct_1(E_979)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_978))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_977,k1_zfmisc_1(A_978))
      | v1_xboole_0(C_977)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_978) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_10765])).

tff(c_10881,plain,(
    ! [A_984,C_985,E_986] :
      ( v1_funct_1(k1_tmap_1(A_984,'#skF_2',C_985,'#skF_4',E_986,'#skF_6'))
      | ~ m1_subset_1(E_986,k1_zfmisc_1(k2_zfmisc_1(C_985,'#skF_2')))
      | ~ v1_funct_2(E_986,C_985,'#skF_2')
      | ~ v1_funct_1(E_986)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_984))
      | ~ m1_subset_1(C_985,k1_zfmisc_1(A_984))
      | v1_xboole_0(C_985)
      | v1_xboole_0(A_984) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_10770])).

tff(c_10885,plain,(
    ! [A_984] :
      ( v1_funct_1(k1_tmap_1(A_984,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_984))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_984))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_984) ) ),
    inference(resolution,[status(thm)],[c_60,c_10881])).

tff(c_10892,plain,(
    ! [A_984] :
      ( v1_funct_1(k1_tmap_1(A_984,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_984))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_984))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_984) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_10885])).

tff(c_11237,plain,(
    ! [A_1003] :
      ( v1_funct_1(k1_tmap_1(A_1003,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1003))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1003))
      | v1_xboole_0(A_1003) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_10892])).

tff(c_11240,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_11237])).

tff(c_11243,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_11240])).

tff(c_11244,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_11243])).

tff(c_10549,plain,(
    ! [D_959] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_959) = k7_relat_1('#skF_5',D_959) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10543])).

tff(c_48,plain,(
    ! [E_165,C_163,F_166,A_161,B_162,D_164] :
      ( v1_funct_2(k1_tmap_1(A_161,B_162,C_163,D_164,E_165,F_166),k4_subset_1(A_161,C_163,D_164),B_162)
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(D_164,B_162)))
      | ~ v1_funct_2(F_166,D_164,B_162)
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(C_163,B_162)))
      | ~ v1_funct_2(E_165,C_163,B_162)
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(A_161))
      | v1_xboole_0(D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | v1_xboole_0(C_163)
      | v1_xboole_0(B_162)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_46,plain,(
    ! [E_165,C_163,F_166,A_161,B_162,D_164] :
      ( m1_subset_1(k1_tmap_1(A_161,B_162,C_163,D_164,E_165,F_166),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_161,C_163,D_164),B_162)))
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(D_164,B_162)))
      | ~ v1_funct_2(F_166,D_164,B_162)
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(C_163,B_162)))
      | ~ v1_funct_2(E_165,C_163,B_162)
      | ~ v1_funct_1(E_165)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(A_161))
      | v1_xboole_0(D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | v1_xboole_0(C_163)
      | v1_xboole_0(B_162)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_11703,plain,(
    ! [C_1026,E_1029,B_1028,A_1025,F_1027,D_1030] :
      ( k2_partfun1(k4_subset_1(A_1025,C_1026,D_1030),B_1028,k1_tmap_1(A_1025,B_1028,C_1026,D_1030,E_1029,F_1027),C_1026) = E_1029
      | ~ m1_subset_1(k1_tmap_1(A_1025,B_1028,C_1026,D_1030,E_1029,F_1027),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1025,C_1026,D_1030),B_1028)))
      | ~ v1_funct_2(k1_tmap_1(A_1025,B_1028,C_1026,D_1030,E_1029,F_1027),k4_subset_1(A_1025,C_1026,D_1030),B_1028)
      | ~ v1_funct_1(k1_tmap_1(A_1025,B_1028,C_1026,D_1030,E_1029,F_1027))
      | k2_partfun1(D_1030,B_1028,F_1027,k9_subset_1(A_1025,C_1026,D_1030)) != k2_partfun1(C_1026,B_1028,E_1029,k9_subset_1(A_1025,C_1026,D_1030))
      | ~ m1_subset_1(F_1027,k1_zfmisc_1(k2_zfmisc_1(D_1030,B_1028)))
      | ~ v1_funct_2(F_1027,D_1030,B_1028)
      | ~ v1_funct_1(F_1027)
      | ~ m1_subset_1(E_1029,k1_zfmisc_1(k2_zfmisc_1(C_1026,B_1028)))
      | ~ v1_funct_2(E_1029,C_1026,B_1028)
      | ~ v1_funct_1(E_1029)
      | ~ m1_subset_1(D_1030,k1_zfmisc_1(A_1025))
      | v1_xboole_0(D_1030)
      | ~ m1_subset_1(C_1026,k1_zfmisc_1(A_1025))
      | v1_xboole_0(C_1026)
      | v1_xboole_0(B_1028)
      | v1_xboole_0(A_1025) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_13655,plain,(
    ! [C_1189,B_1187,E_1191,A_1190,F_1192,D_1188] :
      ( k2_partfun1(k4_subset_1(A_1190,C_1189,D_1188),B_1187,k1_tmap_1(A_1190,B_1187,C_1189,D_1188,E_1191,F_1192),C_1189) = E_1191
      | ~ v1_funct_2(k1_tmap_1(A_1190,B_1187,C_1189,D_1188,E_1191,F_1192),k4_subset_1(A_1190,C_1189,D_1188),B_1187)
      | ~ v1_funct_1(k1_tmap_1(A_1190,B_1187,C_1189,D_1188,E_1191,F_1192))
      | k2_partfun1(D_1188,B_1187,F_1192,k9_subset_1(A_1190,C_1189,D_1188)) != k2_partfun1(C_1189,B_1187,E_1191,k9_subset_1(A_1190,C_1189,D_1188))
      | ~ m1_subset_1(F_1192,k1_zfmisc_1(k2_zfmisc_1(D_1188,B_1187)))
      | ~ v1_funct_2(F_1192,D_1188,B_1187)
      | ~ v1_funct_1(F_1192)
      | ~ m1_subset_1(E_1191,k1_zfmisc_1(k2_zfmisc_1(C_1189,B_1187)))
      | ~ v1_funct_2(E_1191,C_1189,B_1187)
      | ~ v1_funct_1(E_1191)
      | ~ m1_subset_1(D_1188,k1_zfmisc_1(A_1190))
      | v1_xboole_0(D_1188)
      | ~ m1_subset_1(C_1189,k1_zfmisc_1(A_1190))
      | v1_xboole_0(C_1189)
      | v1_xboole_0(B_1187)
      | v1_xboole_0(A_1190) ) ),
    inference(resolution,[status(thm)],[c_46,c_11703])).

tff(c_15482,plain,(
    ! [B_1275,A_1278,C_1277,E_1279,F_1280,D_1276] :
      ( k2_partfun1(k4_subset_1(A_1278,C_1277,D_1276),B_1275,k1_tmap_1(A_1278,B_1275,C_1277,D_1276,E_1279,F_1280),C_1277) = E_1279
      | ~ v1_funct_1(k1_tmap_1(A_1278,B_1275,C_1277,D_1276,E_1279,F_1280))
      | k2_partfun1(D_1276,B_1275,F_1280,k9_subset_1(A_1278,C_1277,D_1276)) != k2_partfun1(C_1277,B_1275,E_1279,k9_subset_1(A_1278,C_1277,D_1276))
      | ~ m1_subset_1(F_1280,k1_zfmisc_1(k2_zfmisc_1(D_1276,B_1275)))
      | ~ v1_funct_2(F_1280,D_1276,B_1275)
      | ~ v1_funct_1(F_1280)
      | ~ m1_subset_1(E_1279,k1_zfmisc_1(k2_zfmisc_1(C_1277,B_1275)))
      | ~ v1_funct_2(E_1279,C_1277,B_1275)
      | ~ v1_funct_1(E_1279)
      | ~ m1_subset_1(D_1276,k1_zfmisc_1(A_1278))
      | v1_xboole_0(D_1276)
      | ~ m1_subset_1(C_1277,k1_zfmisc_1(A_1278))
      | v1_xboole_0(C_1277)
      | v1_xboole_0(B_1275)
      | v1_xboole_0(A_1278) ) ),
    inference(resolution,[status(thm)],[c_48,c_13655])).

tff(c_15486,plain,(
    ! [A_1278,C_1277,E_1279] :
      ( k2_partfun1(k4_subset_1(A_1278,C_1277,'#skF_4'),'#skF_2',k1_tmap_1(A_1278,'#skF_2',C_1277,'#skF_4',E_1279,'#skF_6'),C_1277) = E_1279
      | ~ v1_funct_1(k1_tmap_1(A_1278,'#skF_2',C_1277,'#skF_4',E_1279,'#skF_6'))
      | k2_partfun1(C_1277,'#skF_2',E_1279,k9_subset_1(A_1278,C_1277,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_1278,C_1277,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1279,k1_zfmisc_1(k2_zfmisc_1(C_1277,'#skF_2')))
      | ~ v1_funct_2(E_1279,C_1277,'#skF_2')
      | ~ v1_funct_1(E_1279)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1278))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1277,k1_zfmisc_1(A_1278))
      | v1_xboole_0(C_1277)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1278) ) ),
    inference(resolution,[status(thm)],[c_54,c_15482])).

tff(c_15492,plain,(
    ! [A_1278,C_1277,E_1279] :
      ( k2_partfun1(k4_subset_1(A_1278,C_1277,'#skF_4'),'#skF_2',k1_tmap_1(A_1278,'#skF_2',C_1277,'#skF_4',E_1279,'#skF_6'),C_1277) = E_1279
      | ~ v1_funct_1(k1_tmap_1(A_1278,'#skF_2',C_1277,'#skF_4',E_1279,'#skF_6'))
      | k2_partfun1(C_1277,'#skF_2',E_1279,k9_subset_1(A_1278,C_1277,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1278,C_1277,'#skF_4'))
      | ~ m1_subset_1(E_1279,k1_zfmisc_1(k2_zfmisc_1(C_1277,'#skF_2')))
      | ~ v1_funct_2(E_1279,C_1277,'#skF_2')
      | ~ v1_funct_1(E_1279)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1278))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_1277,k1_zfmisc_1(A_1278))
      | v1_xboole_0(C_1277)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_1278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_10546,c_15486])).

tff(c_15893,plain,(
    ! [A_1311,C_1312,E_1313] :
      ( k2_partfun1(k4_subset_1(A_1311,C_1312,'#skF_4'),'#skF_2',k1_tmap_1(A_1311,'#skF_2',C_1312,'#skF_4',E_1313,'#skF_6'),C_1312) = E_1313
      | ~ v1_funct_1(k1_tmap_1(A_1311,'#skF_2',C_1312,'#skF_4',E_1313,'#skF_6'))
      | k2_partfun1(C_1312,'#skF_2',E_1313,k9_subset_1(A_1311,C_1312,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1311,C_1312,'#skF_4'))
      | ~ m1_subset_1(E_1313,k1_zfmisc_1(k2_zfmisc_1(C_1312,'#skF_2')))
      | ~ v1_funct_2(E_1313,C_1312,'#skF_2')
      | ~ v1_funct_1(E_1313)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1311))
      | ~ m1_subset_1(C_1312,k1_zfmisc_1(A_1311))
      | v1_xboole_0(C_1312)
      | v1_xboole_0(A_1311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_15492])).

tff(c_15900,plain,(
    ! [A_1311] :
      ( k2_partfun1(k4_subset_1(A_1311,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1311,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1311,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_1311,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1311,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1311))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1311))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1311) ) ),
    inference(resolution,[status(thm)],[c_60,c_15893])).

tff(c_15910,plain,(
    ! [A_1311] :
      ( k2_partfun1(k4_subset_1(A_1311,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1311,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1311,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1311,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1311,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1311))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1311))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_10549,c_15900])).

tff(c_16752,plain,(
    ! [A_1334] :
      ( k2_partfun1(k4_subset_1(A_1334,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_1334,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') = '#skF_5'
      | ~ v1_funct_1(k1_tmap_1(A_1334,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_1334,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_1334,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1334))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_1334))
      | v1_xboole_0(A_1334) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_15910])).

tff(c_2553,plain,(
    ~ v1_partfun1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1841])).

tff(c_2859,plain,(
    ! [C_492,A_493,B_494] :
      ( v1_partfun1(C_492,A_493)
      | ~ v1_funct_2(C_492,A_493,B_494)
      | ~ v1_funct_1(C_492)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(A_493,B_494)))
      | v1_xboole_0(B_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2862,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2859])).

tff(c_2868,plain,
    ( v1_partfun1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2862])).

tff(c_2870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2553,c_2868])).

tff(c_2871,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1841])).

tff(c_2882,plain,(
    ! [B_11] :
      ( k7_relat_1('#skF_6',B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,'#skF_4')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2871,c_10])).

tff(c_2906,plain,(
    ! [B_496] :
      ( k7_relat_1('#skF_6',B_496) = k1_xboole_0
      | ~ r1_xboole_0(B_496,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2882])).

tff(c_2910,plain,(
    ! [A_16] :
      ( k7_relat_1('#skF_6',A_16) = k1_xboole_0
      | ~ r1_subset_1(A_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_2906])).

tff(c_3078,plain,(
    ! [A_505] :
      ( k7_relat_1('#skF_6',A_505) = k1_xboole_0
      | ~ r1_subset_1(A_505,'#skF_4')
      | v1_xboole_0(A_505) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2910])).

tff(c_3081,plain,
    ( k7_relat_1('#skF_6','#skF_3') = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3078])).

tff(c_3084,plain,(
    k7_relat_1('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3081])).

tff(c_2879,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2871,c_18])).

tff(c_2888,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1('#skF_6',A_14)) = k3_xboole_0('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2879])).

tff(c_3088,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3084,c_2888])).

tff(c_3091,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3088])).

tff(c_2893,plain,(
    ! [B_495] :
      ( k7_relat_1('#skF_5',B_495) = k1_xboole_0
      | ~ r1_xboole_0(B_495,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2541])).

tff(c_2957,plain,(
    ! [A_499] :
      ( k7_relat_1('#skF_5',A_499) = k1_xboole_0
      | k3_xboole_0(A_499,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2893])).

tff(c_2963,plain,(
    ! [A_499] :
      ( k3_xboole_0('#skF_3',A_499) = k1_relat_1(k1_xboole_0)
      | k3_xboole_0(A_499,'#skF_3') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2957,c_2547])).

tff(c_3240,plain,(
    ! [A_515] :
      ( k3_xboole_0('#skF_3',A_515) = k1_xboole_0
      | k3_xboole_0(A_515,'#skF_3') != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2963])).

tff(c_3246,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3091,c_3240])).

tff(c_2970,plain,(
    ! [B_500,A_501] :
      ( k7_relat_1(B_500,k3_xboole_0(k1_relat_1(B_500),A_501)) = k7_relat_1(B_500,A_501)
      | ~ v1_relat_1(B_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3004,plain,(
    ! [A_501] :
      ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_501)) = k7_relat_1('#skF_5',A_501)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2530,c_2970])).

tff(c_3024,plain,(
    ! [A_501] : k7_relat_1('#skF_5',k3_xboole_0('#skF_3',A_501)) = k7_relat_1('#skF_5',A_501) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_3004])).

tff(c_3255,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k7_relat_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_3024])).

tff(c_3262,plain,(
    ! [A_516,B_517,C_518,D_519] :
      ( k2_partfun1(A_516,B_517,C_518,D_519) = k7_relat_1(C_518,D_519)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(A_516,B_517)))
      | ~ v1_funct_1(C_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3266,plain,(
    ! [D_519] :
      ( k2_partfun1('#skF_3','#skF_2','#skF_5',D_519) = k7_relat_1('#skF_5',D_519)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_3262])).

tff(c_3272,plain,(
    ! [D_519] : k2_partfun1('#skF_3','#skF_2','#skF_5',D_519) = k7_relat_1('#skF_5',D_519) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3266])).

tff(c_3001,plain,(
    ! [A_501] :
      ( k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_501)) = k7_relat_1('#skF_6',A_501)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2871,c_2970])).

tff(c_3022,plain,(
    ! [A_501] : k7_relat_1('#skF_6',k3_xboole_0('#skF_4',A_501)) = k7_relat_1('#skF_6',A_501) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_3001])).

tff(c_3099,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k7_relat_1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3091,c_3022])).

tff(c_3103,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3084,c_3099])).

tff(c_3264,plain,(
    ! [D_519] :
      ( k2_partfun1('#skF_4','#skF_2','#skF_6',D_519) = k7_relat_1('#skF_6',D_519)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_3262])).

tff(c_3269,plain,(
    ! [D_519] : k2_partfun1('#skF_4','#skF_2','#skF_6',D_519) = k7_relat_1('#skF_6',D_519) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3264])).

tff(c_3172,plain,(
    ! [A_507,B_508,C_509] :
      ( k9_subset_1(A_507,B_508,C_509) = k3_xboole_0(B_508,C_509)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(A_507)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3184,plain,(
    ! [B_508] : k9_subset_1('#skF_1',B_508,'#skF_4') = k3_xboole_0(B_508,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3172])).

tff(c_3194,plain,(
    k2_partfun1('#skF_3','#skF_2','#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k2_partfun1('#skF_4','#skF_2','#skF_6',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3184,c_3184,c_1739])).

tff(c_3368,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3272,c_3103,c_3269,c_3246,c_3246,c_3194])).

tff(c_3404,plain,(
    ! [A_532,E_533,C_531,D_530,B_529,F_534] :
      ( v1_funct_1(k1_tmap_1(A_532,B_529,C_531,D_530,E_533,F_534))
      | ~ m1_subset_1(F_534,k1_zfmisc_1(k2_zfmisc_1(D_530,B_529)))
      | ~ v1_funct_2(F_534,D_530,B_529)
      | ~ v1_funct_1(F_534)
      | ~ m1_subset_1(E_533,k1_zfmisc_1(k2_zfmisc_1(C_531,B_529)))
      | ~ v1_funct_2(E_533,C_531,B_529)
      | ~ v1_funct_1(E_533)
      | ~ m1_subset_1(D_530,k1_zfmisc_1(A_532))
      | v1_xboole_0(D_530)
      | ~ m1_subset_1(C_531,k1_zfmisc_1(A_532))
      | v1_xboole_0(C_531)
      | v1_xboole_0(B_529)
      | v1_xboole_0(A_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_3406,plain,(
    ! [A_532,C_531,E_533] :
      ( v1_funct_1(k1_tmap_1(A_532,'#skF_2',C_531,'#skF_4',E_533,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_533,k1_zfmisc_1(k2_zfmisc_1(C_531,'#skF_2')))
      | ~ v1_funct_2(E_533,C_531,'#skF_2')
      | ~ v1_funct_1(E_533)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_532))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_531,k1_zfmisc_1(A_532))
      | v1_xboole_0(C_531)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_532) ) ),
    inference(resolution,[status(thm)],[c_54,c_3404])).

tff(c_3411,plain,(
    ! [A_532,C_531,E_533] :
      ( v1_funct_1(k1_tmap_1(A_532,'#skF_2',C_531,'#skF_4',E_533,'#skF_6'))
      | ~ m1_subset_1(E_533,k1_zfmisc_1(k2_zfmisc_1(C_531,'#skF_2')))
      | ~ v1_funct_2(E_533,C_531,'#skF_2')
      | ~ v1_funct_1(E_533)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_532))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_531,k1_zfmisc_1(A_532))
      | v1_xboole_0(C_531)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_532) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3406])).

tff(c_4441,plain,(
    ! [A_590,C_591,E_592] :
      ( v1_funct_1(k1_tmap_1(A_590,'#skF_2',C_591,'#skF_4',E_592,'#skF_6'))
      | ~ m1_subset_1(E_592,k1_zfmisc_1(k2_zfmisc_1(C_591,'#skF_2')))
      | ~ v1_funct_2(E_592,C_591,'#skF_2')
      | ~ v1_funct_1(E_592)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_590))
      | ~ m1_subset_1(C_591,k1_zfmisc_1(A_590))
      | v1_xboole_0(C_591)
      | v1_xboole_0(A_590) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_3411])).

tff(c_4448,plain,(
    ! [A_590] :
      ( v1_funct_1(k1_tmap_1(A_590,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_590))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_590))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_590) ) ),
    inference(resolution,[status(thm)],[c_60,c_4441])).

tff(c_4458,plain,(
    ! [A_590] :
      ( v1_funct_1(k1_tmap_1(A_590,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_590))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_590))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_590) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_4448])).

tff(c_4519,plain,(
    ! [A_604] :
      ( v1_funct_1(k1_tmap_1(A_604,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_604))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_604))
      | v1_xboole_0(A_604) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4458])).

tff(c_4522,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_4519])).

tff(c_4525,plain,
    ( v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4522])).

tff(c_4526,plain,(
    v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4525])).

tff(c_4402,plain,(
    ! [C_584,E_587,F_585,B_586,D_588,A_583] :
      ( k2_partfun1(k4_subset_1(A_583,C_584,D_588),B_586,k1_tmap_1(A_583,B_586,C_584,D_588,E_587,F_585),D_588) = F_585
      | ~ m1_subset_1(k1_tmap_1(A_583,B_586,C_584,D_588,E_587,F_585),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_583,C_584,D_588),B_586)))
      | ~ v1_funct_2(k1_tmap_1(A_583,B_586,C_584,D_588,E_587,F_585),k4_subset_1(A_583,C_584,D_588),B_586)
      | ~ v1_funct_1(k1_tmap_1(A_583,B_586,C_584,D_588,E_587,F_585))
      | k2_partfun1(D_588,B_586,F_585,k9_subset_1(A_583,C_584,D_588)) != k2_partfun1(C_584,B_586,E_587,k9_subset_1(A_583,C_584,D_588))
      | ~ m1_subset_1(F_585,k1_zfmisc_1(k2_zfmisc_1(D_588,B_586)))
      | ~ v1_funct_2(F_585,D_588,B_586)
      | ~ v1_funct_1(F_585)
      | ~ m1_subset_1(E_587,k1_zfmisc_1(k2_zfmisc_1(C_584,B_586)))
      | ~ v1_funct_2(E_587,C_584,B_586)
      | ~ v1_funct_1(E_587)
      | ~ m1_subset_1(D_588,k1_zfmisc_1(A_583))
      | v1_xboole_0(D_588)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(A_583))
      | v1_xboole_0(C_584)
      | v1_xboole_0(B_586)
      | v1_xboole_0(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_6367,plain,(
    ! [C_742,F_745,E_744,D_741,B_740,A_743] :
      ( k2_partfun1(k4_subset_1(A_743,C_742,D_741),B_740,k1_tmap_1(A_743,B_740,C_742,D_741,E_744,F_745),D_741) = F_745
      | ~ v1_funct_2(k1_tmap_1(A_743,B_740,C_742,D_741,E_744,F_745),k4_subset_1(A_743,C_742,D_741),B_740)
      | ~ v1_funct_1(k1_tmap_1(A_743,B_740,C_742,D_741,E_744,F_745))
      | k2_partfun1(D_741,B_740,F_745,k9_subset_1(A_743,C_742,D_741)) != k2_partfun1(C_742,B_740,E_744,k9_subset_1(A_743,C_742,D_741))
      | ~ m1_subset_1(F_745,k1_zfmisc_1(k2_zfmisc_1(D_741,B_740)))
      | ~ v1_funct_2(F_745,D_741,B_740)
      | ~ v1_funct_1(F_745)
      | ~ m1_subset_1(E_744,k1_zfmisc_1(k2_zfmisc_1(C_742,B_740)))
      | ~ v1_funct_2(E_744,C_742,B_740)
      | ~ v1_funct_1(E_744)
      | ~ m1_subset_1(D_741,k1_zfmisc_1(A_743))
      | v1_xboole_0(D_741)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(A_743))
      | v1_xboole_0(C_742)
      | v1_xboole_0(B_740)
      | v1_xboole_0(A_743) ) ),
    inference(resolution,[status(thm)],[c_46,c_4402])).

tff(c_8193,plain,(
    ! [E_836,C_834,A_835,B_832,D_833,F_837] :
      ( k2_partfun1(k4_subset_1(A_835,C_834,D_833),B_832,k1_tmap_1(A_835,B_832,C_834,D_833,E_836,F_837),D_833) = F_837
      | ~ v1_funct_1(k1_tmap_1(A_835,B_832,C_834,D_833,E_836,F_837))
      | k2_partfun1(D_833,B_832,F_837,k9_subset_1(A_835,C_834,D_833)) != k2_partfun1(C_834,B_832,E_836,k9_subset_1(A_835,C_834,D_833))
      | ~ m1_subset_1(F_837,k1_zfmisc_1(k2_zfmisc_1(D_833,B_832)))
      | ~ v1_funct_2(F_837,D_833,B_832)
      | ~ v1_funct_1(F_837)
      | ~ m1_subset_1(E_836,k1_zfmisc_1(k2_zfmisc_1(C_834,B_832)))
      | ~ v1_funct_2(E_836,C_834,B_832)
      | ~ v1_funct_1(E_836)
      | ~ m1_subset_1(D_833,k1_zfmisc_1(A_835))
      | v1_xboole_0(D_833)
      | ~ m1_subset_1(C_834,k1_zfmisc_1(A_835))
      | v1_xboole_0(C_834)
      | v1_xboole_0(B_832)
      | v1_xboole_0(A_835) ) ),
    inference(resolution,[status(thm)],[c_48,c_6367])).

tff(c_8197,plain,(
    ! [A_835,C_834,E_836] :
      ( k2_partfun1(k4_subset_1(A_835,C_834,'#skF_4'),'#skF_2',k1_tmap_1(A_835,'#skF_2',C_834,'#skF_4',E_836,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_835,'#skF_2',C_834,'#skF_4',E_836,'#skF_6'))
      | k2_partfun1(C_834,'#skF_2',E_836,k9_subset_1(A_835,C_834,'#skF_4')) != k2_partfun1('#skF_4','#skF_2','#skF_6',k9_subset_1(A_835,C_834,'#skF_4'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_836,k1_zfmisc_1(k2_zfmisc_1(C_834,'#skF_2')))
      | ~ v1_funct_2(E_836,C_834,'#skF_2')
      | ~ v1_funct_1(E_836)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_835))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_834,k1_zfmisc_1(A_835))
      | v1_xboole_0(C_834)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_835) ) ),
    inference(resolution,[status(thm)],[c_54,c_8193])).

tff(c_8203,plain,(
    ! [A_835,C_834,E_836] :
      ( k2_partfun1(k4_subset_1(A_835,C_834,'#skF_4'),'#skF_2',k1_tmap_1(A_835,'#skF_2',C_834,'#skF_4',E_836,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_835,'#skF_2',C_834,'#skF_4',E_836,'#skF_6'))
      | k2_partfun1(C_834,'#skF_2',E_836,k9_subset_1(A_835,C_834,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_835,C_834,'#skF_4'))
      | ~ m1_subset_1(E_836,k1_zfmisc_1(k2_zfmisc_1(C_834,'#skF_2')))
      | ~ v1_funct_2(E_836,C_834,'#skF_2')
      | ~ v1_funct_1(E_836)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_835))
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(C_834,k1_zfmisc_1(A_835))
      | v1_xboole_0(C_834)
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_835) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3269,c_8197])).

tff(c_9617,plain,(
    ! [A_895,C_896,E_897] :
      ( k2_partfun1(k4_subset_1(A_895,C_896,'#skF_4'),'#skF_2',k1_tmap_1(A_895,'#skF_2',C_896,'#skF_4',E_897,'#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_895,'#skF_2',C_896,'#skF_4',E_897,'#skF_6'))
      | k2_partfun1(C_896,'#skF_2',E_897,k9_subset_1(A_895,C_896,'#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_895,C_896,'#skF_4'))
      | ~ m1_subset_1(E_897,k1_zfmisc_1(k2_zfmisc_1(C_896,'#skF_2')))
      | ~ v1_funct_2(E_897,C_896,'#skF_2')
      | ~ v1_funct_1(E_897)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_895))
      | ~ m1_subset_1(C_896,k1_zfmisc_1(A_895))
      | v1_xboole_0(C_896)
      | v1_xboole_0(A_895) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_8203])).

tff(c_9624,plain,(
    ! [A_895] :
      ( k2_partfun1(k4_subset_1(A_895,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_895,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_895,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k2_partfun1('#skF_3','#skF_2','#skF_5',k9_subset_1(A_895,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_895,'#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_895))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_895))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_895) ) ),
    inference(resolution,[status(thm)],[c_60,c_9617])).

tff(c_9634,plain,(
    ! [A_895] :
      ( k2_partfun1(k4_subset_1(A_895,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_895,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_895,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_895,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_895,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_895))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_895))
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_895) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_3272,c_9624])).

tff(c_9636,plain,(
    ! [A_898] :
      ( k2_partfun1(k4_subset_1(A_898,'#skF_3','#skF_4'),'#skF_2',k1_tmap_1(A_898,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_898,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | k7_relat_1('#skF_5',k9_subset_1(A_898,'#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1(A_898,'#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_898))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_898))
      | v1_xboole_0(A_898) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_9634])).

tff(c_1738,plain,
    ( k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5'
    | k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2552,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1738])).

tff(c_9647,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9636,c_2552])).

tff(c_9661,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_3368,c_3103,c_3246,c_3184,c_3024,c_3184,c_4526,c_9647])).

tff(c_9663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_9661])).

tff(c_9664,plain,(
    k2_partfun1(k4_subset_1('#skF_1','#skF_3','#skF_4'),'#skF_2',k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1738])).

tff(c_16761,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | k7_relat_1('#skF_5',k9_subset_1('#skF_1','#skF_3','#skF_4')) != k7_relat_1('#skF_6',k9_subset_1('#skF_1','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16752,c_9664])).

tff(c_16772,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_10571,c_10396,c_10359,c_10359,c_10204,c_10204,c_11244,c_16761])).

tff(c_16774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_16772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.20/3.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.96  
% 10.20/3.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.20/3.96  
% 10.20/3.96  %Foreground sorts:
% 10.20/3.96  
% 10.20/3.96  
% 10.20/3.96  %Background operators:
% 10.20/3.96  
% 10.20/3.96  
% 10.20/3.96  %Foreground operators:
% 10.20/3.96  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 10.20/3.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.20/3.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.20/3.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.20/3.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.20/3.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.20/3.96  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.20/3.96  tff('#skF_5', type, '#skF_5': $i).
% 10.20/3.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.20/3.96  tff('#skF_6', type, '#skF_6': $i).
% 10.20/3.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.20/3.96  tff('#skF_2', type, '#skF_2': $i).
% 10.20/3.96  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.20/3.96  tff('#skF_3', type, '#skF_3': $i).
% 10.20/3.96  tff('#skF_1', type, '#skF_1': $i).
% 10.20/3.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.20/3.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.20/3.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.20/3.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.20/3.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.20/3.96  tff('#skF_4', type, '#skF_4': $i).
% 10.20/3.96  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.20/3.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.20/3.96  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.20/3.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.20/3.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.20/3.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.20/3.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.20/3.96  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.20/3.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.20/3.96  
% 10.57/4.00  tff(f_230, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 10.57/4.00  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 10.57/4.00  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 10.57/4.00  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.57/4.00  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.57/4.00  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 10.57/4.00  tff(f_92, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 10.57/4.00  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 10.57/4.00  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 10.57/4.00  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 10.57/4.00  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 10.57/4.00  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.57/4.00  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.57/4.00  tff(f_188, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 10.57/4.00  tff(f_154, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 10.57/4.00  tff(c_78, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_10539, plain, (![A_956, B_957, C_958, D_959]: (k2_partfun1(A_956, B_957, C_958, D_959)=k7_relat_1(C_958, D_959) | ~m1_subset_1(C_958, k1_zfmisc_1(k2_zfmisc_1(A_956, B_957))) | ~v1_funct_1(C_958))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.57/4.00  tff(c_10543, plain, (![D_959]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_959)=k7_relat_1('#skF_5', D_959) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_10539])).
% 10.57/4.00  tff(c_10565, plain, (![D_961]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_961)=k7_relat_1('#skF_5', D_961))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_10543])).
% 10.57/4.00  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_66, plain, (r1_subset_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_22, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | ~r1_subset_1(A_16, B_17) | v1_xboole_0(B_17) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.57/4.00  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_93, plain, (![C_228, A_229, B_230]: (v1_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.57/4.00  tff(c_100, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_93])).
% 10.57/4.00  tff(c_76, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_1770, plain, (![C_390, A_391, B_392]: (v4_relat_1(C_390, A_391) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_391, B_392))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.57/4.00  tff(c_1777, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_1770])).
% 10.57/4.00  tff(c_1829, plain, (![B_402, A_403]: (k1_relat_1(B_402)=A_403 | ~v1_partfun1(B_402, A_403) | ~v4_relat_1(B_402, A_403) | ~v1_relat_1(B_402))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.57/4.00  tff(c_1835, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1777, c_1829])).
% 10.57/4.00  tff(c_1841, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1835])).
% 10.57/4.00  tff(c_9666, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1841])).
% 10.57/4.00  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_10077, plain, (![C_929, A_930, B_931]: (v1_partfun1(C_929, A_930) | ~v1_funct_2(C_929, A_930, B_931) | ~v1_funct_1(C_929) | ~m1_subset_1(C_929, k1_zfmisc_1(k2_zfmisc_1(A_930, B_931))) | v1_xboole_0(B_931))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.57/4.00  tff(c_10080, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_10077])).
% 10.57/4.00  tff(c_10086, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_10080])).
% 10.57/4.00  tff(c_10088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_9666, c_10086])).
% 10.57/4.00  tff(c_10089, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1841])).
% 10.57/4.00  tff(c_10, plain, (![A_9, B_11]: (k7_relat_1(A_9, B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, k1_relat_1(A_9)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.57/4.00  tff(c_10100, plain, (![B_11]: (k7_relat_1('#skF_6', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10089, c_10])).
% 10.57/4.00  tff(c_10134, plain, (![B_933]: (k7_relat_1('#skF_6', B_933)=k1_xboole_0 | ~r1_xboole_0(B_933, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_10100])).
% 10.57/4.00  tff(c_10138, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_22, c_10134])).
% 10.57/4.00  tff(c_10264, plain, (![A_948]: (k7_relat_1('#skF_6', A_948)=k1_xboole_0 | ~r1_subset_1(A_948, '#skF_4') | v1_xboole_0(A_948))), inference(negUnitSimplification, [status(thm)], [c_70, c_10138])).
% 10.57/4.00  tff(c_10267, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_10264])).
% 10.57/4.00  tff(c_10270, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_10267])).
% 10.57/4.00  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.57/4.00  tff(c_18, plain, (![B_15, A_14]: (k3_xboole_0(k1_relat_1(B_15), A_14)=k1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.57/4.00  tff(c_10097, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10089, c_18])).
% 10.57/4.00  tff(c_10106, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_10097])).
% 10.57/4.00  tff(c_10344, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10270, c_10106])).
% 10.57/4.00  tff(c_10351, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10344])).
% 10.57/4.00  tff(c_10271, plain, (![B_949, A_950]: (k7_relat_1(B_949, k3_xboole_0(k1_relat_1(B_949), A_950))=k7_relat_1(B_949, A_950) | ~v1_relat_1(B_949))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.57/4.00  tff(c_10310, plain, (![A_950]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_950))=k7_relat_1('#skF_6', A_950) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10089, c_10271])).
% 10.57/4.00  tff(c_10374, plain, (![A_951]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_951))=k7_relat_1('#skF_6', A_951))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_10310])).
% 10.57/4.00  tff(c_10389, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10351, c_10374])).
% 10.57/4.00  tff(c_10396, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10270, c_10389])).
% 10.57/4.00  tff(c_10541, plain, (![D_959]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_959)=k7_relat_1('#skF_6', D_959) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_10539])).
% 10.57/4.00  tff(c_10546, plain, (![D_959]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_959)=k7_relat_1('#skF_6', D_959))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10541])).
% 10.57/4.00  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.57/4.00  tff(c_101, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_93])).
% 10.57/4.00  tff(c_1778, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1770])).
% 10.57/4.00  tff(c_1832, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1778, c_1829])).
% 10.57/4.00  tff(c_1838, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1832])).
% 10.57/4.00  tff(c_1842, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1838])).
% 10.57/4.00  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_2514, plain, (![C_464, A_465, B_466]: (v1_partfun1(C_464, A_465) | ~v1_funct_2(C_464, A_465, B_466) | ~v1_funct_1(C_464) | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_465, B_466))) | v1_xboole_0(B_466))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.57/4.00  tff(c_2520, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_2514])).
% 10.57/4.00  tff(c_2527, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2520])).
% 10.57/4.00  tff(c_2529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1842, c_2527])).
% 10.57/4.00  tff(c_2530, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1838])).
% 10.57/4.00  tff(c_2541, plain, (![B_11]: (k7_relat_1('#skF_5', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2530, c_10])).
% 10.57/4.00  tff(c_10166, plain, (![B_935]: (k7_relat_1('#skF_5', B_935)=k1_xboole_0 | ~r1_xboole_0(B_935, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2541])).
% 10.57/4.00  tff(c_10224, plain, (![A_942]: (k7_relat_1('#skF_5', A_942)=k1_xboole_0 | k3_xboole_0(A_942, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_10166])).
% 10.57/4.00  tff(c_2538, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2530, c_18])).
% 10.57/4.00  tff(c_2547, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2538])).
% 10.57/4.00  tff(c_10230, plain, (![A_942]: (k3_xboole_0('#skF_3', A_942)=k1_relat_1(k1_xboole_0) | k3_xboole_0(A_942, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10224, c_2547])).
% 10.57/4.00  tff(c_10235, plain, (![A_942]: (k3_xboole_0('#skF_3', A_942)=k1_xboole_0 | k3_xboole_0(A_942, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10230])).
% 10.57/4.00  tff(c_10359, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10351, c_10235])).
% 10.57/4.00  tff(c_10192, plain, (![A_937, B_938, C_939]: (k9_subset_1(A_937, B_938, C_939)=k3_xboole_0(B_938, C_939) | ~m1_subset_1(C_939, k1_zfmisc_1(A_937)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.57/4.00  tff(c_10204, plain, (![B_938]: (k9_subset_1('#skF_1', B_938, '#skF_4')=k3_xboole_0(B_938, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_10192])).
% 10.57/4.00  tff(c_133, plain, (![C_236, A_237, B_238]: (v4_relat_1(C_236, A_237) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.57/4.00  tff(c_140, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_133])).
% 10.57/4.00  tff(c_235, plain, (![B_255, A_256]: (k1_relat_1(B_255)=A_256 | ~v1_partfun1(B_255, A_256) | ~v4_relat_1(B_255, A_256) | ~v1_relat_1(B_255))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.57/4.00  tff(c_241, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_140, c_235])).
% 10.57/4.00  tff(c_247, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_partfun1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_241])).
% 10.57/4.00  tff(c_573, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_247])).
% 10.57/4.00  tff(c_729, plain, (![C_310, A_311, B_312]: (v1_partfun1(C_310, A_311) | ~v1_funct_2(C_310, A_311, B_312) | ~v1_funct_1(C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))) | v1_xboole_0(B_312))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.57/4.00  tff(c_732, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_729])).
% 10.57/4.00  tff(c_738, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_732])).
% 10.57/4.00  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_573, c_738])).
% 10.57/4.00  tff(c_741, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_247])).
% 10.57/4.00  tff(c_749, plain, (![B_11]: (k7_relat_1('#skF_6', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_741, c_10])).
% 10.57/4.00  tff(c_818, plain, (![B_316]: (k7_relat_1('#skF_6', B_316)=k1_xboole_0 | ~r1_xboole_0(B_316, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_749])).
% 10.57/4.00  tff(c_822, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_22, c_818])).
% 10.57/4.00  tff(c_914, plain, (![A_326]: (k7_relat_1('#skF_6', A_326)=k1_xboole_0 | ~r1_subset_1(A_326, '#skF_4') | v1_xboole_0(A_326))), inference(negUnitSimplification, [status(thm)], [c_70, c_822])).
% 10.57/4.00  tff(c_917, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_914])).
% 10.57/4.00  tff(c_920, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_917])).
% 10.57/4.00  tff(c_752, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_741, c_18])).
% 10.57/4.00  tff(c_763, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_752])).
% 10.57/4.00  tff(c_924, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_920, c_763])).
% 10.57/4.00  tff(c_927, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_924])).
% 10.57/4.00  tff(c_141, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_133])).
% 10.57/4.00  tff(c_238, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_141, c_235])).
% 10.57/4.00  tff(c_244, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_238])).
% 10.57/4.00  tff(c_248, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_244])).
% 10.57/4.00  tff(c_521, plain, (![C_291, A_292, B_293]: (v1_partfun1(C_291, A_292) | ~v1_funct_2(C_291, A_292, B_293) | ~v1_funct_1(C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))) | v1_xboole_0(B_293))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.57/4.00  tff(c_527, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_521])).
% 10.57/4.00  tff(c_534, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_527])).
% 10.57/4.00  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_248, c_534])).
% 10.57/4.00  tff(c_537, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_244])).
% 10.57/4.00  tff(c_545, plain, (![B_11]: (k7_relat_1('#skF_5', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_10])).
% 10.57/4.00  tff(c_805, plain, (![B_315]: (k7_relat_1('#skF_5', B_315)=k1_xboole_0 | ~r1_xboole_0(B_315, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_545])).
% 10.57/4.00  tff(c_1067, plain, (![A_334]: (k7_relat_1('#skF_5', A_334)=k1_xboole_0 | k3_xboole_0(A_334, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_805])).
% 10.57/4.00  tff(c_548, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_18])).
% 10.57/4.00  tff(c_559, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_5', A_14))=k3_xboole_0('#skF_3', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_548])).
% 10.57/4.00  tff(c_1076, plain, (![A_334]: (k3_xboole_0('#skF_3', A_334)=k1_relat_1(k1_xboole_0) | k3_xboole_0(A_334, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1067, c_559])).
% 10.57/4.00  tff(c_1103, plain, (![A_336]: (k3_xboole_0('#skF_3', A_336)=k1_xboole_0 | k3_xboole_0(A_336, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1076])).
% 10.57/4.00  tff(c_1109, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_927, c_1103])).
% 10.57/4.00  tff(c_998, plain, (![A_331]: (k7_relat_1('#skF_6', A_331)=k1_xboole_0 | k3_xboole_0(A_331, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_818])).
% 10.57/4.00  tff(c_1013, plain, (![A_331]: (k3_xboole_0('#skF_4', A_331)=k1_relat_1(k1_xboole_0) | k3_xboole_0(A_331, '#skF_4')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_998, c_763])).
% 10.57/4.00  tff(c_1099, plain, (![A_335]: (k3_xboole_0('#skF_4', A_335)=k1_xboole_0 | k3_xboole_0(A_335, '#skF_4')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1013])).
% 10.57/4.00  tff(c_1295, plain, (![B_367]: (k3_xboole_0('#skF_4', k1_relat_1(B_367))=k1_xboole_0 | k1_relat_1(k7_relat_1(B_367, '#skF_4'))!=k1_xboole_0 | ~v1_relat_1(B_367))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1099])).
% 10.57/4.00  tff(c_165, plain, (![A_244, B_245]: (k7_relat_1(A_244, B_245)=k1_xboole_0 | ~r1_xboole_0(B_245, k1_relat_1(A_244)) | ~v1_relat_1(A_244))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.57/4.00  tff(c_178, plain, (![A_244, A_1]: (k7_relat_1(A_244, A_1)=k1_xboole_0 | ~v1_relat_1(A_244) | k3_xboole_0(A_1, k1_relat_1(A_244))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_165])).
% 10.57/4.00  tff(c_1340, plain, (![B_368]: (k7_relat_1(B_368, '#skF_4')=k1_xboole_0 | k1_relat_1(k7_relat_1(B_368, '#skF_4'))!=k1_xboole_0 | ~v1_relat_1(B_368))), inference(superposition, [status(thm), theory('equality')], [c_1295, c_178])).
% 10.57/4.00  tff(c_1352, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_559, c_1340])).
% 10.57/4.00  tff(c_1362, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1109, c_1352])).
% 10.57/4.00  tff(c_12, plain, (![B_13, A_12]: (k7_relat_1(B_13, k3_xboole_0(k1_relat_1(B_13), A_12))=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.57/4.00  tff(c_746, plain, (![A_12]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_12))=k7_relat_1('#skF_6', A_12) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_741, c_12])).
% 10.57/4.00  tff(c_759, plain, (![A_12]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_12))=k7_relat_1('#skF_6', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_746])).
% 10.57/4.00  tff(c_932, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_927, c_759])).
% 10.57/4.00  tff(c_935, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_920, c_932])).
% 10.57/4.00  tff(c_542, plain, (![A_12]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_12))=k7_relat_1('#skF_5', A_12) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_12])).
% 10.57/4.00  tff(c_555, plain, (![A_12]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_12))=k7_relat_1('#skF_5', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_542])).
% 10.57/4.00  tff(c_872, plain, (![A_319, B_320, C_321, D_322]: (k2_partfun1(A_319, B_320, C_321, D_322)=k7_relat_1(C_321, D_322) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))) | ~v1_funct_1(C_321))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.57/4.00  tff(c_876, plain, (![D_322]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_322)=k7_relat_1('#skF_5', D_322) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_872])).
% 10.57/4.00  tff(c_882, plain, (![D_322]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_322)=k7_relat_1('#skF_5', D_322))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_876])).
% 10.57/4.00  tff(c_874, plain, (![D_322]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_322)=k7_relat_1('#skF_6', D_322) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_872])).
% 10.57/4.00  tff(c_879, plain, (![D_322]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_322)=k7_relat_1('#skF_6', D_322))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_874])).
% 10.57/4.00  tff(c_203, plain, (![A_250, B_251, C_252]: (k9_subset_1(A_250, B_251, C_252)=k3_xboole_0(B_251, C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(A_250)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.57/4.00  tff(c_215, plain, (![B_251]: (k9_subset_1('#skF_1', B_251, '#skF_4')=k3_xboole_0(B_251, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_203])).
% 10.57/4.00  tff(c_52, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.57/4.00  tff(c_102, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 10.57/4.00  tff(c_225, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_215, c_102])).
% 10.57/4.00  tff(c_1737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1362, c_935, c_1109, c_555, c_882, c_879, c_225])).
% 10.57/4.00  tff(c_1739, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 10.57/4.00  tff(c_10214, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10204, c_10204, c_1739])).
% 10.57/4.00  tff(c_10369, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10359, c_10359, c_10214])).
% 10.57/4.00  tff(c_10550, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k7_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10546, c_10369])).
% 10.57/4.00  tff(c_10551, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10396, c_10550])).
% 10.57/4.00  tff(c_10571, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10565, c_10551])).
% 10.57/4.00  tff(c_10763, plain, (![F_980, B_975, E_979, D_976, C_977, A_978]: (v1_funct_1(k1_tmap_1(A_978, B_975, C_977, D_976, E_979, F_980)) | ~m1_subset_1(F_980, k1_zfmisc_1(k2_zfmisc_1(D_976, B_975))) | ~v1_funct_2(F_980, D_976, B_975) | ~v1_funct_1(F_980) | ~m1_subset_1(E_979, k1_zfmisc_1(k2_zfmisc_1(C_977, B_975))) | ~v1_funct_2(E_979, C_977, B_975) | ~v1_funct_1(E_979) | ~m1_subset_1(D_976, k1_zfmisc_1(A_978)) | v1_xboole_0(D_976) | ~m1_subset_1(C_977, k1_zfmisc_1(A_978)) | v1_xboole_0(C_977) | v1_xboole_0(B_975) | v1_xboole_0(A_978))), inference(cnfTransformation, [status(thm)], [f_188])).
% 10.57/4.00  tff(c_10765, plain, (![A_978, C_977, E_979]: (v1_funct_1(k1_tmap_1(A_978, '#skF_2', C_977, '#skF_4', E_979, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_979, k1_zfmisc_1(k2_zfmisc_1(C_977, '#skF_2'))) | ~v1_funct_2(E_979, C_977, '#skF_2') | ~v1_funct_1(E_979) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_978)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_977, k1_zfmisc_1(A_978)) | v1_xboole_0(C_977) | v1_xboole_0('#skF_2') | v1_xboole_0(A_978))), inference(resolution, [status(thm)], [c_54, c_10763])).
% 10.57/4.00  tff(c_10770, plain, (![A_978, C_977, E_979]: (v1_funct_1(k1_tmap_1(A_978, '#skF_2', C_977, '#skF_4', E_979, '#skF_6')) | ~m1_subset_1(E_979, k1_zfmisc_1(k2_zfmisc_1(C_977, '#skF_2'))) | ~v1_funct_2(E_979, C_977, '#skF_2') | ~v1_funct_1(E_979) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_978)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_977, k1_zfmisc_1(A_978)) | v1_xboole_0(C_977) | v1_xboole_0('#skF_2') | v1_xboole_0(A_978))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_10765])).
% 10.57/4.00  tff(c_10881, plain, (![A_984, C_985, E_986]: (v1_funct_1(k1_tmap_1(A_984, '#skF_2', C_985, '#skF_4', E_986, '#skF_6')) | ~m1_subset_1(E_986, k1_zfmisc_1(k2_zfmisc_1(C_985, '#skF_2'))) | ~v1_funct_2(E_986, C_985, '#skF_2') | ~v1_funct_1(E_986) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_984)) | ~m1_subset_1(C_985, k1_zfmisc_1(A_984)) | v1_xboole_0(C_985) | v1_xboole_0(A_984))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_10770])).
% 10.57/4.00  tff(c_10885, plain, (![A_984]: (v1_funct_1(k1_tmap_1(A_984, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_984)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_984)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_984))), inference(resolution, [status(thm)], [c_60, c_10881])).
% 10.57/4.00  tff(c_10892, plain, (![A_984]: (v1_funct_1(k1_tmap_1(A_984, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_984)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_984)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_984))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_10885])).
% 10.57/4.00  tff(c_11237, plain, (![A_1003]: (v1_funct_1(k1_tmap_1(A_1003, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1003)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1003)) | v1_xboole_0(A_1003))), inference(negUnitSimplification, [status(thm)], [c_74, c_10892])).
% 10.57/4.00  tff(c_11240, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_11237])).
% 10.57/4.00  tff(c_11243, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_11240])).
% 10.57/4.00  tff(c_11244, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_11243])).
% 10.57/4.00  tff(c_10549, plain, (![D_959]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_959)=k7_relat_1('#skF_5', D_959))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_10543])).
% 10.57/4.00  tff(c_48, plain, (![E_165, C_163, F_166, A_161, B_162, D_164]: (v1_funct_2(k1_tmap_1(A_161, B_162, C_163, D_164, E_165, F_166), k4_subset_1(A_161, C_163, D_164), B_162) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(D_164, B_162))) | ~v1_funct_2(F_166, D_164, B_162) | ~v1_funct_1(F_166) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_163, B_162))) | ~v1_funct_2(E_165, C_163, B_162) | ~v1_funct_1(E_165) | ~m1_subset_1(D_164, k1_zfmisc_1(A_161)) | v1_xboole_0(D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | v1_xboole_0(C_163) | v1_xboole_0(B_162) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_188])).
% 10.57/4.00  tff(c_46, plain, (![E_165, C_163, F_166, A_161, B_162, D_164]: (m1_subset_1(k1_tmap_1(A_161, B_162, C_163, D_164, E_165, F_166), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_161, C_163, D_164), B_162))) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(D_164, B_162))) | ~v1_funct_2(F_166, D_164, B_162) | ~v1_funct_1(F_166) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(C_163, B_162))) | ~v1_funct_2(E_165, C_163, B_162) | ~v1_funct_1(E_165) | ~m1_subset_1(D_164, k1_zfmisc_1(A_161)) | v1_xboole_0(D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | v1_xboole_0(C_163) | v1_xboole_0(B_162) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_188])).
% 10.57/4.00  tff(c_11703, plain, (![C_1026, E_1029, B_1028, A_1025, F_1027, D_1030]: (k2_partfun1(k4_subset_1(A_1025, C_1026, D_1030), B_1028, k1_tmap_1(A_1025, B_1028, C_1026, D_1030, E_1029, F_1027), C_1026)=E_1029 | ~m1_subset_1(k1_tmap_1(A_1025, B_1028, C_1026, D_1030, E_1029, F_1027), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1025, C_1026, D_1030), B_1028))) | ~v1_funct_2(k1_tmap_1(A_1025, B_1028, C_1026, D_1030, E_1029, F_1027), k4_subset_1(A_1025, C_1026, D_1030), B_1028) | ~v1_funct_1(k1_tmap_1(A_1025, B_1028, C_1026, D_1030, E_1029, F_1027)) | k2_partfun1(D_1030, B_1028, F_1027, k9_subset_1(A_1025, C_1026, D_1030))!=k2_partfun1(C_1026, B_1028, E_1029, k9_subset_1(A_1025, C_1026, D_1030)) | ~m1_subset_1(F_1027, k1_zfmisc_1(k2_zfmisc_1(D_1030, B_1028))) | ~v1_funct_2(F_1027, D_1030, B_1028) | ~v1_funct_1(F_1027) | ~m1_subset_1(E_1029, k1_zfmisc_1(k2_zfmisc_1(C_1026, B_1028))) | ~v1_funct_2(E_1029, C_1026, B_1028) | ~v1_funct_1(E_1029) | ~m1_subset_1(D_1030, k1_zfmisc_1(A_1025)) | v1_xboole_0(D_1030) | ~m1_subset_1(C_1026, k1_zfmisc_1(A_1025)) | v1_xboole_0(C_1026) | v1_xboole_0(B_1028) | v1_xboole_0(A_1025))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.57/4.00  tff(c_13655, plain, (![C_1189, B_1187, E_1191, A_1190, F_1192, D_1188]: (k2_partfun1(k4_subset_1(A_1190, C_1189, D_1188), B_1187, k1_tmap_1(A_1190, B_1187, C_1189, D_1188, E_1191, F_1192), C_1189)=E_1191 | ~v1_funct_2(k1_tmap_1(A_1190, B_1187, C_1189, D_1188, E_1191, F_1192), k4_subset_1(A_1190, C_1189, D_1188), B_1187) | ~v1_funct_1(k1_tmap_1(A_1190, B_1187, C_1189, D_1188, E_1191, F_1192)) | k2_partfun1(D_1188, B_1187, F_1192, k9_subset_1(A_1190, C_1189, D_1188))!=k2_partfun1(C_1189, B_1187, E_1191, k9_subset_1(A_1190, C_1189, D_1188)) | ~m1_subset_1(F_1192, k1_zfmisc_1(k2_zfmisc_1(D_1188, B_1187))) | ~v1_funct_2(F_1192, D_1188, B_1187) | ~v1_funct_1(F_1192) | ~m1_subset_1(E_1191, k1_zfmisc_1(k2_zfmisc_1(C_1189, B_1187))) | ~v1_funct_2(E_1191, C_1189, B_1187) | ~v1_funct_1(E_1191) | ~m1_subset_1(D_1188, k1_zfmisc_1(A_1190)) | v1_xboole_0(D_1188) | ~m1_subset_1(C_1189, k1_zfmisc_1(A_1190)) | v1_xboole_0(C_1189) | v1_xboole_0(B_1187) | v1_xboole_0(A_1190))), inference(resolution, [status(thm)], [c_46, c_11703])).
% 10.57/4.00  tff(c_15482, plain, (![B_1275, A_1278, C_1277, E_1279, F_1280, D_1276]: (k2_partfun1(k4_subset_1(A_1278, C_1277, D_1276), B_1275, k1_tmap_1(A_1278, B_1275, C_1277, D_1276, E_1279, F_1280), C_1277)=E_1279 | ~v1_funct_1(k1_tmap_1(A_1278, B_1275, C_1277, D_1276, E_1279, F_1280)) | k2_partfun1(D_1276, B_1275, F_1280, k9_subset_1(A_1278, C_1277, D_1276))!=k2_partfun1(C_1277, B_1275, E_1279, k9_subset_1(A_1278, C_1277, D_1276)) | ~m1_subset_1(F_1280, k1_zfmisc_1(k2_zfmisc_1(D_1276, B_1275))) | ~v1_funct_2(F_1280, D_1276, B_1275) | ~v1_funct_1(F_1280) | ~m1_subset_1(E_1279, k1_zfmisc_1(k2_zfmisc_1(C_1277, B_1275))) | ~v1_funct_2(E_1279, C_1277, B_1275) | ~v1_funct_1(E_1279) | ~m1_subset_1(D_1276, k1_zfmisc_1(A_1278)) | v1_xboole_0(D_1276) | ~m1_subset_1(C_1277, k1_zfmisc_1(A_1278)) | v1_xboole_0(C_1277) | v1_xboole_0(B_1275) | v1_xboole_0(A_1278))), inference(resolution, [status(thm)], [c_48, c_13655])).
% 10.57/4.00  tff(c_15486, plain, (![A_1278, C_1277, E_1279]: (k2_partfun1(k4_subset_1(A_1278, C_1277, '#skF_4'), '#skF_2', k1_tmap_1(A_1278, '#skF_2', C_1277, '#skF_4', E_1279, '#skF_6'), C_1277)=E_1279 | ~v1_funct_1(k1_tmap_1(A_1278, '#skF_2', C_1277, '#skF_4', E_1279, '#skF_6')) | k2_partfun1(C_1277, '#skF_2', E_1279, k9_subset_1(A_1278, C_1277, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_1278, C_1277, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1279, k1_zfmisc_1(k2_zfmisc_1(C_1277, '#skF_2'))) | ~v1_funct_2(E_1279, C_1277, '#skF_2') | ~v1_funct_1(E_1279) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1278)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1277, k1_zfmisc_1(A_1278)) | v1_xboole_0(C_1277) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1278))), inference(resolution, [status(thm)], [c_54, c_15482])).
% 10.57/4.00  tff(c_15492, plain, (![A_1278, C_1277, E_1279]: (k2_partfun1(k4_subset_1(A_1278, C_1277, '#skF_4'), '#skF_2', k1_tmap_1(A_1278, '#skF_2', C_1277, '#skF_4', E_1279, '#skF_6'), C_1277)=E_1279 | ~v1_funct_1(k1_tmap_1(A_1278, '#skF_2', C_1277, '#skF_4', E_1279, '#skF_6')) | k2_partfun1(C_1277, '#skF_2', E_1279, k9_subset_1(A_1278, C_1277, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1278, C_1277, '#skF_4')) | ~m1_subset_1(E_1279, k1_zfmisc_1(k2_zfmisc_1(C_1277, '#skF_2'))) | ~v1_funct_2(E_1279, C_1277, '#skF_2') | ~v1_funct_1(E_1279) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1278)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_1277, k1_zfmisc_1(A_1278)) | v1_xboole_0(C_1277) | v1_xboole_0('#skF_2') | v1_xboole_0(A_1278))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_10546, c_15486])).
% 10.57/4.00  tff(c_15893, plain, (![A_1311, C_1312, E_1313]: (k2_partfun1(k4_subset_1(A_1311, C_1312, '#skF_4'), '#skF_2', k1_tmap_1(A_1311, '#skF_2', C_1312, '#skF_4', E_1313, '#skF_6'), C_1312)=E_1313 | ~v1_funct_1(k1_tmap_1(A_1311, '#skF_2', C_1312, '#skF_4', E_1313, '#skF_6')) | k2_partfun1(C_1312, '#skF_2', E_1313, k9_subset_1(A_1311, C_1312, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1311, C_1312, '#skF_4')) | ~m1_subset_1(E_1313, k1_zfmisc_1(k2_zfmisc_1(C_1312, '#skF_2'))) | ~v1_funct_2(E_1313, C_1312, '#skF_2') | ~v1_funct_1(E_1313) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1311)) | ~m1_subset_1(C_1312, k1_zfmisc_1(A_1311)) | v1_xboole_0(C_1312) | v1_xboole_0(A_1311))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_15492])).
% 10.57/4.00  tff(c_15900, plain, (![A_1311]: (k2_partfun1(k4_subset_1(A_1311, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1311, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1311, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_1311, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1311, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1311)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1311)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1311))), inference(resolution, [status(thm)], [c_60, c_15893])).
% 10.57/4.00  tff(c_15910, plain, (![A_1311]: (k2_partfun1(k4_subset_1(A_1311, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1311, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1311, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1311, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1311, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1311)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1311)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1311))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_10549, c_15900])).
% 10.57/4.00  tff(c_16752, plain, (![A_1334]: (k2_partfun1(k4_subset_1(A_1334, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_1334, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')='#skF_5' | ~v1_funct_1(k1_tmap_1(A_1334, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_1334, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_1334, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1334)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_1334)) | v1_xboole_0(A_1334))), inference(negUnitSimplification, [status(thm)], [c_74, c_15910])).
% 10.57/4.00  tff(c_2553, plain, (~v1_partfun1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1841])).
% 10.57/4.00  tff(c_2859, plain, (![C_492, A_493, B_494]: (v1_partfun1(C_492, A_493) | ~v1_funct_2(C_492, A_493, B_494) | ~v1_funct_1(C_492) | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(A_493, B_494))) | v1_xboole_0(B_494))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.57/4.00  tff(c_2862, plain, (v1_partfun1('#skF_6', '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_2859])).
% 10.57/4.00  tff(c_2868, plain, (v1_partfun1('#skF_6', '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2862])).
% 10.57/4.00  tff(c_2870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2553, c_2868])).
% 10.57/4.00  tff(c_2871, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1841])).
% 10.57/4.00  tff(c_2882, plain, (![B_11]: (k7_relat_1('#skF_6', B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, '#skF_4') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2871, c_10])).
% 10.57/4.00  tff(c_2906, plain, (![B_496]: (k7_relat_1('#skF_6', B_496)=k1_xboole_0 | ~r1_xboole_0(B_496, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2882])).
% 10.57/4.00  tff(c_2910, plain, (![A_16]: (k7_relat_1('#skF_6', A_16)=k1_xboole_0 | ~r1_subset_1(A_16, '#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_22, c_2906])).
% 10.57/4.00  tff(c_3078, plain, (![A_505]: (k7_relat_1('#skF_6', A_505)=k1_xboole_0 | ~r1_subset_1(A_505, '#skF_4') | v1_xboole_0(A_505))), inference(negUnitSimplification, [status(thm)], [c_70, c_2910])).
% 10.57/4.00  tff(c_3081, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3078])).
% 10.57/4.00  tff(c_3084, plain, (k7_relat_1('#skF_6', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_3081])).
% 10.57/4.00  tff(c_2879, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2871, c_18])).
% 10.57/4.00  tff(c_2888, plain, (![A_14]: (k1_relat_1(k7_relat_1('#skF_6', A_14))=k3_xboole_0('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2879])).
% 10.57/4.00  tff(c_3088, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3084, c_2888])).
% 10.57/4.00  tff(c_3091, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3088])).
% 10.57/4.00  tff(c_2893, plain, (![B_495]: (k7_relat_1('#skF_5', B_495)=k1_xboole_0 | ~r1_xboole_0(B_495, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2541])).
% 10.57/4.00  tff(c_2957, plain, (![A_499]: (k7_relat_1('#skF_5', A_499)=k1_xboole_0 | k3_xboole_0(A_499, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2893])).
% 10.57/4.00  tff(c_2963, plain, (![A_499]: (k3_xboole_0('#skF_3', A_499)=k1_relat_1(k1_xboole_0) | k3_xboole_0(A_499, '#skF_3')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2957, c_2547])).
% 10.57/4.00  tff(c_3240, plain, (![A_515]: (k3_xboole_0('#skF_3', A_515)=k1_xboole_0 | k3_xboole_0(A_515, '#skF_3')!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2963])).
% 10.57/4.00  tff(c_3246, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3091, c_3240])).
% 10.57/4.00  tff(c_2970, plain, (![B_500, A_501]: (k7_relat_1(B_500, k3_xboole_0(k1_relat_1(B_500), A_501))=k7_relat_1(B_500, A_501) | ~v1_relat_1(B_500))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.57/4.00  tff(c_3004, plain, (![A_501]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_501))=k7_relat_1('#skF_5', A_501) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2530, c_2970])).
% 10.57/4.00  tff(c_3024, plain, (![A_501]: (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', A_501))=k7_relat_1('#skF_5', A_501))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_3004])).
% 10.57/4.00  tff(c_3255, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k7_relat_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3246, c_3024])).
% 10.57/4.00  tff(c_3262, plain, (![A_516, B_517, C_518, D_519]: (k2_partfun1(A_516, B_517, C_518, D_519)=k7_relat_1(C_518, D_519) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(A_516, B_517))) | ~v1_funct_1(C_518))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.57/4.00  tff(c_3266, plain, (![D_519]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_519)=k7_relat_1('#skF_5', D_519) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_3262])).
% 10.57/4.00  tff(c_3272, plain, (![D_519]: (k2_partfun1('#skF_3', '#skF_2', '#skF_5', D_519)=k7_relat_1('#skF_5', D_519))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3266])).
% 10.57/4.00  tff(c_3001, plain, (![A_501]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_501))=k7_relat_1('#skF_6', A_501) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2871, c_2970])).
% 10.57/4.00  tff(c_3022, plain, (![A_501]: (k7_relat_1('#skF_6', k3_xboole_0('#skF_4', A_501))=k7_relat_1('#skF_6', A_501))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_3001])).
% 10.57/4.00  tff(c_3099, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k7_relat_1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3091, c_3022])).
% 10.57/4.00  tff(c_3103, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3084, c_3099])).
% 10.57/4.00  tff(c_3264, plain, (![D_519]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_519)=k7_relat_1('#skF_6', D_519) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_3262])).
% 10.57/4.00  tff(c_3269, plain, (![D_519]: (k2_partfun1('#skF_4', '#skF_2', '#skF_6', D_519)=k7_relat_1('#skF_6', D_519))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3264])).
% 10.57/4.00  tff(c_3172, plain, (![A_507, B_508, C_509]: (k9_subset_1(A_507, B_508, C_509)=k3_xboole_0(B_508, C_509) | ~m1_subset_1(C_509, k1_zfmisc_1(A_507)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.57/4.00  tff(c_3184, plain, (![B_508]: (k9_subset_1('#skF_1', B_508, '#skF_4')=k3_xboole_0(B_508, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_3172])).
% 10.57/4.00  tff(c_3194, plain, (k2_partfun1('#skF_3', '#skF_2', '#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3184, c_3184, c_1739])).
% 10.57/4.00  tff(c_3368, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3272, c_3103, c_3269, c_3246, c_3246, c_3194])).
% 10.57/4.00  tff(c_3404, plain, (![A_532, E_533, C_531, D_530, B_529, F_534]: (v1_funct_1(k1_tmap_1(A_532, B_529, C_531, D_530, E_533, F_534)) | ~m1_subset_1(F_534, k1_zfmisc_1(k2_zfmisc_1(D_530, B_529))) | ~v1_funct_2(F_534, D_530, B_529) | ~v1_funct_1(F_534) | ~m1_subset_1(E_533, k1_zfmisc_1(k2_zfmisc_1(C_531, B_529))) | ~v1_funct_2(E_533, C_531, B_529) | ~v1_funct_1(E_533) | ~m1_subset_1(D_530, k1_zfmisc_1(A_532)) | v1_xboole_0(D_530) | ~m1_subset_1(C_531, k1_zfmisc_1(A_532)) | v1_xboole_0(C_531) | v1_xboole_0(B_529) | v1_xboole_0(A_532))), inference(cnfTransformation, [status(thm)], [f_188])).
% 10.57/4.00  tff(c_3406, plain, (![A_532, C_531, E_533]: (v1_funct_1(k1_tmap_1(A_532, '#skF_2', C_531, '#skF_4', E_533, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_533, k1_zfmisc_1(k2_zfmisc_1(C_531, '#skF_2'))) | ~v1_funct_2(E_533, C_531, '#skF_2') | ~v1_funct_1(E_533) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_532)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_531, k1_zfmisc_1(A_532)) | v1_xboole_0(C_531) | v1_xboole_0('#skF_2') | v1_xboole_0(A_532))), inference(resolution, [status(thm)], [c_54, c_3404])).
% 10.57/4.00  tff(c_3411, plain, (![A_532, C_531, E_533]: (v1_funct_1(k1_tmap_1(A_532, '#skF_2', C_531, '#skF_4', E_533, '#skF_6')) | ~m1_subset_1(E_533, k1_zfmisc_1(k2_zfmisc_1(C_531, '#skF_2'))) | ~v1_funct_2(E_533, C_531, '#skF_2') | ~v1_funct_1(E_533) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_532)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_531, k1_zfmisc_1(A_532)) | v1_xboole_0(C_531) | v1_xboole_0('#skF_2') | v1_xboole_0(A_532))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3406])).
% 10.57/4.00  tff(c_4441, plain, (![A_590, C_591, E_592]: (v1_funct_1(k1_tmap_1(A_590, '#skF_2', C_591, '#skF_4', E_592, '#skF_6')) | ~m1_subset_1(E_592, k1_zfmisc_1(k2_zfmisc_1(C_591, '#skF_2'))) | ~v1_funct_2(E_592, C_591, '#skF_2') | ~v1_funct_1(E_592) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_590)) | ~m1_subset_1(C_591, k1_zfmisc_1(A_590)) | v1_xboole_0(C_591) | v1_xboole_0(A_590))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_3411])).
% 10.57/4.00  tff(c_4448, plain, (![A_590]: (v1_funct_1(k1_tmap_1(A_590, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_590)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_590)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_590))), inference(resolution, [status(thm)], [c_60, c_4441])).
% 10.57/4.00  tff(c_4458, plain, (![A_590]: (v1_funct_1(k1_tmap_1(A_590, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_590)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_590)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_590))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_4448])).
% 10.57/4.00  tff(c_4519, plain, (![A_604]: (v1_funct_1(k1_tmap_1(A_604, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_604)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_604)) | v1_xboole_0(A_604))), inference(negUnitSimplification, [status(thm)], [c_74, c_4458])).
% 10.57/4.00  tff(c_4522, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_4519])).
% 10.57/4.00  tff(c_4525, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4522])).
% 10.57/4.00  tff(c_4526, plain, (v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_4525])).
% 10.57/4.00  tff(c_4402, plain, (![C_584, E_587, F_585, B_586, D_588, A_583]: (k2_partfun1(k4_subset_1(A_583, C_584, D_588), B_586, k1_tmap_1(A_583, B_586, C_584, D_588, E_587, F_585), D_588)=F_585 | ~m1_subset_1(k1_tmap_1(A_583, B_586, C_584, D_588, E_587, F_585), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_583, C_584, D_588), B_586))) | ~v1_funct_2(k1_tmap_1(A_583, B_586, C_584, D_588, E_587, F_585), k4_subset_1(A_583, C_584, D_588), B_586) | ~v1_funct_1(k1_tmap_1(A_583, B_586, C_584, D_588, E_587, F_585)) | k2_partfun1(D_588, B_586, F_585, k9_subset_1(A_583, C_584, D_588))!=k2_partfun1(C_584, B_586, E_587, k9_subset_1(A_583, C_584, D_588)) | ~m1_subset_1(F_585, k1_zfmisc_1(k2_zfmisc_1(D_588, B_586))) | ~v1_funct_2(F_585, D_588, B_586) | ~v1_funct_1(F_585) | ~m1_subset_1(E_587, k1_zfmisc_1(k2_zfmisc_1(C_584, B_586))) | ~v1_funct_2(E_587, C_584, B_586) | ~v1_funct_1(E_587) | ~m1_subset_1(D_588, k1_zfmisc_1(A_583)) | v1_xboole_0(D_588) | ~m1_subset_1(C_584, k1_zfmisc_1(A_583)) | v1_xboole_0(C_584) | v1_xboole_0(B_586) | v1_xboole_0(A_583))), inference(cnfTransformation, [status(thm)], [f_154])).
% 10.57/4.00  tff(c_6367, plain, (![C_742, F_745, E_744, D_741, B_740, A_743]: (k2_partfun1(k4_subset_1(A_743, C_742, D_741), B_740, k1_tmap_1(A_743, B_740, C_742, D_741, E_744, F_745), D_741)=F_745 | ~v1_funct_2(k1_tmap_1(A_743, B_740, C_742, D_741, E_744, F_745), k4_subset_1(A_743, C_742, D_741), B_740) | ~v1_funct_1(k1_tmap_1(A_743, B_740, C_742, D_741, E_744, F_745)) | k2_partfun1(D_741, B_740, F_745, k9_subset_1(A_743, C_742, D_741))!=k2_partfun1(C_742, B_740, E_744, k9_subset_1(A_743, C_742, D_741)) | ~m1_subset_1(F_745, k1_zfmisc_1(k2_zfmisc_1(D_741, B_740))) | ~v1_funct_2(F_745, D_741, B_740) | ~v1_funct_1(F_745) | ~m1_subset_1(E_744, k1_zfmisc_1(k2_zfmisc_1(C_742, B_740))) | ~v1_funct_2(E_744, C_742, B_740) | ~v1_funct_1(E_744) | ~m1_subset_1(D_741, k1_zfmisc_1(A_743)) | v1_xboole_0(D_741) | ~m1_subset_1(C_742, k1_zfmisc_1(A_743)) | v1_xboole_0(C_742) | v1_xboole_0(B_740) | v1_xboole_0(A_743))), inference(resolution, [status(thm)], [c_46, c_4402])).
% 10.57/4.00  tff(c_8193, plain, (![E_836, C_834, A_835, B_832, D_833, F_837]: (k2_partfun1(k4_subset_1(A_835, C_834, D_833), B_832, k1_tmap_1(A_835, B_832, C_834, D_833, E_836, F_837), D_833)=F_837 | ~v1_funct_1(k1_tmap_1(A_835, B_832, C_834, D_833, E_836, F_837)) | k2_partfun1(D_833, B_832, F_837, k9_subset_1(A_835, C_834, D_833))!=k2_partfun1(C_834, B_832, E_836, k9_subset_1(A_835, C_834, D_833)) | ~m1_subset_1(F_837, k1_zfmisc_1(k2_zfmisc_1(D_833, B_832))) | ~v1_funct_2(F_837, D_833, B_832) | ~v1_funct_1(F_837) | ~m1_subset_1(E_836, k1_zfmisc_1(k2_zfmisc_1(C_834, B_832))) | ~v1_funct_2(E_836, C_834, B_832) | ~v1_funct_1(E_836) | ~m1_subset_1(D_833, k1_zfmisc_1(A_835)) | v1_xboole_0(D_833) | ~m1_subset_1(C_834, k1_zfmisc_1(A_835)) | v1_xboole_0(C_834) | v1_xboole_0(B_832) | v1_xboole_0(A_835))), inference(resolution, [status(thm)], [c_48, c_6367])).
% 10.57/4.00  tff(c_8197, plain, (![A_835, C_834, E_836]: (k2_partfun1(k4_subset_1(A_835, C_834, '#skF_4'), '#skF_2', k1_tmap_1(A_835, '#skF_2', C_834, '#skF_4', E_836, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_835, '#skF_2', C_834, '#skF_4', E_836, '#skF_6')) | k2_partfun1(C_834, '#skF_2', E_836, k9_subset_1(A_835, C_834, '#skF_4'))!=k2_partfun1('#skF_4', '#skF_2', '#skF_6', k9_subset_1(A_835, C_834, '#skF_4')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_836, k1_zfmisc_1(k2_zfmisc_1(C_834, '#skF_2'))) | ~v1_funct_2(E_836, C_834, '#skF_2') | ~v1_funct_1(E_836) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_835)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_834, k1_zfmisc_1(A_835)) | v1_xboole_0(C_834) | v1_xboole_0('#skF_2') | v1_xboole_0(A_835))), inference(resolution, [status(thm)], [c_54, c_8193])).
% 10.57/4.00  tff(c_8203, plain, (![A_835, C_834, E_836]: (k2_partfun1(k4_subset_1(A_835, C_834, '#skF_4'), '#skF_2', k1_tmap_1(A_835, '#skF_2', C_834, '#skF_4', E_836, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_835, '#skF_2', C_834, '#skF_4', E_836, '#skF_6')) | k2_partfun1(C_834, '#skF_2', E_836, k9_subset_1(A_835, C_834, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_835, C_834, '#skF_4')) | ~m1_subset_1(E_836, k1_zfmisc_1(k2_zfmisc_1(C_834, '#skF_2'))) | ~v1_funct_2(E_836, C_834, '#skF_2') | ~v1_funct_1(E_836) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_835)) | v1_xboole_0('#skF_4') | ~m1_subset_1(C_834, k1_zfmisc_1(A_835)) | v1_xboole_0(C_834) | v1_xboole_0('#skF_2') | v1_xboole_0(A_835))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3269, c_8197])).
% 10.57/4.00  tff(c_9617, plain, (![A_895, C_896, E_897]: (k2_partfun1(k4_subset_1(A_895, C_896, '#skF_4'), '#skF_2', k1_tmap_1(A_895, '#skF_2', C_896, '#skF_4', E_897, '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_895, '#skF_2', C_896, '#skF_4', E_897, '#skF_6')) | k2_partfun1(C_896, '#skF_2', E_897, k9_subset_1(A_895, C_896, '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_895, C_896, '#skF_4')) | ~m1_subset_1(E_897, k1_zfmisc_1(k2_zfmisc_1(C_896, '#skF_2'))) | ~v1_funct_2(E_897, C_896, '#skF_2') | ~v1_funct_1(E_897) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_895)) | ~m1_subset_1(C_896, k1_zfmisc_1(A_895)) | v1_xboole_0(C_896) | v1_xboole_0(A_895))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_8203])).
% 10.57/4.00  tff(c_9624, plain, (![A_895]: (k2_partfun1(k4_subset_1(A_895, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_895, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_895, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k2_partfun1('#skF_3', '#skF_2', '#skF_5', k9_subset_1(A_895, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_895, '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_895)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_895)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_895))), inference(resolution, [status(thm)], [c_60, c_9617])).
% 10.57/4.00  tff(c_9634, plain, (![A_895]: (k2_partfun1(k4_subset_1(A_895, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_895, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_895, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_895, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_895, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_895)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_895)) | v1_xboole_0('#skF_3') | v1_xboole_0(A_895))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_3272, c_9624])).
% 10.57/4.00  tff(c_9636, plain, (![A_898]: (k2_partfun1(k4_subset_1(A_898, '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1(A_898, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_898, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1(A_898, '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1(A_898, '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_898)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_898)) | v1_xboole_0(A_898))), inference(negUnitSimplification, [status(thm)], [c_74, c_9634])).
% 10.57/4.00  tff(c_1738, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5' | k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 10.57/4.00  tff(c_2552, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')!='#skF_6'), inference(splitLeft, [status(thm)], [c_1738])).
% 10.57/4.00  tff(c_9647, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9636, c_2552])).
% 10.57/4.00  tff(c_9661, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_3368, c_3103, c_3246, c_3184, c_3024, c_3184, c_4526, c_9647])).
% 10.57/4.00  tff(c_9663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_9661])).
% 10.57/4.00  tff(c_9664, plain, (k2_partfun1(k4_subset_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2', k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_1738])).
% 10.57/4.00  tff(c_16761, plain, (~v1_funct_1(k1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | k7_relat_1('#skF_5', k9_subset_1('#skF_1', '#skF_3', '#skF_4'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16752, c_9664])).
% 10.57/4.00  tff(c_16772, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_10571, c_10396, c_10359, c_10359, c_10204, c_10204, c_11244, c_16761])).
% 10.57/4.00  tff(c_16774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_16772])).
% 10.57/4.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/4.00  
% 10.57/4.00  Inference rules
% 10.57/4.00  ----------------------
% 10.57/4.00  #Ref     : 0
% 10.57/4.00  #Sup     : 3673
% 10.57/4.00  #Fact    : 0
% 10.57/4.00  #Define  : 0
% 10.57/4.00  #Split   : 54
% 10.57/4.00  #Chain   : 0
% 10.57/4.00  #Close   : 0
% 10.57/4.00  
% 10.57/4.00  Ordering : KBO
% 10.57/4.00  
% 10.57/4.00  Simplification rules
% 10.57/4.00  ----------------------
% 10.57/4.00  #Subsume      : 1831
% 10.57/4.00  #Demod        : 8576
% 10.57/4.00  #Tautology    : 789
% 10.57/4.00  #SimpNegUnit  : 192
% 10.57/4.00  #BackRed      : 17
% 10.57/4.00  
% 10.57/4.00  #Partial instantiations: 0
% 10.57/4.00  #Strategies tried      : 1
% 10.57/4.00  
% 10.57/4.00  Timing (in seconds)
% 10.57/4.00  ----------------------
% 10.57/4.01  Preprocessing        : 0.41
% 10.57/4.01  Parsing              : 0.20
% 10.57/4.01  CNF conversion       : 0.06
% 10.57/4.01  Main loop            : 2.75
% 10.57/4.01  Inferencing          : 0.79
% 10.57/4.01  Reduction            : 1.18
% 10.57/4.01  Demodulation         : 0.92
% 10.57/4.01  BG Simplification    : 0.08
% 10.57/4.01  Subsumption          : 0.58
% 10.57/4.01  Abstraction          : 0.11
% 10.57/4.01  MUC search           : 0.00
% 10.57/4.01  Cooper               : 0.00
% 10.57/4.01  Total                : 3.25
% 10.57/4.01  Index Insertion      : 0.00
% 10.57/4.01  Index Deletion       : 0.00
% 10.57/4.01  Index Matching       : 0.00
% 10.57/4.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
