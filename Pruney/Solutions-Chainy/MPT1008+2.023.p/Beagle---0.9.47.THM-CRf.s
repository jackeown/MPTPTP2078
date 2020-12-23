%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:29 EST 2020

% Result     : Theorem 8.83s
% Output     : CNFRefutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 267 expanded)
%              Number of leaves         :   42 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  200 ( 584 expanded)
%              Number of equality atoms :  106 ( 280 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_103,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_132,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_136,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_132])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_143,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_136,c_50])).

tff(c_145,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_394,plain,(
    ! [B_117,A_118] :
      ( k1_tarski(k1_funct_1(B_117,A_118)) = k2_relat_1(B_117)
      | k1_tarski(A_118) != k1_relat_1(B_117)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_337,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_341,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_337])).

tff(c_66,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_357,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_66])).

tff(c_400,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_357])).

tff(c_425,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74,c_400])).

tff(c_260,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_264,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_260])).

tff(c_42,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_536,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( k1_enumset1(A_136,B_137,C_138) = D_139
      | k2_tarski(A_136,C_138) = D_139
      | k2_tarski(B_137,C_138) = D_139
      | k2_tarski(A_136,B_137) = D_139
      | k1_tarski(C_138) = D_139
      | k1_tarski(B_137) = D_139
      | k1_tarski(A_136) = D_139
      | k1_xboole_0 = D_139
      | ~ r1_tarski(D_139,k1_enumset1(A_136,B_137,C_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_556,plain,(
    ! [A_10,B_11,D_139] :
      ( k1_enumset1(A_10,A_10,B_11) = D_139
      | k2_tarski(A_10,B_11) = D_139
      | k2_tarski(A_10,B_11) = D_139
      | k2_tarski(A_10,A_10) = D_139
      | k1_tarski(B_11) = D_139
      | k1_tarski(A_10) = D_139
      | k1_tarski(A_10) = D_139
      | k1_xboole_0 = D_139
      | ~ r1_tarski(D_139,k2_tarski(A_10,B_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_536])).

tff(c_1774,plain,(
    ! [A_410,B_411,D_412] :
      ( k2_tarski(A_410,B_411) = D_412
      | k2_tarski(A_410,B_411) = D_412
      | k2_tarski(A_410,B_411) = D_412
      | k1_tarski(A_410) = D_412
      | k1_tarski(B_411) = D_412
      | k1_tarski(A_410) = D_412
      | k1_tarski(A_410) = D_412
      | k1_xboole_0 = D_412
      | ~ r1_tarski(D_412,k2_tarski(A_410,B_411)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_556])).

tff(c_1803,plain,(
    ! [A_9,D_412] :
      ( k2_tarski(A_9,A_9) = D_412
      | k2_tarski(A_9,A_9) = D_412
      | k2_tarski(A_9,A_9) = D_412
      | k1_tarski(A_9) = D_412
      | k1_tarski(A_9) = D_412
      | k1_tarski(A_9) = D_412
      | k1_tarski(A_9) = D_412
      | k1_xboole_0 = D_412
      | ~ r1_tarski(D_412,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1774])).

tff(c_3293,plain,(
    ! [A_655,D_656] :
      ( k1_tarski(A_655) = D_656
      | k1_tarski(A_655) = D_656
      | k1_tarski(A_655) = D_656
      | k1_tarski(A_655) = D_656
      | k1_tarski(A_655) = D_656
      | k1_tarski(A_655) = D_656
      | k1_tarski(A_655) = D_656
      | k1_xboole_0 = D_656
      | ~ r1_tarski(D_656,k1_tarski(A_655)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_16,c_1803])).

tff(c_3323,plain,(
    ! [A_657,B_658] :
      ( k1_tarski(A_657) = k1_relat_1(B_658)
      | k1_relat_1(B_658) = k1_xboole_0
      | ~ v4_relat_1(B_658,k1_tarski(A_657))
      | ~ v1_relat_1(B_658) ) ),
    inference(resolution,[status(thm)],[c_42,c_3293])).

tff(c_3329,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_264,c_3323])).

tff(c_3332,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_3329])).

tff(c_3334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_425,c_3332])).

tff(c_3335,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_3336,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_3348,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_3336])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3341,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_3335,c_44])).

tff(c_3571,plain,(
    ! [B_707,A_708] :
      ( k1_tarski(k1_funct_1(B_707,A_708)) = k2_relat_1(B_707)
      | k1_tarski(A_708) != k1_relat_1(B_707)
      | ~ v1_funct_1(B_707)
      | ~ v1_relat_1(B_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3554,plain,(
    ! [A_702,B_703,C_704] :
      ( k2_relset_1(A_702,B_703,C_704) = k2_relat_1(C_704)
      | ~ m1_subset_1(C_704,k1_zfmisc_1(k2_zfmisc_1(A_702,B_703))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3557,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3554])).

tff(c_3559,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3341,c_3557])).

tff(c_3560,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3559,c_66])).

tff(c_3580,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3571,c_3560])).

tff(c_3601,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74,c_3348,c_3341,c_3580])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3339,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_14])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3342,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_68])).

tff(c_72,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_64,plain,(
    ! [D_38,C_37,A_35,B_36] :
      ( r2_hidden(k1_funct_1(D_38,C_37),k2_relset_1(A_35,B_36,D_38))
      | k1_xboole_0 = B_36
      | ~ r2_hidden(C_37,A_35)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(D_38,A_35,B_36)
      | ~ v1_funct_1(D_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3676,plain,(
    ! [D_718,C_719,A_720,B_721] :
      ( r2_hidden(k1_funct_1(D_718,C_719),k2_relset_1(A_720,B_721,D_718))
      | B_721 = '#skF_4'
      | ~ r2_hidden(C_719,A_720)
      | ~ m1_subset_1(D_718,k1_zfmisc_1(k2_zfmisc_1(A_720,B_721)))
      | ~ v1_funct_2(D_718,A_720,B_721)
      | ~ v1_funct_1(D_718) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3335,c_64])).

tff(c_3684,plain,(
    ! [C_719] :
      ( r2_hidden(k1_funct_1('#skF_4',C_719),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_719,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3559,c_3676])).

tff(c_3688,plain,(
    ! [C_719] :
      ( r2_hidden(k1_funct_1('#skF_4',C_719),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_719,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_3684])).

tff(c_3697,plain,(
    ! [C_724] :
      ( r2_hidden(k1_funct_1('#skF_4',C_724),'#skF_4')
      | ~ r2_hidden(C_724,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3342,c_3688])).

tff(c_54,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3702,plain,(
    ! [C_724] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_724))
      | ~ r2_hidden(C_724,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3697,c_54])).

tff(c_3709,plain,(
    ! [C_725] : ~ r2_hidden(C_725,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3339,c_3702])).

tff(c_3720,plain,(
    ! [B_726] : r1_tarski(k1_tarski('#skF_2'),B_726) ),
    inference(resolution,[status(thm)],[c_6,c_3709])).

tff(c_3367,plain,(
    ! [B_661,A_662] :
      ( B_661 = A_662
      | ~ r1_tarski(B_661,A_662)
      | ~ r1_tarski(A_662,B_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3382,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3339,c_3367])).

tff(c_3735,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3720,c_3382])).

tff(c_3746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3601,c_3735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n020.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 18:20:22 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.83/3.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.15  
% 8.85/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.85/3.15  
% 8.85/3.15  %Foreground sorts:
% 8.85/3.15  
% 8.85/3.15  
% 8.85/3.15  %Background operators:
% 8.85/3.15  
% 8.85/3.15  
% 8.85/3.15  %Foreground operators:
% 8.85/3.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.85/3.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.85/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.85/3.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.85/3.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.85/3.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.85/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.85/3.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.85/3.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.85/3.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.85/3.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.85/3.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.85/3.15  tff('#skF_2', type, '#skF_2': $i).
% 8.85/3.15  tff('#skF_3', type, '#skF_3': $i).
% 8.85/3.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.85/3.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.85/3.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.85/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.85/3.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.85/3.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.85/3.15  tff('#skF_4', type, '#skF_4': $i).
% 8.85/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.85/3.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.85/3.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.85/3.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.85/3.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.85/3.15  
% 8.85/3.17  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 8.85/3.17  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.85/3.17  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.85/3.17  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 8.85/3.17  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.85/3.17  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.85/3.17  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.85/3.17  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.85/3.17  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.85/3.17  tff(f_73, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 8.85/3.17  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.85/3.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.85/3.17  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.85/3.17  tff(f_129, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 8.85/3.17  tff(f_103, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.85/3.17  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.85/3.17  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.85/3.17  tff(c_132, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.85/3.17  tff(c_136, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_132])).
% 8.85/3.17  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.85/3.17  tff(c_50, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.85/3.17  tff(c_143, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_136, c_50])).
% 8.85/3.17  tff(c_145, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_143])).
% 8.85/3.17  tff(c_394, plain, (![B_117, A_118]: (k1_tarski(k1_funct_1(B_117, A_118))=k2_relat_1(B_117) | k1_tarski(A_118)!=k1_relat_1(B_117) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.85/3.17  tff(c_337, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.85/3.17  tff(c_341, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_337])).
% 8.85/3.17  tff(c_66, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.85/3.17  tff(c_357, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_66])).
% 8.85/3.17  tff(c_400, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_394, c_357])).
% 8.85/3.17  tff(c_425, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74, c_400])).
% 8.85/3.17  tff(c_260, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.85/3.17  tff(c_264, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_70, c_260])).
% 8.85/3.17  tff(c_42, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.85/3.17  tff(c_16, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.85/3.17  tff(c_18, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.85/3.17  tff(c_536, plain, (![A_136, B_137, C_138, D_139]: (k1_enumset1(A_136, B_137, C_138)=D_139 | k2_tarski(A_136, C_138)=D_139 | k2_tarski(B_137, C_138)=D_139 | k2_tarski(A_136, B_137)=D_139 | k1_tarski(C_138)=D_139 | k1_tarski(B_137)=D_139 | k1_tarski(A_136)=D_139 | k1_xboole_0=D_139 | ~r1_tarski(D_139, k1_enumset1(A_136, B_137, C_138)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.85/3.17  tff(c_556, plain, (![A_10, B_11, D_139]: (k1_enumset1(A_10, A_10, B_11)=D_139 | k2_tarski(A_10, B_11)=D_139 | k2_tarski(A_10, B_11)=D_139 | k2_tarski(A_10, A_10)=D_139 | k1_tarski(B_11)=D_139 | k1_tarski(A_10)=D_139 | k1_tarski(A_10)=D_139 | k1_xboole_0=D_139 | ~r1_tarski(D_139, k2_tarski(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_536])).
% 8.85/3.17  tff(c_1774, plain, (![A_410, B_411, D_412]: (k2_tarski(A_410, B_411)=D_412 | k2_tarski(A_410, B_411)=D_412 | k2_tarski(A_410, B_411)=D_412 | k1_tarski(A_410)=D_412 | k1_tarski(B_411)=D_412 | k1_tarski(A_410)=D_412 | k1_tarski(A_410)=D_412 | k1_xboole_0=D_412 | ~r1_tarski(D_412, k2_tarski(A_410, B_411)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_556])).
% 8.85/3.17  tff(c_1803, plain, (![A_9, D_412]: (k2_tarski(A_9, A_9)=D_412 | k2_tarski(A_9, A_9)=D_412 | k2_tarski(A_9, A_9)=D_412 | k1_tarski(A_9)=D_412 | k1_tarski(A_9)=D_412 | k1_tarski(A_9)=D_412 | k1_tarski(A_9)=D_412 | k1_xboole_0=D_412 | ~r1_tarski(D_412, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1774])).
% 8.85/3.17  tff(c_3293, plain, (![A_655, D_656]: (k1_tarski(A_655)=D_656 | k1_tarski(A_655)=D_656 | k1_tarski(A_655)=D_656 | k1_tarski(A_655)=D_656 | k1_tarski(A_655)=D_656 | k1_tarski(A_655)=D_656 | k1_tarski(A_655)=D_656 | k1_xboole_0=D_656 | ~r1_tarski(D_656, k1_tarski(A_655)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_16, c_1803])).
% 8.85/3.17  tff(c_3323, plain, (![A_657, B_658]: (k1_tarski(A_657)=k1_relat_1(B_658) | k1_relat_1(B_658)=k1_xboole_0 | ~v4_relat_1(B_658, k1_tarski(A_657)) | ~v1_relat_1(B_658))), inference(resolution, [status(thm)], [c_42, c_3293])).
% 8.85/3.17  tff(c_3329, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_264, c_3323])).
% 8.85/3.17  tff(c_3332, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_136, c_3329])).
% 8.85/3.17  tff(c_3334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_425, c_3332])).
% 8.85/3.17  tff(c_3335, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_143])).
% 8.85/3.17  tff(c_3336, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_143])).
% 8.85/3.17  tff(c_3348, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_3336])).
% 8.85/3.17  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.85/3.17  tff(c_3341, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_3335, c_44])).
% 8.85/3.17  tff(c_3571, plain, (![B_707, A_708]: (k1_tarski(k1_funct_1(B_707, A_708))=k2_relat_1(B_707) | k1_tarski(A_708)!=k1_relat_1(B_707) | ~v1_funct_1(B_707) | ~v1_relat_1(B_707))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.85/3.17  tff(c_3554, plain, (![A_702, B_703, C_704]: (k2_relset_1(A_702, B_703, C_704)=k2_relat_1(C_704) | ~m1_subset_1(C_704, k1_zfmisc_1(k2_zfmisc_1(A_702, B_703))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.85/3.17  tff(c_3557, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3554])).
% 8.85/3.17  tff(c_3559, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3341, c_3557])).
% 8.85/3.17  tff(c_3560, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3559, c_66])).
% 8.85/3.17  tff(c_3580, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3571, c_3560])).
% 8.85/3.17  tff(c_3601, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74, c_3348, c_3341, c_3580])).
% 8.85/3.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.85/3.17  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.85/3.17  tff(c_3339, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_14])).
% 8.85/3.17  tff(c_68, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.85/3.17  tff(c_3342, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_68])).
% 8.85/3.17  tff(c_72, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.85/3.17  tff(c_64, plain, (![D_38, C_37, A_35, B_36]: (r2_hidden(k1_funct_1(D_38, C_37), k2_relset_1(A_35, B_36, D_38)) | k1_xboole_0=B_36 | ~r2_hidden(C_37, A_35) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(D_38, A_35, B_36) | ~v1_funct_1(D_38))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.85/3.17  tff(c_3676, plain, (![D_718, C_719, A_720, B_721]: (r2_hidden(k1_funct_1(D_718, C_719), k2_relset_1(A_720, B_721, D_718)) | B_721='#skF_4' | ~r2_hidden(C_719, A_720) | ~m1_subset_1(D_718, k1_zfmisc_1(k2_zfmisc_1(A_720, B_721))) | ~v1_funct_2(D_718, A_720, B_721) | ~v1_funct_1(D_718))), inference(demodulation, [status(thm), theory('equality')], [c_3335, c_64])).
% 8.85/3.17  tff(c_3684, plain, (![C_719]: (r2_hidden(k1_funct_1('#skF_4', C_719), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_719, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3559, c_3676])).
% 8.85/3.17  tff(c_3688, plain, (![C_719]: (r2_hidden(k1_funct_1('#skF_4', C_719), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_719, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_3684])).
% 8.85/3.17  tff(c_3697, plain, (![C_724]: (r2_hidden(k1_funct_1('#skF_4', C_724), '#skF_4') | ~r2_hidden(C_724, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_3342, c_3688])).
% 8.85/3.17  tff(c_54, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.85/3.17  tff(c_3702, plain, (![C_724]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_724)) | ~r2_hidden(C_724, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_3697, c_54])).
% 8.85/3.17  tff(c_3709, plain, (![C_725]: (~r2_hidden(C_725, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3339, c_3702])).
% 8.85/3.17  tff(c_3720, plain, (![B_726]: (r1_tarski(k1_tarski('#skF_2'), B_726))), inference(resolution, [status(thm)], [c_6, c_3709])).
% 8.85/3.17  tff(c_3367, plain, (![B_661, A_662]: (B_661=A_662 | ~r1_tarski(B_661, A_662) | ~r1_tarski(A_662, B_661))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.85/3.17  tff(c_3382, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(resolution, [status(thm)], [c_3339, c_3367])).
% 8.85/3.17  tff(c_3735, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_3720, c_3382])).
% 8.85/3.17  tff(c_3746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3601, c_3735])).
% 8.85/3.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.17  
% 8.85/3.17  Inference rules
% 8.85/3.17  ----------------------
% 8.85/3.17  #Ref     : 0
% 8.85/3.17  #Sup     : 929
% 8.85/3.17  #Fact    : 0
% 8.85/3.17  #Define  : 0
% 8.85/3.17  #Split   : 5
% 8.85/3.17  #Chain   : 0
% 8.85/3.17  #Close   : 0
% 8.85/3.17  
% 8.85/3.17  Ordering : KBO
% 8.85/3.17  
% 8.85/3.17  Simplification rules
% 8.85/3.17  ----------------------
% 8.85/3.17  #Subsume      : 223
% 8.85/3.17  #Demod        : 235
% 8.85/3.17  #Tautology    : 130
% 8.85/3.17  #SimpNegUnit  : 6
% 8.85/3.17  #BackRed      : 8
% 8.85/3.17  
% 8.85/3.17  #Partial instantiations: 0
% 8.85/3.17  #Strategies tried      : 1
% 8.85/3.17  
% 8.85/3.17  Timing (in seconds)
% 8.85/3.17  ----------------------
% 8.85/3.17  Preprocessing        : 0.54
% 8.85/3.17  Parsing              : 0.28
% 8.85/3.17  CNF conversion       : 0.04
% 8.85/3.17  Main loop            : 1.81
% 8.85/3.17  Inferencing          : 0.60
% 8.85/3.17  Reduction            : 0.47
% 8.85/3.18  Demodulation         : 0.33
% 8.85/3.18  BG Simplification    : 0.07
% 8.85/3.18  Subsumption          : 0.54
% 8.85/3.18  Abstraction          : 0.07
% 8.85/3.18  MUC search           : 0.00
% 8.85/3.18  Cooper               : 0.00
% 8.85/3.18  Total                : 2.39
% 8.85/3.18  Index Insertion      : 0.00
% 8.85/3.18  Index Deletion       : 0.00
% 8.85/3.18  Index Matching       : 0.00
% 8.85/3.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
