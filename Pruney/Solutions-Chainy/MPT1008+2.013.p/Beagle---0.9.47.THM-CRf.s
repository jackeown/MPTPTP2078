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
% DateTime   : Thu Dec  3 10:14:27 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 379 expanded)
%              Number of leaves         :   46 ( 144 expanded)
%              Depth                    :   14
%              Number of atoms          :  184 ( 803 expanded)
%              Number of equality atoms :   74 ( 329 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

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

tff(f_100,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_109,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_109])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_113,c_36])).

tff(c_122,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_163,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_167,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_163])).

tff(c_195,plain,(
    ! [B_81,A_82] :
      ( k7_relat_1(B_81,A_82) = B_81
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_198,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_195])).

tff(c_201,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_198])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_24])).

tff(c_209,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_205])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(A_15,k1_tarski(B_17)) = k11_relat_1(A_15,B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_230,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_22])).

tff(c_237,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_230])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,k1_relat_1(B_21))
      | k11_relat_1(B_21,A_20) = k1_xboole_0
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_373,plain,(
    ! [B_108,A_109] :
      ( k1_tarski(k1_funct_1(B_108,A_109)) = k11_relat_1(B_108,A_109)
      | ~ r2_hidden(A_109,k1_relat_1(B_108))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_409,plain,(
    ! [B_116,A_117] :
      ( k1_tarski(k1_funct_1(B_116,A_117)) = k11_relat_1(B_116,A_117)
      | ~ v1_funct_1(B_116)
      | k11_relat_1(B_116,A_117) = k1_xboole_0
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_26,c_373])).

tff(c_283,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_287,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_283])).

tff(c_56,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_288,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_56])).

tff(c_418,plain,
    ( k11_relat_1('#skF_4','#skF_2') != k2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_288])).

tff(c_430,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_237,c_64,c_237,c_418])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_430])).

tff(c_433,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_439,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_433,c_34])).

tff(c_434,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_449,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_434])).

tff(c_673,plain,(
    ! [B_155,A_156] :
      ( k1_tarski(k1_funct_1(B_155,A_156)) = k2_relat_1(B_155)
      | k1_tarski(A_156) != k1_relat_1(B_155)
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_643,plain,(
    ! [A_150,B_151,C_152] :
      ( k2_relset_1(A_150,B_151,C_152) = k2_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_646,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_643])).

tff(c_648,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_646])).

tff(c_667,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_56])).

tff(c_679,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_667])).

tff(c_688,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_64,c_439,c_449,c_679])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_440,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_58])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_437,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_14])).

tff(c_600,plain,(
    ! [A_147,B_148] :
      ( r2_hidden(A_147,k1_relat_1(B_148))
      | k11_relat_1(B_148,A_147) = '#skF_4'
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_26])).

tff(c_615,plain,(
    ! [A_147] :
      ( r2_hidden(A_147,'#skF_4')
      | k11_relat_1('#skF_4',A_147) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_600])).

tff(c_622,plain,(
    ! [A_149] :
      ( r2_hidden(A_149,'#skF_4')
      | k11_relat_1('#skF_4',A_149) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_615])).

tff(c_44,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_634,plain,(
    ! [A_149] :
      ( ~ r1_tarski('#skF_4',A_149)
      | k11_relat_1('#skF_4',A_149) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_622,c_44])).

tff(c_642,plain,(
    ! [A_149] : k11_relat_1('#skF_4',A_149) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_634])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( k11_relat_1(B_21,A_20) != k1_xboole_0
      | ~ r2_hidden(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_581,plain,(
    ! [B_144,A_145] :
      ( k11_relat_1(B_144,A_145) != '#skF_4'
      | ~ r2_hidden(A_145,k1_relat_1(B_144))
      | ~ v1_relat_1(B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_28])).

tff(c_584,plain,(
    ! [A_145] :
      ( k11_relat_1('#skF_4',A_145) != '#skF_4'
      | ~ r2_hidden(A_145,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_581])).

tff(c_590,plain,(
    ! [A_145] :
      ( k11_relat_1('#skF_4',A_145) != '#skF_4'
      | ~ r2_hidden(A_145,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_584])).

tff(c_651,plain,(
    ! [A_145] : ~ r2_hidden(A_145,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_590])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    ! [D_43,C_42,A_40,B_41] :
      ( r2_hidden(k1_funct_1(D_43,C_42),k2_relset_1(A_40,B_41,D_43))
      | k1_xboole_0 = B_41
      | ~ r2_hidden(C_42,A_40)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(D_43,A_40,B_41)
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_824,plain,(
    ! [D_172,C_173,A_174,B_175] :
      ( r2_hidden(k1_funct_1(D_172,C_173),k2_relset_1(A_174,B_175,D_172))
      | B_175 = '#skF_4'
      | ~ r2_hidden(C_173,A_174)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_2(D_172,A_174,B_175)
      | ~ v1_funct_1(D_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_54])).

tff(c_832,plain,(
    ! [C_173] :
      ( r2_hidden(k1_funct_1('#skF_4',C_173),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_173,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_824])).

tff(c_836,plain,(
    ! [C_173] :
      ( r2_hidden(k1_funct_1('#skF_4',C_173),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_173,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_832])).

tff(c_838,plain,(
    ! [C_176] : ~ r2_hidden(C_176,k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_651,c_836])).

tff(c_849,plain,(
    ! [B_177] : r1_tarski(k1_tarski('#skF_2'),B_177) ),
    inference(resolution,[status(thm)],[c_6,c_838])).

tff(c_455,plain,(
    ! [B_119,A_120] :
      ( B_119 = A_120
      | ~ r1_tarski(B_119,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_460,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_437,c_455])).

tff(c_864,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_849,c_460])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_688,c_864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.82/1.43  
% 2.82/1.43  %Foreground sorts:
% 2.82/1.43  
% 2.82/1.43  
% 2.82/1.43  %Background operators:
% 2.82/1.43  
% 2.82/1.43  
% 2.82/1.43  %Foreground operators:
% 2.82/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.82/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.82/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.43  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.82/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.82/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.43  
% 3.15/1.45  tff(f_138, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.15/1.45  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.15/1.45  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.15/1.45  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.15/1.45  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.15/1.45  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.15/1.45  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.15/1.45  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.15/1.45  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.15/1.45  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.15/1.45  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.15/1.45  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.15/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.15/1.45  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.45  tff(f_100, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.15/1.45  tff(f_126, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.15/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.45  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.15/1.45  tff(c_109, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.15/1.45  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_109])).
% 3.15/1.45  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.15/1.45  tff(c_36, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.45  tff(c_120, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_113, c_36])).
% 3.15/1.45  tff(c_122, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_120])).
% 3.15/1.45  tff(c_163, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.15/1.45  tff(c_167, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_163])).
% 3.15/1.45  tff(c_195, plain, (![B_81, A_82]: (k7_relat_1(B_81, A_82)=B_81 | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.15/1.45  tff(c_198, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_167, c_195])).
% 3.15/1.45  tff(c_201, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_198])).
% 3.15/1.45  tff(c_24, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.15/1.45  tff(c_205, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_201, c_24])).
% 3.15/1.45  tff(c_209, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_205])).
% 3.15/1.45  tff(c_22, plain, (![A_15, B_17]: (k9_relat_1(A_15, k1_tarski(B_17))=k11_relat_1(A_15, B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.15/1.45  tff(c_230, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_209, c_22])).
% 3.15/1.45  tff(c_237, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_230])).
% 3.15/1.45  tff(c_26, plain, (![A_20, B_21]: (r2_hidden(A_20, k1_relat_1(B_21)) | k11_relat_1(B_21, A_20)=k1_xboole_0 | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.45  tff(c_373, plain, (![B_108, A_109]: (k1_tarski(k1_funct_1(B_108, A_109))=k11_relat_1(B_108, A_109) | ~r2_hidden(A_109, k1_relat_1(B_108)) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.15/1.45  tff(c_409, plain, (![B_116, A_117]: (k1_tarski(k1_funct_1(B_116, A_117))=k11_relat_1(B_116, A_117) | ~v1_funct_1(B_116) | k11_relat_1(B_116, A_117)=k1_xboole_0 | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_26, c_373])).
% 3.15/1.45  tff(c_283, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.15/1.45  tff(c_287, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_283])).
% 3.15/1.45  tff(c_56, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.15/1.45  tff(c_288, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_56])).
% 3.15/1.45  tff(c_418, plain, (k11_relat_1('#skF_4', '#skF_2')!=k2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_409, c_288])).
% 3.15/1.45  tff(c_430, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_113, c_237, c_64, c_237, c_418])).
% 3.15/1.45  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_430])).
% 3.15/1.45  tff(c_433, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_120])).
% 3.15/1.45  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.45  tff(c_439, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_433, c_433, c_34])).
% 3.15/1.45  tff(c_434, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_120])).
% 3.15/1.45  tff(c_449, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_433, c_434])).
% 3.15/1.45  tff(c_673, plain, (![B_155, A_156]: (k1_tarski(k1_funct_1(B_155, A_156))=k2_relat_1(B_155) | k1_tarski(A_156)!=k1_relat_1(B_155) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.15/1.45  tff(c_643, plain, (![A_150, B_151, C_152]: (k2_relset_1(A_150, B_151, C_152)=k2_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.15/1.45  tff(c_646, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_643])).
% 3.15/1.45  tff(c_648, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_449, c_646])).
% 3.15/1.45  tff(c_667, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_648, c_56])).
% 3.15/1.45  tff(c_679, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_673, c_667])).
% 3.15/1.45  tff(c_688, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_64, c_439, c_449, c_679])).
% 3.15/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.45  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.15/1.45  tff(c_440, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_433, c_58])).
% 3.15/1.45  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.45  tff(c_437, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_14])).
% 3.15/1.45  tff(c_600, plain, (![A_147, B_148]: (r2_hidden(A_147, k1_relat_1(B_148)) | k11_relat_1(B_148, A_147)='#skF_4' | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_26])).
% 3.15/1.45  tff(c_615, plain, (![A_147]: (r2_hidden(A_147, '#skF_4') | k11_relat_1('#skF_4', A_147)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_439, c_600])).
% 3.15/1.45  tff(c_622, plain, (![A_149]: (r2_hidden(A_149, '#skF_4') | k11_relat_1('#skF_4', A_149)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_615])).
% 3.15/1.45  tff(c_44, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.45  tff(c_634, plain, (![A_149]: (~r1_tarski('#skF_4', A_149) | k11_relat_1('#skF_4', A_149)='#skF_4')), inference(resolution, [status(thm)], [c_622, c_44])).
% 3.15/1.45  tff(c_642, plain, (![A_149]: (k11_relat_1('#skF_4', A_149)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_437, c_634])).
% 3.15/1.45  tff(c_28, plain, (![B_21, A_20]: (k11_relat_1(B_21, A_20)!=k1_xboole_0 | ~r2_hidden(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.45  tff(c_581, plain, (![B_144, A_145]: (k11_relat_1(B_144, A_145)!='#skF_4' | ~r2_hidden(A_145, k1_relat_1(B_144)) | ~v1_relat_1(B_144))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_28])).
% 3.15/1.45  tff(c_584, plain, (![A_145]: (k11_relat_1('#skF_4', A_145)!='#skF_4' | ~r2_hidden(A_145, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_439, c_581])).
% 3.15/1.45  tff(c_590, plain, (![A_145]: (k11_relat_1('#skF_4', A_145)!='#skF_4' | ~r2_hidden(A_145, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_584])).
% 3.15/1.45  tff(c_651, plain, (![A_145]: (~r2_hidden(A_145, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_642, c_590])).
% 3.15/1.45  tff(c_62, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.15/1.45  tff(c_54, plain, (![D_43, C_42, A_40, B_41]: (r2_hidden(k1_funct_1(D_43, C_42), k2_relset_1(A_40, B_41, D_43)) | k1_xboole_0=B_41 | ~r2_hidden(C_42, A_40) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.15/1.45  tff(c_824, plain, (![D_172, C_173, A_174, B_175]: (r2_hidden(k1_funct_1(D_172, C_173), k2_relset_1(A_174, B_175, D_172)) | B_175='#skF_4' | ~r2_hidden(C_173, A_174) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_2(D_172, A_174, B_175) | ~v1_funct_1(D_172))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_54])).
% 3.15/1.45  tff(c_832, plain, (![C_173]: (r2_hidden(k1_funct_1('#skF_4', C_173), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_173, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_648, c_824])).
% 3.15/1.45  tff(c_836, plain, (![C_173]: (r2_hidden(k1_funct_1('#skF_4', C_173), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_173, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_832])).
% 3.15/1.45  tff(c_838, plain, (![C_176]: (~r2_hidden(C_176, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_440, c_651, c_836])).
% 3.15/1.45  tff(c_849, plain, (![B_177]: (r1_tarski(k1_tarski('#skF_2'), B_177))), inference(resolution, [status(thm)], [c_6, c_838])).
% 3.15/1.45  tff(c_455, plain, (![B_119, A_120]: (B_119=A_120 | ~r1_tarski(B_119, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.45  tff(c_460, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(resolution, [status(thm)], [c_437, c_455])).
% 3.15/1.45  tff(c_864, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_849, c_460])).
% 3.15/1.45  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_688, c_864])).
% 3.15/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.45  
% 3.15/1.45  Inference rules
% 3.15/1.45  ----------------------
% 3.15/1.45  #Ref     : 0
% 3.15/1.45  #Sup     : 172
% 3.15/1.45  #Fact    : 0
% 3.15/1.45  #Define  : 0
% 3.15/1.45  #Split   : 3
% 3.15/1.45  #Chain   : 0
% 3.15/1.45  #Close   : 0
% 3.15/1.45  
% 3.15/1.45  Ordering : KBO
% 3.15/1.45  
% 3.15/1.45  Simplification rules
% 3.15/1.45  ----------------------
% 3.15/1.45  #Subsume      : 14
% 3.15/1.45  #Demod        : 93
% 3.15/1.45  #Tautology    : 98
% 3.15/1.45  #SimpNegUnit  : 3
% 3.15/1.45  #BackRed      : 9
% 3.15/1.45  
% 3.15/1.45  #Partial instantiations: 0
% 3.15/1.45  #Strategies tried      : 1
% 3.15/1.45  
% 3.15/1.45  Timing (in seconds)
% 3.15/1.45  ----------------------
% 3.15/1.45  Preprocessing        : 0.34
% 3.15/1.45  Parsing              : 0.18
% 3.15/1.45  CNF conversion       : 0.02
% 3.15/1.45  Main loop            : 0.34
% 3.15/1.45  Inferencing          : 0.13
% 3.15/1.45  Reduction            : 0.10
% 3.15/1.45  Demodulation         : 0.07
% 3.15/1.45  BG Simplification    : 0.02
% 3.15/1.45  Subsumption          : 0.06
% 3.15/1.45  Abstraction          : 0.01
% 3.15/1.45  MUC search           : 0.00
% 3.15/1.45  Cooper               : 0.00
% 3.15/1.45  Total                : 0.72
% 3.15/1.45  Index Insertion      : 0.00
% 3.15/1.45  Index Deletion       : 0.00
% 3.15/1.45  Index Matching       : 0.00
% 3.15/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
