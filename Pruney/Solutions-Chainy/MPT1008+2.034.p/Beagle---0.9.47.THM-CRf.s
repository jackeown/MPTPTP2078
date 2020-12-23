%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:30 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 404 expanded)
%              Number of leaves         :   46 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 ( 861 expanded)
%              Number of equality atoms :   83 ( 364 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_117,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_101,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_101])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_24,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_113,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_105,c_24])).

tff(c_115,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_164,plain,(
    ! [A_81,B_82] :
      ( k9_relat_1(A_81,k1_tarski(B_82)) = k11_relat_1(A_81,B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_140,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_144,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_140])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = B_16
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_147,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_150,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_147])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_12])).

tff(c_158,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_154])).

tff(c_170,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_158])).

tff(c_179,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_170])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,k1_relat_1(B_14))
      | k11_relat_1(B_14,A_13) = k1_xboole_0
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_229,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_233,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_229])).

tff(c_50,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_234,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_50])).

tff(c_265,plain,(
    ! [B_113,A_114] :
      ( k2_relat_1(k7_relat_1(B_113,k1_tarski(A_114))) = k1_tarski(k1_funct_1(B_113,A_114))
      | ~ r2_hidden(A_114,k1_relat_1(B_113))
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_280,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_2')) = k2_relat_1('#skF_4')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_265])).

tff(c_288,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_2')) = k2_relat_1('#skF_4')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58,c_280])).

tff(c_289,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_288])).

tff(c_292,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_289])).

tff(c_295,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_179,c_292])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_295])).

tff(c_298,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_307,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_298,c_22])).

tff(c_26,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_105,c_26])).

tff(c_114,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_300,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_114])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_300])).

tff(c_326,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_327,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_375,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_327])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_361,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_326,c_20])).

tff(c_596,plain,(
    ! [B_173,A_174] :
      ( k1_tarski(k1_funct_1(B_173,A_174)) = k2_relat_1(B_173)
      | k1_tarski(A_174) != k1_relat_1(B_173)
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_556,plain,(
    ! [A_154,B_155,C_156] :
      ( k2_relset_1(A_154,B_155,C_156) = k2_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_559,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_556])).

tff(c_561,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_559])).

tff(c_562,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_50])).

tff(c_602,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_562])).

tff(c_611,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58,c_375,c_361,c_602])).

tff(c_42,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),A_33)
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_359,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),A_33)
      | A_33 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_42])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_363,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_52])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_360,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_2])).

tff(c_501,plain,(
    ! [A_144,B_145] :
      ( r2_hidden(A_144,k1_relat_1(B_145))
      | k11_relat_1(B_145,A_144) = '#skF_4'
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_14])).

tff(c_510,plain,(
    ! [A_144] :
      ( r2_hidden(A_144,'#skF_4')
      | k11_relat_1('#skF_4',A_144) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_501])).

tff(c_523,plain,(
    ! [A_151] :
      ( r2_hidden(A_151,'#skF_4')
      | k11_relat_1('#skF_4',A_151) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_510])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( ~ r1_tarski(B_23,A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_531,plain,(
    ! [A_151] :
      ( ~ r1_tarski('#skF_4',A_151)
      | k11_relat_1('#skF_4',A_151) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_523,c_32])).

tff(c_537,plain,(
    ! [A_151] : k11_relat_1('#skF_4',A_151) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_531])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k11_relat_1(B_14,A_13) != k1_xboole_0
      | ~ r2_hidden(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_482,plain,(
    ! [B_141,A_142] :
      ( k11_relat_1(B_141,A_142) != '#skF_4'
      | ~ r2_hidden(A_142,k1_relat_1(B_141))
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_16])).

tff(c_489,plain,(
    ! [A_142] :
      ( k11_relat_1('#skF_4',A_142) != '#skF_4'
      | ~ r2_hidden(A_142,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_482])).

tff(c_492,plain,(
    ! [A_142] :
      ( k11_relat_1('#skF_4',A_142) != '#skF_4'
      | ~ r2_hidden(A_142,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_489])).

tff(c_540,plain,(
    ! [A_142] : ~ r2_hidden(A_142,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_492])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    ! [D_54,C_53,A_51,B_52] :
      ( r2_hidden(k1_funct_1(D_54,C_53),k2_relset_1(A_51,B_52,D_54))
      | k1_xboole_0 = B_52
      | ~ r2_hidden(C_53,A_51)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(D_54,A_51,B_52)
      | ~ v1_funct_1(D_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_723,plain,(
    ! [D_193,C_194,A_195,B_196] :
      ( r2_hidden(k1_funct_1(D_193,C_194),k2_relset_1(A_195,B_196,D_193))
      | B_196 = '#skF_4'
      | ~ r2_hidden(C_194,A_195)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ v1_funct_2(D_193,A_195,B_196)
      | ~ v1_funct_1(D_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_48])).

tff(c_733,plain,(
    ! [C_194] :
      ( r2_hidden(k1_funct_1('#skF_4',C_194),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_194,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_723])).

tff(c_738,plain,(
    ! [C_194] :
      ( r2_hidden(k1_funct_1('#skF_4',C_194),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_194,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_733])).

tff(c_740,plain,(
    ! [C_197] : ~ r2_hidden(C_197,k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_540,c_738])).

tff(c_744,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_359,c_740])).

tff(c_748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:33:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.68/1.44  
% 2.68/1.44  %Foreground sorts:
% 2.68/1.44  
% 2.68/1.44  
% 2.68/1.44  %Background operators:
% 2.68/1.44  
% 2.68/1.44  
% 2.68/1.44  %Foreground operators:
% 2.68/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.68/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.68/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.68/1.44  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.68/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.68/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.68/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.68/1.44  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.68/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.44  
% 3.06/1.46  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.06/1.46  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.06/1.46  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.06/1.46  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.06/1.46  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.06/1.46  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.06/1.46  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.06/1.46  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.06/1.46  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.06/1.46  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 3.06/1.46  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.06/1.46  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.06/1.46  tff(f_117, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.06/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.06/1.46  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.06/1.46  tff(f_129, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.06/1.46  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.06/1.46  tff(c_101, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.06/1.46  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_101])).
% 3.06/1.46  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.06/1.46  tff(c_24, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.46  tff(c_113, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_105, c_24])).
% 3.06/1.46  tff(c_115, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_113])).
% 3.06/1.46  tff(c_164, plain, (![A_81, B_82]: (k9_relat_1(A_81, k1_tarski(B_82))=k11_relat_1(A_81, B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.06/1.46  tff(c_140, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.06/1.46  tff(c_144, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_140])).
% 3.06/1.46  tff(c_18, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=B_16 | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.46  tff(c_147, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_144, c_18])).
% 3.06/1.46  tff(c_150, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_147])).
% 3.06/1.46  tff(c_12, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.06/1.46  tff(c_154, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_150, c_12])).
% 3.06/1.46  tff(c_158, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_154])).
% 3.06/1.46  tff(c_170, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_164, c_158])).
% 3.06/1.46  tff(c_179, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_170])).
% 3.06/1.46  tff(c_14, plain, (![A_13, B_14]: (r2_hidden(A_13, k1_relat_1(B_14)) | k11_relat_1(B_14, A_13)=k1_xboole_0 | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.46  tff(c_229, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.06/1.46  tff(c_233, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_229])).
% 3.06/1.46  tff(c_50, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.06/1.46  tff(c_234, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_50])).
% 3.06/1.46  tff(c_265, plain, (![B_113, A_114]: (k2_relat_1(k7_relat_1(B_113, k1_tarski(A_114)))=k1_tarski(k1_funct_1(B_113, A_114)) | ~r2_hidden(A_114, k1_relat_1(B_113)) | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.06/1.46  tff(c_280, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))=k2_relat_1('#skF_4') | ~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_150, c_265])).
% 3.06/1.46  tff(c_288, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))=k2_relat_1('#skF_4') | ~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58, c_280])).
% 3.06/1.46  tff(c_289, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_234, c_288])).
% 3.06/1.46  tff(c_292, plain, (k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_289])).
% 3.06/1.46  tff(c_295, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_179, c_292])).
% 3.06/1.46  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_295])).
% 3.06/1.46  tff(c_298, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_113])).
% 3.06/1.46  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.06/1.46  tff(c_307, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_298, c_22])).
% 3.06/1.46  tff(c_26, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.46  tff(c_112, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_105, c_26])).
% 3.06/1.46  tff(c_114, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_112])).
% 3.06/1.46  tff(c_300, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_114])).
% 3.06/1.46  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_300])).
% 3.06/1.46  tff(c_326, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_112])).
% 3.06/1.46  tff(c_327, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_112])).
% 3.06/1.46  tff(c_375, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_327])).
% 3.06/1.46  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.06/1.46  tff(c_361, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_326, c_20])).
% 3.06/1.46  tff(c_596, plain, (![B_173, A_174]: (k1_tarski(k1_funct_1(B_173, A_174))=k2_relat_1(B_173) | k1_tarski(A_174)!=k1_relat_1(B_173) | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.06/1.46  tff(c_556, plain, (![A_154, B_155, C_156]: (k2_relset_1(A_154, B_155, C_156)=k2_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.06/1.46  tff(c_559, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_556])).
% 3.06/1.46  tff(c_561, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_361, c_559])).
% 3.06/1.46  tff(c_562, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_561, c_50])).
% 3.06/1.46  tff(c_602, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_596, c_562])).
% 3.06/1.46  tff(c_611, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58, c_375, c_361, c_602])).
% 3.06/1.46  tff(c_42, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), A_33) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.06/1.46  tff(c_359, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), A_33) | A_33='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_42])).
% 3.06/1.46  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.06/1.46  tff(c_363, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_52])).
% 3.06/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.46  tff(c_360, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_2])).
% 3.06/1.46  tff(c_501, plain, (![A_144, B_145]: (r2_hidden(A_144, k1_relat_1(B_145)) | k11_relat_1(B_145, A_144)='#skF_4' | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_14])).
% 3.06/1.46  tff(c_510, plain, (![A_144]: (r2_hidden(A_144, '#skF_4') | k11_relat_1('#skF_4', A_144)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_501])).
% 3.06/1.46  tff(c_523, plain, (![A_151]: (r2_hidden(A_151, '#skF_4') | k11_relat_1('#skF_4', A_151)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_510])).
% 3.06/1.46  tff(c_32, plain, (![B_23, A_22]: (~r1_tarski(B_23, A_22) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.46  tff(c_531, plain, (![A_151]: (~r1_tarski('#skF_4', A_151) | k11_relat_1('#skF_4', A_151)='#skF_4')), inference(resolution, [status(thm)], [c_523, c_32])).
% 3.06/1.46  tff(c_537, plain, (![A_151]: (k11_relat_1('#skF_4', A_151)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_531])).
% 3.06/1.46  tff(c_16, plain, (![B_14, A_13]: (k11_relat_1(B_14, A_13)!=k1_xboole_0 | ~r2_hidden(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.46  tff(c_482, plain, (![B_141, A_142]: (k11_relat_1(B_141, A_142)!='#skF_4' | ~r2_hidden(A_142, k1_relat_1(B_141)) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_16])).
% 3.06/1.46  tff(c_489, plain, (![A_142]: (k11_relat_1('#skF_4', A_142)!='#skF_4' | ~r2_hidden(A_142, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_375, c_482])).
% 3.06/1.46  tff(c_492, plain, (![A_142]: (k11_relat_1('#skF_4', A_142)!='#skF_4' | ~r2_hidden(A_142, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_489])).
% 3.06/1.46  tff(c_540, plain, (![A_142]: (~r2_hidden(A_142, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_537, c_492])).
% 3.06/1.46  tff(c_56, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.06/1.46  tff(c_48, plain, (![D_54, C_53, A_51, B_52]: (r2_hidden(k1_funct_1(D_54, C_53), k2_relset_1(A_51, B_52, D_54)) | k1_xboole_0=B_52 | ~r2_hidden(C_53, A_51) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(D_54, A_51, B_52) | ~v1_funct_1(D_54))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.06/1.46  tff(c_723, plain, (![D_193, C_194, A_195, B_196]: (r2_hidden(k1_funct_1(D_193, C_194), k2_relset_1(A_195, B_196, D_193)) | B_196='#skF_4' | ~r2_hidden(C_194, A_195) | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~v1_funct_2(D_193, A_195, B_196) | ~v1_funct_1(D_193))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_48])).
% 3.06/1.46  tff(c_733, plain, (![C_194]: (r2_hidden(k1_funct_1('#skF_4', C_194), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_194, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_561, c_723])).
% 3.06/1.46  tff(c_738, plain, (![C_194]: (r2_hidden(k1_funct_1('#skF_4', C_194), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_194, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_733])).
% 3.06/1.46  tff(c_740, plain, (![C_197]: (~r2_hidden(C_197, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_363, c_540, c_738])).
% 3.06/1.46  tff(c_744, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_359, c_740])).
% 3.06/1.46  tff(c_748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_611, c_744])).
% 3.06/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.46  
% 3.06/1.46  Inference rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Ref     : 0
% 3.06/1.46  #Sup     : 153
% 3.06/1.46  #Fact    : 0
% 3.06/1.46  #Define  : 0
% 3.06/1.46  #Split   : 4
% 3.06/1.46  #Chain   : 0
% 3.06/1.46  #Close   : 0
% 3.06/1.46  
% 3.06/1.46  Ordering : KBO
% 3.06/1.46  
% 3.06/1.46  Simplification rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Subsume      : 6
% 3.06/1.46  #Demod        : 123
% 3.06/1.46  #Tautology    : 95
% 3.06/1.46  #SimpNegUnit  : 7
% 3.06/1.46  #BackRed      : 28
% 3.06/1.46  
% 3.06/1.46  #Partial instantiations: 0
% 3.06/1.46  #Strategies tried      : 1
% 3.06/1.46  
% 3.06/1.46  Timing (in seconds)
% 3.06/1.46  ----------------------
% 3.06/1.46  Preprocessing        : 0.33
% 3.06/1.46  Parsing              : 0.18
% 3.06/1.46  CNF conversion       : 0.02
% 3.06/1.46  Main loop            : 0.32
% 3.06/1.46  Inferencing          : 0.12
% 3.06/1.46  Reduction            : 0.10
% 3.06/1.46  Demodulation         : 0.07
% 3.06/1.46  BG Simplification    : 0.02
% 3.06/1.46  Subsumption          : 0.05
% 3.06/1.46  Abstraction          : 0.02
% 3.06/1.46  MUC search           : 0.00
% 3.06/1.46  Cooper               : 0.00
% 3.06/1.46  Total                : 0.70
% 3.06/1.46  Index Insertion      : 0.00
% 3.06/1.46  Index Deletion       : 0.00
% 3.06/1.46  Index Matching       : 0.00
% 3.06/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
