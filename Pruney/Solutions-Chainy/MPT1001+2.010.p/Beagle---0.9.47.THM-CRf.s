%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:56 EST 2020

% Result     : Theorem 5.40s
% Output     : CNFRefutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 390 expanded)
%              Number of leaves         :   33 ( 143 expanded)
%              Depth                    :   18
%              Number of atoms          :  156 ( 924 expanded)
%              Number of equality atoms :   62 ( 310 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_91,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_40,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_73,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_96,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_73])).

tff(c_18,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_69])).

tff(c_1763,plain,(
    ! [A_207,B_208,C_209] :
      ( m1_subset_1(k2_relset_1(A_207,B_208,C_209),k1_zfmisc_1(B_208))
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1773,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_1763])).

tff(c_1777,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1773])).

tff(c_76,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,k2_relat_1(B_42))
      | k10_relat_1(B_42,k1_tarski(A_41)) = k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1813,plain,(
    ! [A_219,A_220,B_221] :
      ( r2_hidden(A_219,A_220)
      | ~ m1_subset_1(k2_relat_1(B_221),k1_zfmisc_1(A_220))
      | k10_relat_1(B_221,k1_tarski(A_219)) = k1_xboole_0
      | ~ v1_relat_1(B_221) ) ),
    inference(resolution,[status(thm)],[c_76,c_14])).

tff(c_1815,plain,(
    ! [A_219] :
      ( r2_hidden(A_219,'#skF_4')
      | k10_relat_1('#skF_5',k1_tarski(A_219)) = k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1777,c_1813])).

tff(c_1818,plain,(
    ! [A_219] :
      ( r2_hidden(A_219,'#skF_4')
      | k10_relat_1('#skF_5',k1_tarski(A_219)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1815])).

tff(c_1739,plain,(
    ! [A_205,B_206] :
      ( r2_hidden('#skF_1'(A_205,B_206),B_206)
      | r2_hidden('#skF_2'(A_205,B_206),A_205)
      | B_206 = A_205 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k1_tarski(A_16)) != k1_xboole_0
      | ~ r2_hidden(A_16,k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2085,plain,(
    ! [B_251,A_252] :
      ( k10_relat_1(B_251,k1_tarski('#skF_1'(A_252,k2_relat_1(B_251)))) != k1_xboole_0
      | ~ v1_relat_1(B_251)
      | r2_hidden('#skF_2'(A_252,k2_relat_1(B_251)),A_252)
      | k2_relat_1(B_251) = A_252 ) ),
    inference(resolution,[status(thm)],[c_1739,c_22])).

tff(c_2088,plain,(
    ! [A_252] :
      ( ~ v1_relat_1('#skF_5')
      | r2_hidden('#skF_2'(A_252,k2_relat_1('#skF_5')),A_252)
      | k2_relat_1('#skF_5') = A_252
      | r2_hidden('#skF_1'(A_252,k2_relat_1('#skF_5')),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1818,c_2085])).

tff(c_2091,plain,(
    ! [A_252] :
      ( r2_hidden('#skF_2'(A_252,k2_relat_1('#skF_5')),A_252)
      | k2_relat_1('#skF_5') = A_252
      | r2_hidden('#skF_1'(A_252,k2_relat_1('#skF_5')),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2088])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,k2_relat_1(B_17))
      | k10_relat_1(B_17,k1_tarski(A_16)) = k1_xboole_0
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_85,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),B_46)
      | ~ r2_hidden('#skF_2'(A_45,B_46),B_46)
      | B_46 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2209,plain,(
    ! [A_269,B_270] :
      ( r2_hidden('#skF_1'(A_269,k2_relat_1(B_270)),k2_relat_1(B_270))
      | k2_relat_1(B_270) = A_269
      | k10_relat_1(B_270,k1_tarski('#skF_2'(A_269,k2_relat_1(B_270)))) = k1_xboole_0
      | ~ v1_relat_1(B_270) ) ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_3028,plain,(
    ! [B_346,A_347] :
      ( k10_relat_1(B_346,k1_tarski('#skF_1'(A_347,k2_relat_1(B_346)))) != k1_xboole_0
      | k2_relat_1(B_346) = A_347
      | k10_relat_1(B_346,k1_tarski('#skF_2'(A_347,k2_relat_1(B_346)))) = k1_xboole_0
      | ~ v1_relat_1(B_346) ) ),
    inference(resolution,[status(thm)],[c_2209,c_22])).

tff(c_1778,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( k8_relset_1(A_210,B_211,C_212,D_213) = k10_relat_1(C_212,D_213)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1785,plain,(
    ! [D_213] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_213) = k10_relat_1('#skF_5',D_213) ),
    inference(resolution,[status(thm)],[c_30,c_1778])).

tff(c_46,plain,(
    ! [D_30] :
      ( k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski(D_30)) != k1_xboole_0
      | ~ r2_hidden(D_30,'#skF_4')
      | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1715,plain,(
    ! [D_30] :
      ( k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski(D_30)) != k1_xboole_0
      | ~ r2_hidden(D_30,'#skF_4')
      | k2_relat_1('#skF_5') = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_46])).

tff(c_1716,plain,(
    ! [D_30] :
      ( k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski(D_30)) != k1_xboole_0
      | ~ r2_hidden(D_30,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1715])).

tff(c_1791,plain,(
    ! [D_30] :
      ( k10_relat_1('#skF_5',k1_tarski(D_30)) != k1_xboole_0
      | ~ r2_hidden(D_30,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1785,c_1716])).

tff(c_3050,plain,(
    ! [A_347] :
      ( ~ r2_hidden('#skF_2'(A_347,k2_relat_1('#skF_5')),'#skF_4')
      | k10_relat_1('#skF_5',k1_tarski('#skF_1'(A_347,k2_relat_1('#skF_5')))) != k1_xboole_0
      | k2_relat_1('#skF_5') = A_347
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3028,c_1791])).

tff(c_3083,plain,(
    ! [A_348] :
      ( ~ r2_hidden('#skF_2'(A_348,k2_relat_1('#skF_5')),'#skF_4')
      | k10_relat_1('#skF_5',k1_tarski('#skF_1'(A_348,k2_relat_1('#skF_5')))) != k1_xboole_0
      | k2_relat_1('#skF_5') = A_348 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3050])).

tff(c_3088,plain,(
    ! [A_349] :
      ( ~ r2_hidden('#skF_2'(A_349,k2_relat_1('#skF_5')),'#skF_4')
      | k2_relat_1('#skF_5') = A_349
      | r2_hidden('#skF_1'(A_349,k2_relat_1('#skF_5')),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1818,c_3083])).

tff(c_3112,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | r2_hidden('#skF_1'('#skF_4',k2_relat_1('#skF_5')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2091,c_3088])).

tff(c_3134,plain,(
    r2_hidden('#skF_1'('#skF_4',k2_relat_1('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_96,c_3112])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3144,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4',k2_relat_1('#skF_5')),k2_relat_1('#skF_5'))
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3134,c_2])).

tff(c_3152,plain,(
    ~ r2_hidden('#skF_2'('#skF_4',k2_relat_1('#skF_5')),k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_3144])).

tff(c_3165,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_2'('#skF_4',k2_relat_1('#skF_5')))) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_3152])).

tff(c_3175,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_2'('#skF_4',k2_relat_1('#skF_5')))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3165])).

tff(c_3227,plain,(
    ~ r2_hidden('#skF_2'('#skF_4',k2_relat_1('#skF_5')),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3175,c_1791])).

tff(c_3252,plain,
    ( ~ r2_hidden('#skF_1'('#skF_4',k2_relat_1('#skF_5')),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_3227])).

tff(c_3267,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3134,c_3252])).

tff(c_3269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_3267])).

tff(c_3270,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_3425,plain,(
    ! [A_379,B_380,C_381,D_382] :
      ( k8_relset_1(A_379,B_380,C_381,D_382) = k10_relat_1(C_381,D_382)
      | ~ m1_subset_1(C_381,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3433,plain,(
    ! [D_383] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_383) = k10_relat_1('#skF_5',D_383) ),
    inference(resolution,[status(thm)],[c_30,c_3425])).

tff(c_3271,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3272,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_3278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3272])).

tff(c_3279,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3439,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3433,c_3279])).

tff(c_3349,plain,(
    ! [A_366,B_367,C_368] :
      ( k2_relset_1(A_366,B_367,C_368) = k2_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3352,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_3349])).

tff(c_3354,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3352])).

tff(c_3361,plain,(
    ! [A_16] :
      ( k10_relat_1('#skF_5',k1_tarski(A_16)) != k1_xboole_0
      | ~ r2_hidden(A_16,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3354,c_22])).

tff(c_3367,plain,(
    ! [A_16] :
      ( k10_relat_1('#skF_5',k1_tarski(A_16)) != k1_xboole_0
      | ~ r2_hidden(A_16,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3361])).

tff(c_3451,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3439,c_3367])).

tff(c_3463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3270,c_3451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.40/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.04  
% 5.40/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.05  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.40/2.05  
% 5.40/2.05  %Foreground sorts:
% 5.40/2.05  
% 5.40/2.05  
% 5.40/2.05  %Background operators:
% 5.40/2.05  
% 5.40/2.05  
% 5.40/2.05  %Foreground operators:
% 5.40/2.05  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.40/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.40/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.40/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.40/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.40/2.05  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.40/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.40/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.40/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.40/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.40/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.40/2.05  tff('#skF_6', type, '#skF_6': $i).
% 5.40/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.40/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.40/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.40/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.40/2.05  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.40/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.40/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.40/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.40/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.40/2.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.40/2.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.40/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.40/2.05  
% 5.47/2.06  tff(f_86, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_2)).
% 5.47/2.06  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.47/2.06  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.47/2.06  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.47/2.06  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.47/2.06  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 5.47/2.06  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.47/2.06  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.47/2.06  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.47/2.06  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.47/2.06  tff(c_91, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.47/2.06  tff(c_95, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_91])).
% 5.47/2.06  tff(c_40, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.47/2.06  tff(c_73, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_40])).
% 5.47/2.06  tff(c_96, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_73])).
% 5.47/2.06  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.47/2.06  tff(c_66, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.47/2.06  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_66])).
% 5.47/2.06  tff(c_72, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_69])).
% 5.47/2.06  tff(c_1763, plain, (![A_207, B_208, C_209]: (m1_subset_1(k2_relset_1(A_207, B_208, C_209), k1_zfmisc_1(B_208)) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.47/2.06  tff(c_1773, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_95, c_1763])).
% 5.47/2.06  tff(c_1777, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1773])).
% 5.47/2.06  tff(c_76, plain, (![A_41, B_42]: (r2_hidden(A_41, k2_relat_1(B_42)) | k10_relat_1(B_42, k1_tarski(A_41))=k1_xboole_0 | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.47/2.06  tff(c_14, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.47/2.06  tff(c_1813, plain, (![A_219, A_220, B_221]: (r2_hidden(A_219, A_220) | ~m1_subset_1(k2_relat_1(B_221), k1_zfmisc_1(A_220)) | k10_relat_1(B_221, k1_tarski(A_219))=k1_xboole_0 | ~v1_relat_1(B_221))), inference(resolution, [status(thm)], [c_76, c_14])).
% 5.47/2.06  tff(c_1815, plain, (![A_219]: (r2_hidden(A_219, '#skF_4') | k10_relat_1('#skF_5', k1_tarski(A_219))=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1777, c_1813])).
% 5.47/2.06  tff(c_1818, plain, (![A_219]: (r2_hidden(A_219, '#skF_4') | k10_relat_1('#skF_5', k1_tarski(A_219))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1815])).
% 5.47/2.06  tff(c_1739, plain, (![A_205, B_206]: (r2_hidden('#skF_1'(A_205, B_206), B_206) | r2_hidden('#skF_2'(A_205, B_206), A_205) | B_206=A_205)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.06  tff(c_22, plain, (![B_17, A_16]: (k10_relat_1(B_17, k1_tarski(A_16))!=k1_xboole_0 | ~r2_hidden(A_16, k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.47/2.06  tff(c_2085, plain, (![B_251, A_252]: (k10_relat_1(B_251, k1_tarski('#skF_1'(A_252, k2_relat_1(B_251))))!=k1_xboole_0 | ~v1_relat_1(B_251) | r2_hidden('#skF_2'(A_252, k2_relat_1(B_251)), A_252) | k2_relat_1(B_251)=A_252)), inference(resolution, [status(thm)], [c_1739, c_22])).
% 5.47/2.06  tff(c_2088, plain, (![A_252]: (~v1_relat_1('#skF_5') | r2_hidden('#skF_2'(A_252, k2_relat_1('#skF_5')), A_252) | k2_relat_1('#skF_5')=A_252 | r2_hidden('#skF_1'(A_252, k2_relat_1('#skF_5')), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1818, c_2085])).
% 5.47/2.06  tff(c_2091, plain, (![A_252]: (r2_hidden('#skF_2'(A_252, k2_relat_1('#skF_5')), A_252) | k2_relat_1('#skF_5')=A_252 | r2_hidden('#skF_1'(A_252, k2_relat_1('#skF_5')), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2088])).
% 5.47/2.06  tff(c_20, plain, (![A_16, B_17]: (r2_hidden(A_16, k2_relat_1(B_17)) | k10_relat_1(B_17, k1_tarski(A_16))=k1_xboole_0 | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.47/2.06  tff(c_85, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), B_46) | ~r2_hidden('#skF_2'(A_45, B_46), B_46) | B_46=A_45)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.06  tff(c_2209, plain, (![A_269, B_270]: (r2_hidden('#skF_1'(A_269, k2_relat_1(B_270)), k2_relat_1(B_270)) | k2_relat_1(B_270)=A_269 | k10_relat_1(B_270, k1_tarski('#skF_2'(A_269, k2_relat_1(B_270))))=k1_xboole_0 | ~v1_relat_1(B_270))), inference(resolution, [status(thm)], [c_20, c_85])).
% 5.47/2.06  tff(c_3028, plain, (![B_346, A_347]: (k10_relat_1(B_346, k1_tarski('#skF_1'(A_347, k2_relat_1(B_346))))!=k1_xboole_0 | k2_relat_1(B_346)=A_347 | k10_relat_1(B_346, k1_tarski('#skF_2'(A_347, k2_relat_1(B_346))))=k1_xboole_0 | ~v1_relat_1(B_346))), inference(resolution, [status(thm)], [c_2209, c_22])).
% 5.47/2.06  tff(c_1778, plain, (![A_210, B_211, C_212, D_213]: (k8_relset_1(A_210, B_211, C_212, D_213)=k10_relat_1(C_212, D_213) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.47/2.06  tff(c_1785, plain, (![D_213]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_213)=k10_relat_1('#skF_5', D_213))), inference(resolution, [status(thm)], [c_30, c_1778])).
% 5.47/2.06  tff(c_46, plain, (![D_30]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski(D_30))!=k1_xboole_0 | ~r2_hidden(D_30, '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.47/2.06  tff(c_1715, plain, (![D_30]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski(D_30))!=k1_xboole_0 | ~r2_hidden(D_30, '#skF_4') | k2_relat_1('#skF_5')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_46])).
% 5.47/2.06  tff(c_1716, plain, (![D_30]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski(D_30))!=k1_xboole_0 | ~r2_hidden(D_30, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_96, c_1715])).
% 5.47/2.06  tff(c_1791, plain, (![D_30]: (k10_relat_1('#skF_5', k1_tarski(D_30))!=k1_xboole_0 | ~r2_hidden(D_30, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1785, c_1716])).
% 5.47/2.06  tff(c_3050, plain, (![A_347]: (~r2_hidden('#skF_2'(A_347, k2_relat_1('#skF_5')), '#skF_4') | k10_relat_1('#skF_5', k1_tarski('#skF_1'(A_347, k2_relat_1('#skF_5'))))!=k1_xboole_0 | k2_relat_1('#skF_5')=A_347 | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3028, c_1791])).
% 5.47/2.06  tff(c_3083, plain, (![A_348]: (~r2_hidden('#skF_2'(A_348, k2_relat_1('#skF_5')), '#skF_4') | k10_relat_1('#skF_5', k1_tarski('#skF_1'(A_348, k2_relat_1('#skF_5'))))!=k1_xboole_0 | k2_relat_1('#skF_5')=A_348)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3050])).
% 5.47/2.06  tff(c_3088, plain, (![A_349]: (~r2_hidden('#skF_2'(A_349, k2_relat_1('#skF_5')), '#skF_4') | k2_relat_1('#skF_5')=A_349 | r2_hidden('#skF_1'(A_349, k2_relat_1('#skF_5')), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1818, c_3083])).
% 5.47/2.06  tff(c_3112, plain, (k2_relat_1('#skF_5')='#skF_4' | r2_hidden('#skF_1'('#skF_4', k2_relat_1('#skF_5')), '#skF_4')), inference(resolution, [status(thm)], [c_2091, c_3088])).
% 5.47/2.06  tff(c_3134, plain, (r2_hidden('#skF_1'('#skF_4', k2_relat_1('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_96, c_96, c_3112])).
% 5.47/2.06  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.06  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.47/2.06  tff(c_3144, plain, (~r2_hidden('#skF_2'('#skF_4', k2_relat_1('#skF_5')), k2_relat_1('#skF_5')) | k2_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_3134, c_2])).
% 5.47/2.06  tff(c_3152, plain, (~r2_hidden('#skF_2'('#skF_4', k2_relat_1('#skF_5')), k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_96, c_3144])).
% 5.47/2.06  tff(c_3165, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_2'('#skF_4', k2_relat_1('#skF_5'))))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_3152])).
% 5.47/2.06  tff(c_3175, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_2'('#skF_4', k2_relat_1('#skF_5'))))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3165])).
% 5.47/2.06  tff(c_3227, plain, (~r2_hidden('#skF_2'('#skF_4', k2_relat_1('#skF_5')), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3175, c_1791])).
% 5.47/2.06  tff(c_3252, plain, (~r2_hidden('#skF_1'('#skF_4', k2_relat_1('#skF_5')), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_6, c_3227])).
% 5.47/2.06  tff(c_3267, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3134, c_3252])).
% 5.47/2.06  tff(c_3269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_3267])).
% 5.47/2.06  tff(c_3270, plain, (r2_hidden('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 5.47/2.06  tff(c_3425, plain, (![A_379, B_380, C_381, D_382]: (k8_relset_1(A_379, B_380, C_381, D_382)=k10_relat_1(C_381, D_382) | ~m1_subset_1(C_381, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.47/2.06  tff(c_3433, plain, (![D_383]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_383)=k10_relat_1('#skF_5', D_383))), inference(resolution, [status(thm)], [c_30, c_3425])).
% 5.47/2.06  tff(c_3271, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 5.47/2.06  tff(c_36, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.47/2.06  tff(c_3272, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 5.47/2.06  tff(c_3278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3271, c_3272])).
% 5.47/2.06  tff(c_3279, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 5.47/2.06  tff(c_3439, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3433, c_3279])).
% 5.47/2.06  tff(c_3349, plain, (![A_366, B_367, C_368]: (k2_relset_1(A_366, B_367, C_368)=k2_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.47/2.06  tff(c_3352, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_3349])).
% 5.47/2.06  tff(c_3354, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_3352])).
% 5.47/2.06  tff(c_3361, plain, (![A_16]: (k10_relat_1('#skF_5', k1_tarski(A_16))!=k1_xboole_0 | ~r2_hidden(A_16, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3354, c_22])).
% 5.47/2.06  tff(c_3367, plain, (![A_16]: (k10_relat_1('#skF_5', k1_tarski(A_16))!=k1_xboole_0 | ~r2_hidden(A_16, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3361])).
% 5.47/2.06  tff(c_3451, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3439, c_3367])).
% 5.47/2.06  tff(c_3463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3270, c_3451])).
% 5.47/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.47/2.06  
% 5.47/2.06  Inference rules
% 5.47/2.06  ----------------------
% 5.47/2.06  #Ref     : 0
% 5.47/2.06  #Sup     : 679
% 5.47/2.06  #Fact    : 0
% 5.47/2.06  #Define  : 0
% 5.47/2.06  #Split   : 12
% 5.47/2.06  #Chain   : 0
% 5.47/2.06  #Close   : 0
% 5.47/2.06  
% 5.47/2.06  Ordering : KBO
% 5.47/2.06  
% 5.47/2.06  Simplification rules
% 5.47/2.06  ----------------------
% 5.47/2.06  #Subsume      : 239
% 5.47/2.06  #Demod        : 120
% 5.47/2.06  #Tautology    : 137
% 5.47/2.06  #SimpNegUnit  : 89
% 5.47/2.06  #BackRed      : 3
% 5.47/2.06  
% 5.47/2.06  #Partial instantiations: 0
% 5.47/2.06  #Strategies tried      : 1
% 5.47/2.06  
% 5.47/2.06  Timing (in seconds)
% 5.47/2.06  ----------------------
% 5.47/2.07  Preprocessing        : 0.33
% 5.47/2.07  Parsing              : 0.18
% 5.47/2.07  CNF conversion       : 0.02
% 5.47/2.07  Main loop            : 0.91
% 5.47/2.07  Inferencing          : 0.34
% 5.47/2.07  Reduction            : 0.25
% 5.47/2.07  Demodulation         : 0.16
% 5.47/2.07  BG Simplification    : 0.03
% 5.47/2.07  Subsumption          : 0.22
% 5.47/2.07  Abstraction          : 0.05
% 5.47/2.07  MUC search           : 0.00
% 5.47/2.07  Cooper               : 0.00
% 5.47/2.07  Total                : 1.28
% 5.47/2.07  Index Insertion      : 0.00
% 5.47/2.07  Index Deletion       : 0.00
% 5.47/2.07  Index Matching       : 0.00
% 5.47/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
