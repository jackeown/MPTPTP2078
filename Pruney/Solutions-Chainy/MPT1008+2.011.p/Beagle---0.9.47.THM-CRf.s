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
% DateTime   : Thu Dec  3 10:14:27 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 395 expanded)
%              Number of leaves         :   51 ( 151 expanded)
%              Depth                    :   19
%              Number of atoms          :  199 ( 814 expanded)
%              Number of equality atoms :   91 ( 336 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_79,axiom,
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

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_156,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_164,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_156])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,(
    ! [A_28] :
      ( k2_relat_1(A_28) != k1_xboole_0
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_172,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_164,c_40])).

tff(c_188,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_189,plain,(
    ! [C_81,A_82,B_83] :
      ( v4_relat_1(C_81,A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_197,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_189])).

tff(c_226,plain,(
    ! [B_92,A_93] :
      ( k7_relat_1(B_92,A_93) = B_92
      | ~ v4_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_229,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_197,c_226])).

tff(c_235,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_229])).

tff(c_254,plain,(
    ! [B_98,A_99] :
      ( k2_relat_1(k7_relat_1(B_98,A_99)) = k9_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_263,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_254])).

tff(c_270,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_263])).

tff(c_26,plain,(
    ! [A_19,B_21] :
      ( k9_relat_1(A_19,k1_tarski(B_21)) = k11_relat_1(A_19,B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_295,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_26])).

tff(c_302,plain,(
    k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_295])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,k1_relat_1(B_25))
      | k11_relat_1(B_25,A_24) = k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_424,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_432,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_424])).

tff(c_76,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_442,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_76])).

tff(c_731,plain,(
    ! [B_179,A_180] :
      ( k2_relat_1(k7_relat_1(B_179,k1_tarski(A_180))) = k1_tarski(k1_funct_1(B_179,A_180))
      | ~ r2_hidden(A_180,k1_relat_1(B_179))
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_750,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_4')) = k2_relat_1('#skF_6')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_731])).

tff(c_758,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_4')) = k2_relat_1('#skF_6')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_84,c_750])).

tff(c_759,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_758])).

tff(c_764,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_759])).

tff(c_767,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_302,c_764])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_767])).

tff(c_770,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_779,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_770,c_38])).

tff(c_771,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_788,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_771])).

tff(c_1067,plain,(
    ! [B_233,A_234] :
      ( k1_tarski(k1_funct_1(B_233,A_234)) = k2_relat_1(B_233)
      | k1_tarski(A_234) != k1_relat_1(B_233)
      | ~ v1_funct_1(B_233)
      | ~ v1_relat_1(B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_777,plain,(
    ! [A_15] : m1_subset_1('#skF_6',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_22])).

tff(c_990,plain,(
    ! [A_222,B_223,C_224] :
      ( k2_relset_1(A_222,B_223,C_224) = k2_relat_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_994,plain,(
    ! [A_222,B_223] : k2_relset_1(A_222,B_223,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_777,c_990])).

tff(c_996,plain,(
    ! [A_222,B_223] : k2_relset_1(A_222,B_223,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_994])).

tff(c_997,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_76])).

tff(c_1073,plain,
    ( k2_relat_1('#skF_6') != '#skF_6'
    | k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_997])).

tff(c_1082,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_84,c_779,c_788,c_1073])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_781,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_78])).

tff(c_82,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_74,plain,(
    ! [B_58,A_57,C_59] :
      ( k1_xboole_0 = B_58
      | k1_relset_1(A_57,B_58,C_59) = A_57
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1320,plain,(
    ! [B_281,A_282,C_283] :
      ( B_281 = '#skF_6'
      | k1_relset_1(A_282,B_281,C_283) = A_282
      | ~ v1_funct_2(C_283,A_282,B_281)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_282,B_281))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_74])).

tff(c_1333,plain,(
    ! [B_287,A_288] :
      ( B_287 = '#skF_6'
      | k1_relset_1(A_288,B_287,'#skF_6') = A_288
      | ~ v1_funct_2('#skF_6',A_288,B_287) ) ),
    inference(resolution,[status(thm)],[c_777,c_1320])).

tff(c_1342,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_1333])).

tff(c_1349,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_781,c_1342])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1474,plain,(
    ! [D_307,A_308,B_309,C_310] :
      ( r2_hidden(k4_tarski(D_307,'#skF_3'(A_308,B_309,C_310,D_307)),C_310)
      | ~ r2_hidden(D_307,B_309)
      | k1_relset_1(B_309,A_308,C_310) != B_309
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(B_309,A_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_876,plain,(
    ! [C_201,A_202,B_203] :
      ( v4_relat_1(C_201,A_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_881,plain,(
    ! [A_202] : v4_relat_1('#skF_6',A_202) ),
    inference(resolution,[status(thm)],[c_777,c_876])).

tff(c_892,plain,(
    ! [B_207,A_208] :
      ( k7_relat_1(B_207,A_208) = B_207
      | ~ v4_relat_1(B_207,A_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_895,plain,(
    ! [A_202] :
      ( k7_relat_1('#skF_6',A_202) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_881,c_892])).

tff(c_899,plain,(
    ! [A_209] : k7_relat_1('#skF_6',A_209) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_895])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_904,plain,(
    ! [A_209] :
      ( k9_relat_1('#skF_6',A_209) = k2_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_28])).

tff(c_911,plain,(
    ! [A_210] : k9_relat_1('#skF_6',A_210) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_788,c_904])).

tff(c_917,plain,(
    ! [B_21] :
      ( k11_relat_1('#skF_6',B_21) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_26])).

tff(c_926,plain,(
    ! [B_21] : k11_relat_1('#skF_6',B_21) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_917])).

tff(c_32,plain,(
    ! [B_25,A_24] :
      ( k11_relat_1(B_25,A_24) != k1_xboole_0
      | ~ r2_hidden(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_968,plain,(
    ! [B_219,A_220] :
      ( k11_relat_1(B_219,A_220) != '#skF_6'
      | ~ r2_hidden(A_220,k1_relat_1(B_219))
      | ~ v1_relat_1(B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_32])).

tff(c_974,plain,(
    ! [A_220] :
      ( k11_relat_1('#skF_6',A_220) != '#skF_6'
      | ~ r2_hidden(A_220,'#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_968])).

tff(c_981,plain,(
    ! [A_220] : ~ r2_hidden(A_220,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_926,c_974])).

tff(c_1486,plain,(
    ! [D_307,B_309,A_308] :
      ( ~ r2_hidden(D_307,B_309)
      | k1_relset_1(B_309,A_308,'#skF_6') != B_309
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_309,A_308))) ) ),
    inference(resolution,[status(thm)],[c_1474,c_981])).

tff(c_1504,plain,(
    ! [D_311,B_312,A_313] :
      ( ~ r2_hidden(D_311,B_312)
      | k1_relset_1(B_312,A_313,'#skF_6') != B_312 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_1486])).

tff(c_1523,plain,(
    ! [A_314,A_315,B_316] :
      ( k1_relset_1(A_314,A_315,'#skF_6') != A_314
      | r1_tarski(A_314,B_316) ) ),
    inference(resolution,[status(thm)],[c_6,c_1504])).

tff(c_1531,plain,(
    ! [B_317] : r1_tarski(k1_tarski('#skF_4'),B_317) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_1523])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_126,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_773,plain,(
    ! [A_8] :
      ( A_8 = '#skF_6'
      | ~ r1_tarski(A_8,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_770,c_135])).

tff(c_1561,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1531,c_773])).

tff(c_1577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1082,c_1561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:55:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.62  
% 3.55/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.88/1.62  
% 3.88/1.62  %Foreground sorts:
% 3.88/1.62  
% 3.88/1.62  
% 3.88/1.62  %Background operators:
% 3.88/1.62  
% 3.88/1.62  
% 3.88/1.62  %Foreground operators:
% 3.88/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.88/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.88/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.88/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.88/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.88/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.88/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.88/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.88/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.62  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.88/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.88/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.88/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.88/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.88/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.88/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.88/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.88/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.88/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.88/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.88/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.88/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.62  
% 3.88/1.64  tff(f_164, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.88/1.64  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.88/1.64  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.88/1.64  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.88/1.64  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.88/1.64  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.88/1.64  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.88/1.64  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.88/1.64  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.88/1.64  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 3.88/1.64  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.88/1.64  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.88/1.64  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.88/1.64  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.88/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.88/1.64  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 3.88/1.64  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.88/1.64  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/1.64  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.88/1.64  tff(c_156, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.88/1.64  tff(c_164, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_156])).
% 3.88/1.64  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.88/1.64  tff(c_40, plain, (![A_28]: (k2_relat_1(A_28)!=k1_xboole_0 | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.88/1.64  tff(c_172, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_164, c_40])).
% 3.88/1.64  tff(c_188, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_172])).
% 3.88/1.64  tff(c_189, plain, (![C_81, A_82, B_83]: (v4_relat_1(C_81, A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.88/1.64  tff(c_197, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_189])).
% 3.88/1.64  tff(c_226, plain, (![B_92, A_93]: (k7_relat_1(B_92, A_93)=B_92 | ~v4_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.88/1.64  tff(c_229, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_197, c_226])).
% 3.88/1.64  tff(c_235, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_229])).
% 3.88/1.64  tff(c_254, plain, (![B_98, A_99]: (k2_relat_1(k7_relat_1(B_98, A_99))=k9_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.88/1.64  tff(c_263, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_235, c_254])).
% 3.88/1.64  tff(c_270, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_263])).
% 3.88/1.64  tff(c_26, plain, (![A_19, B_21]: (k9_relat_1(A_19, k1_tarski(B_21))=k11_relat_1(A_19, B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.88/1.64  tff(c_295, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_270, c_26])).
% 3.88/1.64  tff(c_302, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_295])).
% 3.88/1.64  tff(c_30, plain, (![A_24, B_25]: (r2_hidden(A_24, k1_relat_1(B_25)) | k11_relat_1(B_25, A_24)=k1_xboole_0 | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.88/1.64  tff(c_424, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.88/1.64  tff(c_432, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_424])).
% 3.88/1.64  tff(c_76, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.88/1.64  tff(c_442, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_76])).
% 3.88/1.64  tff(c_731, plain, (![B_179, A_180]: (k2_relat_1(k7_relat_1(B_179, k1_tarski(A_180)))=k1_tarski(k1_funct_1(B_179, A_180)) | ~r2_hidden(A_180, k1_relat_1(B_179)) | ~v1_funct_1(B_179) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.88/1.64  tff(c_750, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))=k2_relat_1('#skF_6') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_235, c_731])).
% 3.88/1.64  tff(c_758, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))=k2_relat_1('#skF_6') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_84, c_750])).
% 3.88/1.64  tff(c_759, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_442, c_758])).
% 3.88/1.64  tff(c_764, plain, (k11_relat_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_759])).
% 3.88/1.64  tff(c_767, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_164, c_302, c_764])).
% 3.88/1.64  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_767])).
% 3.88/1.64  tff(c_770, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_172])).
% 3.88/1.64  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.88/1.64  tff(c_779, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_770, c_770, c_38])).
% 3.88/1.64  tff(c_771, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_172])).
% 3.88/1.64  tff(c_788, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_770, c_771])).
% 3.88/1.64  tff(c_1067, plain, (![B_233, A_234]: (k1_tarski(k1_funct_1(B_233, A_234))=k2_relat_1(B_233) | k1_tarski(A_234)!=k1_relat_1(B_233) | ~v1_funct_1(B_233) | ~v1_relat_1(B_233))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.88/1.64  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.88/1.64  tff(c_777, plain, (![A_15]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_22])).
% 3.88/1.64  tff(c_990, plain, (![A_222, B_223, C_224]: (k2_relset_1(A_222, B_223, C_224)=k2_relat_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.88/1.64  tff(c_994, plain, (![A_222, B_223]: (k2_relset_1(A_222, B_223, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_777, c_990])).
% 3.88/1.64  tff(c_996, plain, (![A_222, B_223]: (k2_relset_1(A_222, B_223, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_994])).
% 3.88/1.64  tff(c_997, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_996, c_76])).
% 3.88/1.64  tff(c_1073, plain, (k2_relat_1('#skF_6')!='#skF_6' | k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1067, c_997])).
% 3.88/1.64  tff(c_1082, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_84, c_779, c_788, c_1073])).
% 3.88/1.64  tff(c_78, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.88/1.64  tff(c_781, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_770, c_78])).
% 3.88/1.64  tff(c_82, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.88/1.64  tff(c_74, plain, (![B_58, A_57, C_59]: (k1_xboole_0=B_58 | k1_relset_1(A_57, B_58, C_59)=A_57 | ~v1_funct_2(C_59, A_57, B_58) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.88/1.64  tff(c_1320, plain, (![B_281, A_282, C_283]: (B_281='#skF_6' | k1_relset_1(A_282, B_281, C_283)=A_282 | ~v1_funct_2(C_283, A_282, B_281) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_282, B_281))))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_74])).
% 3.88/1.64  tff(c_1333, plain, (![B_287, A_288]: (B_287='#skF_6' | k1_relset_1(A_288, B_287, '#skF_6')=A_288 | ~v1_funct_2('#skF_6', A_288, B_287))), inference(resolution, [status(thm)], [c_777, c_1320])).
% 3.88/1.64  tff(c_1342, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_82, c_1333])).
% 3.88/1.64  tff(c_1349, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_781, c_1342])).
% 3.88/1.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.64  tff(c_1474, plain, (![D_307, A_308, B_309, C_310]: (r2_hidden(k4_tarski(D_307, '#skF_3'(A_308, B_309, C_310, D_307)), C_310) | ~r2_hidden(D_307, B_309) | k1_relset_1(B_309, A_308, C_310)!=B_309 | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(B_309, A_308))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.88/1.64  tff(c_876, plain, (![C_201, A_202, B_203]: (v4_relat_1(C_201, A_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.88/1.64  tff(c_881, plain, (![A_202]: (v4_relat_1('#skF_6', A_202))), inference(resolution, [status(thm)], [c_777, c_876])).
% 3.88/1.64  tff(c_892, plain, (![B_207, A_208]: (k7_relat_1(B_207, A_208)=B_207 | ~v4_relat_1(B_207, A_208) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.88/1.64  tff(c_895, plain, (![A_202]: (k7_relat_1('#skF_6', A_202)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_881, c_892])).
% 3.88/1.64  tff(c_899, plain, (![A_209]: (k7_relat_1('#skF_6', A_209)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_895])).
% 3.88/1.64  tff(c_28, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.88/1.64  tff(c_904, plain, (![A_209]: (k9_relat_1('#skF_6', A_209)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_899, c_28])).
% 3.88/1.64  tff(c_911, plain, (![A_210]: (k9_relat_1('#skF_6', A_210)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_788, c_904])).
% 3.88/1.64  tff(c_917, plain, (![B_21]: (k11_relat_1('#skF_6', B_21)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_911, c_26])).
% 3.88/1.64  tff(c_926, plain, (![B_21]: (k11_relat_1('#skF_6', B_21)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_917])).
% 3.88/1.64  tff(c_32, plain, (![B_25, A_24]: (k11_relat_1(B_25, A_24)!=k1_xboole_0 | ~r2_hidden(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.88/1.64  tff(c_968, plain, (![B_219, A_220]: (k11_relat_1(B_219, A_220)!='#skF_6' | ~r2_hidden(A_220, k1_relat_1(B_219)) | ~v1_relat_1(B_219))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_32])).
% 3.88/1.64  tff(c_974, plain, (![A_220]: (k11_relat_1('#skF_6', A_220)!='#skF_6' | ~r2_hidden(A_220, '#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_779, c_968])).
% 3.88/1.64  tff(c_981, plain, (![A_220]: (~r2_hidden(A_220, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_926, c_974])).
% 3.88/1.64  tff(c_1486, plain, (![D_307, B_309, A_308]: (~r2_hidden(D_307, B_309) | k1_relset_1(B_309, A_308, '#skF_6')!=B_309 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_309, A_308))))), inference(resolution, [status(thm)], [c_1474, c_981])).
% 3.88/1.64  tff(c_1504, plain, (![D_311, B_312, A_313]: (~r2_hidden(D_311, B_312) | k1_relset_1(B_312, A_313, '#skF_6')!=B_312)), inference(demodulation, [status(thm), theory('equality')], [c_777, c_1486])).
% 3.88/1.64  tff(c_1523, plain, (![A_314, A_315, B_316]: (k1_relset_1(A_314, A_315, '#skF_6')!=A_314 | r1_tarski(A_314, B_316))), inference(resolution, [status(thm)], [c_6, c_1504])).
% 3.88/1.64  tff(c_1531, plain, (![B_317]: (r1_tarski(k1_tarski('#skF_4'), B_317))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_1523])).
% 3.88/1.64  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.88/1.64  tff(c_126, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.88/1.64  tff(c_135, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_126])).
% 3.88/1.64  tff(c_773, plain, (![A_8]: (A_8='#skF_6' | ~r1_tarski(A_8, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_770, c_770, c_135])).
% 3.88/1.64  tff(c_1561, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_1531, c_773])).
% 3.88/1.64  tff(c_1577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1082, c_1561])).
% 3.88/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.64  
% 3.88/1.64  Inference rules
% 3.88/1.64  ----------------------
% 3.88/1.64  #Ref     : 0
% 3.88/1.64  #Sup     : 304
% 3.88/1.64  #Fact    : 0
% 3.88/1.64  #Define  : 0
% 3.88/1.64  #Split   : 2
% 3.88/1.64  #Chain   : 0
% 3.88/1.64  #Close   : 0
% 3.88/1.64  
% 3.88/1.64  Ordering : KBO
% 3.88/1.64  
% 3.88/1.64  Simplification rules
% 3.88/1.64  ----------------------
% 3.88/1.64  #Subsume      : 22
% 3.88/1.64  #Demod        : 199
% 3.88/1.64  #Tautology    : 167
% 3.88/1.64  #SimpNegUnit  : 7
% 3.88/1.64  #BackRed      : 14
% 3.88/1.64  
% 3.88/1.64  #Partial instantiations: 0
% 3.88/1.64  #Strategies tried      : 1
% 3.88/1.64  
% 3.88/1.64  Timing (in seconds)
% 3.88/1.64  ----------------------
% 3.88/1.64  Preprocessing        : 0.38
% 3.88/1.64  Parsing              : 0.20
% 3.88/1.64  CNF conversion       : 0.03
% 3.88/1.64  Main loop            : 0.49
% 3.88/1.64  Inferencing          : 0.18
% 3.88/1.64  Reduction            : 0.15
% 3.88/1.64  Demodulation         : 0.10
% 3.88/1.64  BG Simplification    : 0.03
% 3.88/1.64  Subsumption          : 0.09
% 3.88/1.64  Abstraction          : 0.02
% 3.88/1.64  MUC search           : 0.00
% 3.88/1.64  Cooper               : 0.00
% 3.88/1.64  Total                : 0.91
% 3.88/1.64  Index Insertion      : 0.00
% 3.88/1.64  Index Deletion       : 0.00
% 3.88/1.64  Index Matching       : 0.00
% 3.88/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
