%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:29 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 310 expanded)
%              Number of leaves         :   47 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  162 ( 632 expanded)
%              Number of equality atoms :   70 ( 250 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_135,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_91,axiom,(
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

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_109,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_117,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_109])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_126,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_117,c_36])).

tff(c_160,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_246,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_254,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_246])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_265,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_254,c_32])).

tff(c_268,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_265])).

tff(c_38,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_290,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),k1_tarski('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_38])).

tff(c_294,plain,(
    r1_tarski(k1_relat_1('#skF_6'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_290])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( k1_tarski(B_16) = A_15
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_303,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_294,c_22])).

tff(c_308,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_303])).

tff(c_529,plain,(
    ! [B_126,A_127] :
      ( k1_tarski(k1_funct_1(B_126,A_127)) = k2_relat_1(B_126)
      | k1_tarski(A_127) != k1_relat_1(B_126)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_314,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_74])).

tff(c_394,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_402,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_314,c_394])).

tff(c_70,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_313,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_70])).

tff(c_411,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_313])).

tff(c_535,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_411])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_78,c_308,c_535])).

tff(c_547,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_548,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_562,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_548])).

tff(c_884,plain,(
    ! [B_189,A_190] :
      ( k1_tarski(k1_funct_1(B_189,A_190)) = k2_relat_1(B_189)
      | k1_tarski(A_190) != k1_relat_1(B_189)
      | ~ v1_funct_1(B_189)
      | ~ v1_relat_1(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_554,plain,(
    ! [A_17] : m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_28])).

tff(c_747,plain,(
    ! [A_170,B_171,C_172] :
      ( k2_relset_1(A_170,B_171,C_172) = k2_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_752,plain,(
    ! [A_170,B_171] : k2_relset_1(A_170,B_171,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_554,c_747])).

tff(c_753,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_70])).

tff(c_890,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_753])).

tff(c_900,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_78,c_562,c_890])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_556,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_72])).

tff(c_76,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,(
    ! [B_53,A_52,C_54] :
      ( k1_xboole_0 = B_53
      | k1_relset_1(A_52,B_53,C_54) = A_52
      | ~ v1_funct_2(C_54,A_52,B_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1366,plain,(
    ! [B_230,A_231,C_232] :
      ( B_230 = '#skF_6'
      | k1_relset_1(A_231,B_230,C_232) = A_231
      | ~ v1_funct_2(C_232,A_231,B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_68])).

tff(c_1372,plain,(
    ! [B_233,A_234] :
      ( B_233 = '#skF_6'
      | k1_relset_1(A_234,B_233,'#skF_6') = A_234
      | ~ v1_funct_2('#skF_6',A_234,B_233) ) ),
    inference(resolution,[status(thm)],[c_554,c_1366])).

tff(c_1384,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1372])).

tff(c_1391,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_556,c_1384])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_555,plain,(
    ! [A_8] : r1_tarski('#skF_6',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_14])).

tff(c_1556,plain,(
    ! [D_254,A_255,B_256,C_257] :
      ( r2_hidden(k4_tarski(D_254,'#skF_3'(A_255,B_256,C_257,D_254)),C_257)
      | ~ r2_hidden(D_254,B_256)
      | k1_relset_1(B_256,A_255,C_257) != B_256
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(B_256,A_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    ! [B_29,A_28] :
      ( ~ r1_tarski(B_29,A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1674,plain,(
    ! [C_268,D_269,A_270,B_271] :
      ( ~ r1_tarski(C_268,k4_tarski(D_269,'#skF_3'(A_270,B_271,C_268,D_269)))
      | ~ r2_hidden(D_269,B_271)
      | k1_relset_1(B_271,A_270,C_268) != B_271
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(B_271,A_270))) ) ),
    inference(resolution,[status(thm)],[c_1556,c_42])).

tff(c_1686,plain,(
    ! [D_269,B_271,A_270] :
      ( ~ r2_hidden(D_269,B_271)
      | k1_relset_1(B_271,A_270,'#skF_6') != B_271
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_271,A_270))) ) ),
    inference(resolution,[status(thm)],[c_555,c_1674])).

tff(c_1692,plain,(
    ! [D_272,B_273,A_274] :
      ( ~ r2_hidden(D_272,B_273)
      | k1_relset_1(B_273,A_274,'#skF_6') != B_273 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_1686])).

tff(c_1711,plain,(
    ! [A_275,A_276,B_277] :
      ( k1_relset_1(A_275,A_276,'#skF_6') != A_275
      | r1_tarski(A_275,B_277) ) ),
    inference(resolution,[status(thm)],[c_6,c_1692])).

tff(c_1722,plain,(
    ! [B_278] : r1_tarski(k1_tarski('#skF_4'),B_278) ),
    inference(superposition,[status(thm),theory(equality)],[c_1391,c_1711])).

tff(c_127,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_127])).

tff(c_549,plain,(
    ! [A_8] :
      ( A_8 = '#skF_6'
      | ~ r1_tarski(A_8,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_136])).

tff(c_1772,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1722,c_549])).

tff(c_1798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_900,c_1772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:35:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.60  
% 3.61/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.61/1.61  
% 3.61/1.61  %Foreground sorts:
% 3.61/1.61  
% 3.61/1.61  
% 3.61/1.61  %Background operators:
% 3.61/1.61  
% 3.61/1.61  
% 3.61/1.61  %Foreground operators:
% 3.61/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.61/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.61/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.61/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.61/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.61/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.61/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.61/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.61/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.61/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.61/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.61/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.61/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.61/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.61/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.61  
% 3.61/1.62  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.61/1.62  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.61/1.62  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.61/1.62  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.61/1.62  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.61/1.62  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.61/1.62  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.61/1.62  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.61/1.62  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.61/1.62  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.61/1.62  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.61/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.61/1.62  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.61/1.62  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 3.61/1.62  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.61/1.62  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.61/1.62  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.61/1.62  tff(c_109, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.61/1.62  tff(c_117, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_109])).
% 3.61/1.62  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.61/1.62  tff(c_36, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.61/1.62  tff(c_126, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_117, c_36])).
% 3.61/1.62  tff(c_160, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126])).
% 3.61/1.62  tff(c_246, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.61/1.62  tff(c_254, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_74, c_246])).
% 3.61/1.62  tff(c_32, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.61/1.62  tff(c_265, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_254, c_32])).
% 3.61/1.62  tff(c_268, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_265])).
% 3.61/1.62  tff(c_38, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.62  tff(c_290, plain, (r1_tarski(k1_relat_1('#skF_6'), k1_tarski('#skF_4')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_268, c_38])).
% 3.61/1.62  tff(c_294, plain, (r1_tarski(k1_relat_1('#skF_6'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_290])).
% 3.61/1.62  tff(c_22, plain, (![B_16, A_15]: (k1_tarski(B_16)=A_15 | k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.61/1.62  tff(c_303, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_294, c_22])).
% 3.61/1.62  tff(c_308, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_160, c_303])).
% 3.61/1.62  tff(c_529, plain, (![B_126, A_127]: (k1_tarski(k1_funct_1(B_126, A_127))=k2_relat_1(B_126) | k1_tarski(A_127)!=k1_relat_1(B_126) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.62  tff(c_314, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_74])).
% 3.61/1.62  tff(c_394, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.61/1.62  tff(c_402, plain, (k2_relset_1(k1_relat_1('#skF_6'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_314, c_394])).
% 3.61/1.62  tff(c_70, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.61/1.62  tff(c_313, plain, (k2_relset_1(k1_relat_1('#skF_6'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_70])).
% 3.61/1.62  tff(c_411, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_313])).
% 3.61/1.62  tff(c_535, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_529, c_411])).
% 3.61/1.62  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_78, c_308, c_535])).
% 3.61/1.62  tff(c_547, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_126])).
% 3.61/1.62  tff(c_548, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 3.61/1.62  tff(c_562, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_547, c_548])).
% 3.61/1.62  tff(c_884, plain, (![B_189, A_190]: (k1_tarski(k1_funct_1(B_189, A_190))=k2_relat_1(B_189) | k1_tarski(A_190)!=k1_relat_1(B_189) | ~v1_funct_1(B_189) | ~v1_relat_1(B_189))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.62  tff(c_28, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.61/1.62  tff(c_554, plain, (![A_17]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_28])).
% 3.61/1.62  tff(c_747, plain, (![A_170, B_171, C_172]: (k2_relset_1(A_170, B_171, C_172)=k2_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.61/1.62  tff(c_752, plain, (![A_170, B_171]: (k2_relset_1(A_170, B_171, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_554, c_747])).
% 3.61/1.62  tff(c_753, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_70])).
% 3.61/1.62  tff(c_890, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_884, c_753])).
% 3.61/1.62  tff(c_900, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_78, c_562, c_890])).
% 3.61/1.62  tff(c_72, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.61/1.62  tff(c_556, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_547, c_72])).
% 3.61/1.62  tff(c_76, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.61/1.62  tff(c_68, plain, (![B_53, A_52, C_54]: (k1_xboole_0=B_53 | k1_relset_1(A_52, B_53, C_54)=A_52 | ~v1_funct_2(C_54, A_52, B_53) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.61/1.62  tff(c_1366, plain, (![B_230, A_231, C_232]: (B_230='#skF_6' | k1_relset_1(A_231, B_230, C_232)=A_231 | ~v1_funct_2(C_232, A_231, B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_68])).
% 3.61/1.62  tff(c_1372, plain, (![B_233, A_234]: (B_233='#skF_6' | k1_relset_1(A_234, B_233, '#skF_6')=A_234 | ~v1_funct_2('#skF_6', A_234, B_233))), inference(resolution, [status(thm)], [c_554, c_1366])).
% 3.61/1.62  tff(c_1384, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1372])).
% 3.61/1.62  tff(c_1391, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_556, c_1384])).
% 3.61/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.62  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.61/1.62  tff(c_555, plain, (![A_8]: (r1_tarski('#skF_6', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_14])).
% 3.61/1.62  tff(c_1556, plain, (![D_254, A_255, B_256, C_257]: (r2_hidden(k4_tarski(D_254, '#skF_3'(A_255, B_256, C_257, D_254)), C_257) | ~r2_hidden(D_254, B_256) | k1_relset_1(B_256, A_255, C_257)!=B_256 | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(B_256, A_255))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.61/1.62  tff(c_42, plain, (![B_29, A_28]: (~r1_tarski(B_29, A_28) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.61/1.62  tff(c_1674, plain, (![C_268, D_269, A_270, B_271]: (~r1_tarski(C_268, k4_tarski(D_269, '#skF_3'(A_270, B_271, C_268, D_269))) | ~r2_hidden(D_269, B_271) | k1_relset_1(B_271, A_270, C_268)!=B_271 | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(B_271, A_270))))), inference(resolution, [status(thm)], [c_1556, c_42])).
% 3.61/1.62  tff(c_1686, plain, (![D_269, B_271, A_270]: (~r2_hidden(D_269, B_271) | k1_relset_1(B_271, A_270, '#skF_6')!=B_271 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_271, A_270))))), inference(resolution, [status(thm)], [c_555, c_1674])).
% 3.61/1.62  tff(c_1692, plain, (![D_272, B_273, A_274]: (~r2_hidden(D_272, B_273) | k1_relset_1(B_273, A_274, '#skF_6')!=B_273)), inference(demodulation, [status(thm), theory('equality')], [c_554, c_1686])).
% 3.61/1.62  tff(c_1711, plain, (![A_275, A_276, B_277]: (k1_relset_1(A_275, A_276, '#skF_6')!=A_275 | r1_tarski(A_275, B_277))), inference(resolution, [status(thm)], [c_6, c_1692])).
% 3.61/1.62  tff(c_1722, plain, (![B_278]: (r1_tarski(k1_tarski('#skF_4'), B_278))), inference(superposition, [status(thm), theory('equality')], [c_1391, c_1711])).
% 3.61/1.62  tff(c_127, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.61/1.62  tff(c_136, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_127])).
% 3.61/1.62  tff(c_549, plain, (![A_8]: (A_8='#skF_6' | ~r1_tarski(A_8, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_547, c_136])).
% 3.61/1.62  tff(c_1772, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_1722, c_549])).
% 3.61/1.62  tff(c_1798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_900, c_1772])).
% 3.61/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.62  
% 3.61/1.62  Inference rules
% 3.61/1.62  ----------------------
% 3.61/1.62  #Ref     : 0
% 3.61/1.62  #Sup     : 370
% 3.61/1.62  #Fact    : 2
% 3.61/1.62  #Define  : 0
% 3.61/1.62  #Split   : 2
% 3.61/1.62  #Chain   : 0
% 3.61/1.62  #Close   : 0
% 3.61/1.62  
% 3.61/1.62  Ordering : KBO
% 3.61/1.62  
% 3.61/1.62  Simplification rules
% 3.61/1.62  ----------------------
% 3.61/1.62  #Subsume      : 97
% 3.61/1.62  #Demod        : 181
% 3.61/1.62  #Tautology    : 135
% 3.61/1.62  #SimpNegUnit  : 8
% 3.61/1.62  #BackRed      : 17
% 3.61/1.62  
% 3.61/1.62  #Partial instantiations: 0
% 3.61/1.62  #Strategies tried      : 1
% 3.61/1.62  
% 3.61/1.62  Timing (in seconds)
% 3.61/1.62  ----------------------
% 3.61/1.63  Preprocessing        : 0.35
% 3.61/1.63  Parsing              : 0.18
% 3.61/1.63  CNF conversion       : 0.03
% 3.61/1.63  Main loop            : 0.51
% 3.61/1.63  Inferencing          : 0.19
% 3.61/1.63  Reduction            : 0.15
% 3.61/1.63  Demodulation         : 0.11
% 3.61/1.63  BG Simplification    : 0.03
% 3.61/1.63  Subsumption          : 0.10
% 3.61/1.63  Abstraction          : 0.02
% 3.61/1.63  MUC search           : 0.00
% 3.61/1.63  Cooper               : 0.00
% 3.61/1.63  Total                : 0.90
% 3.61/1.63  Index Insertion      : 0.00
% 3.61/1.63  Index Deletion       : 0.00
% 3.61/1.63  Index Matching       : 0.00
% 3.61/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
