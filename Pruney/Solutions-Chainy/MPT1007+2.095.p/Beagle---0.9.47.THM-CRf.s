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
% DateTime   : Thu Dec  3 10:14:23 EST 2020

% Result     : Theorem 22.10s
% Output     : CNFRefutation 22.10s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 229 expanded)
%              Number of leaves         :   44 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  140 ( 542 expanded)
%              Number of equality atoms :   60 ( 177 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_94,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_68,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_383,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_393,plain,(
    k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_383])).

tff(c_1098,plain,(
    ! [B_260,A_261,C_262] :
      ( k1_xboole_0 = B_260
      | k1_relset_1(A_261,B_260,C_262) = A_261
      | ~ v1_funct_2(C_262,A_261,B_260)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_261,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1110,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_tarski('#skF_2')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1098])).

tff(c_1114,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_393,c_1110])).

tff(c_1115,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1114])).

tff(c_1128,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_68])).

tff(c_1127,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_66])).

tff(c_42,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_1'(A_48),A_48)
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_198,plain,(
    ! [C_98,A_99,B_100] :
      ( r2_hidden(C_98,A_99)
      | ~ r2_hidden(C_98,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_202,plain,(
    ! [A_101,A_102] :
      ( r2_hidden('#skF_1'(A_101),A_102)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(A_102))
      | k1_xboole_0 = A_101 ) ),
    inference(resolution,[status(thm)],[c_42,c_198])).

tff(c_36,plain,(
    ! [A_42,B_43,C_44] :
      ( r2_hidden(k1_mcart_1(A_42),B_43)
      | ~ r2_hidden(A_42,k2_zfmisc_1(B_43,C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_464,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden(k1_mcart_1('#skF_1'(A_149)),B_150)
      | ~ m1_subset_1(A_149,k1_zfmisc_1(k2_zfmisc_1(B_150,C_151)))
      | k1_xboole_0 = A_149 ) ),
    inference(resolution,[status(thm)],[c_202,c_36])).

tff(c_472,plain,
    ( r2_hidden(k1_mcart_1('#skF_1'('#skF_4')),k1_tarski('#skF_2'))
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_464])).

tff(c_473,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(A_80,B_81)
      | k4_xboole_0(k1_tarski(A_80),B_81) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_153,plain,(
    ! [A_83] :
      ( r2_hidden(A_83,k1_xboole_0)
      | k1_tarski(A_83) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_137])).

tff(c_30,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_159,plain,(
    ! [A_83] :
      ( ~ r1_tarski(k1_xboole_0,A_83)
      | k1_tarski(A_83) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_30])).

tff(c_163,plain,(
    ! [A_83] : k1_tarski(A_83) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_159])).

tff(c_493,plain,(
    ! [A_83] : k1_tarski(A_83) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_163])).

tff(c_502,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_64])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_500,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_473,c_28])).

tff(c_519,plain,(
    k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_393])).

tff(c_58,plain,(
    ! [B_63,A_62,C_64] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_62,B_63,C_64) = A_62
      | ~ v1_funct_2(C_64,A_62,B_63)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_696,plain,(
    ! [B_196,A_197,C_198] :
      ( B_196 = '#skF_4'
      | k1_relset_1(A_197,B_196,C_198) = A_197
      | ~ v1_funct_2(C_198,A_197,B_196)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_58])).

tff(c_705,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_tarski('#skF_2')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_696])).

tff(c_709,plain,
    ( '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_519,c_705])).

tff(c_711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_502,c_709])).

tff(c_713,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_40,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_mcart_1(A_45) = B_46
      | ~ r2_hidden(A_45,k2_zfmisc_1(k1_tarski(B_46),C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_872,plain,(
    ! [A_230,B_231,C_232] :
      ( k1_mcart_1('#skF_1'(A_230)) = B_231
      | ~ m1_subset_1(A_230,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_231),C_232)))
      | k1_xboole_0 = A_230 ) ),
    inference(resolution,[status(thm)],[c_202,c_40])).

tff(c_878,plain,
    ( k1_mcart_1('#skF_1'('#skF_4')) = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_872])).

tff(c_881,plain,(
    k1_mcart_1('#skF_1'('#skF_4')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_878])).

tff(c_712,plain,(
    r2_hidden(k1_mcart_1('#skF_1'('#skF_4')),k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_888,plain,(
    r2_hidden('#skF_2',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_712])).

tff(c_1124,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_888])).

tff(c_1259,plain,(
    ! [D_274,C_275,B_276,A_277] :
      ( r2_hidden(k1_funct_1(D_274,C_275),B_276)
      | k1_xboole_0 = B_276
      | ~ r2_hidden(C_275,A_277)
      | ~ m1_subset_1(D_274,k1_zfmisc_1(k2_zfmisc_1(A_277,B_276)))
      | ~ v1_funct_2(D_274,A_277,B_276)
      | ~ v1_funct_1(D_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_93741,plain,(
    ! [D_1991,B_1992] :
      ( r2_hidden(k1_funct_1(D_1991,'#skF_2'),B_1992)
      | k1_xboole_0 = B_1992
      | ~ m1_subset_1(D_1991,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_1992)))
      | ~ v1_funct_2(D_1991,k1_relat_1('#skF_4'),B_1992)
      | ~ v1_funct_1(D_1991) ) ),
    inference(resolution,[status(thm)],[c_1124,c_1259])).

tff(c_93860,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1127,c_93741])).

tff(c_93867,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1128,c_93860])).

tff(c_93869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_93867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.10/13.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.10/13.64  
% 22.10/13.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.10/13.64  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_relset_1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 22.10/13.64  
% 22.10/13.64  %Foreground sorts:
% 22.10/13.64  
% 22.10/13.64  
% 22.10/13.64  %Background operators:
% 22.10/13.64  
% 22.10/13.64  
% 22.10/13.64  %Foreground operators:
% 22.10/13.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.10/13.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.10/13.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.10/13.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.10/13.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.10/13.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.10/13.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.10/13.64  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 22.10/13.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 22.10/13.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.10/13.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.10/13.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.10/13.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.10/13.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.10/13.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.10/13.64  tff('#skF_2', type, '#skF_2': $i).
% 22.10/13.64  tff('#skF_3', type, '#skF_3': $i).
% 22.10/13.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.10/13.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 22.10/13.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.10/13.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 22.10/13.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 22.10/13.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.10/13.64  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 22.10/13.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.10/13.64  tff('#skF_4', type, '#skF_4': $i).
% 22.10/13.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.10/13.64  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 22.10/13.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 22.10/13.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.10/13.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.10/13.64  
% 22.10/13.66  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 22.10/13.66  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 22.10/13.66  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 22.10/13.66  tff(f_94, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 22.10/13.66  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 22.10/13.66  tff(f_72, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 22.10/13.66  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 22.10/13.66  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 22.10/13.66  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 22.10/13.66  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 22.10/13.66  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 22.10/13.66  tff(f_78, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 22.10/13.66  tff(f_124, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 22.10/13.66  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.10/13.66  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.10/13.66  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.10/13.66  tff(c_68, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.10/13.66  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 22.10/13.66  tff(c_383, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.10/13.66  tff(c_393, plain, (k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_383])).
% 22.10/13.66  tff(c_1098, plain, (![B_260, A_261, C_262]: (k1_xboole_0=B_260 | k1_relset_1(A_261, B_260, C_262)=A_261 | ~v1_funct_2(C_262, A_261, B_260) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_261, B_260))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 22.10/13.66  tff(c_1110, plain, (k1_xboole_0='#skF_3' | k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_tarski('#skF_2') | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_66, c_1098])).
% 22.10/13.66  tff(c_1114, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_393, c_1110])).
% 22.10/13.66  tff(c_1115, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_1114])).
% 22.10/13.66  tff(c_1128, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_68])).
% 22.10/13.66  tff(c_1127, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_66])).
% 22.10/13.66  tff(c_42, plain, (![A_48]: (r2_hidden('#skF_1'(A_48), A_48) | k1_xboole_0=A_48)), inference(cnfTransformation, [status(thm)], [f_94])).
% 22.10/13.66  tff(c_198, plain, (![C_98, A_99, B_100]: (r2_hidden(C_98, A_99) | ~r2_hidden(C_98, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 22.10/13.66  tff(c_202, plain, (![A_101, A_102]: (r2_hidden('#skF_1'(A_101), A_102) | ~m1_subset_1(A_101, k1_zfmisc_1(A_102)) | k1_xboole_0=A_101)), inference(resolution, [status(thm)], [c_42, c_198])).
% 22.10/13.66  tff(c_36, plain, (![A_42, B_43, C_44]: (r2_hidden(k1_mcart_1(A_42), B_43) | ~r2_hidden(A_42, k2_zfmisc_1(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.10/13.66  tff(c_464, plain, (![A_149, B_150, C_151]: (r2_hidden(k1_mcart_1('#skF_1'(A_149)), B_150) | ~m1_subset_1(A_149, k1_zfmisc_1(k2_zfmisc_1(B_150, C_151))) | k1_xboole_0=A_149)), inference(resolution, [status(thm)], [c_202, c_36])).
% 22.10/13.66  tff(c_472, plain, (r2_hidden(k1_mcart_1('#skF_1'('#skF_4')), k1_tarski('#skF_2')) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_464])).
% 22.10/13.66  tff(c_473, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_472])).
% 22.10/13.66  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.10/13.66  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.10/13.66  tff(c_137, plain, (![A_80, B_81]: (r2_hidden(A_80, B_81) | k4_xboole_0(k1_tarski(A_80), B_81)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 22.10/13.66  tff(c_153, plain, (![A_83]: (r2_hidden(A_83, k1_xboole_0) | k1_tarski(A_83)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_137])).
% 22.10/13.66  tff(c_30, plain, (![B_38, A_37]: (~r1_tarski(B_38, A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.10/13.66  tff(c_159, plain, (![A_83]: (~r1_tarski(k1_xboole_0, A_83) | k1_tarski(A_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_30])).
% 22.10/13.66  tff(c_163, plain, (![A_83]: (k1_tarski(A_83)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_159])).
% 22.10/13.66  tff(c_493, plain, (![A_83]: (k1_tarski(A_83)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_163])).
% 22.10/13.66  tff(c_502, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_64])).
% 22.10/13.66  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.10/13.66  tff(c_500, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_473, c_28])).
% 22.10/13.66  tff(c_519, plain, (k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_500, c_393])).
% 22.10/13.66  tff(c_58, plain, (![B_63, A_62, C_64]: (k1_xboole_0=B_63 | k1_relset_1(A_62, B_63, C_64)=A_62 | ~v1_funct_2(C_64, A_62, B_63) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 22.10/13.66  tff(c_696, plain, (![B_196, A_197, C_198]: (B_196='#skF_4' | k1_relset_1(A_197, B_196, C_198)=A_197 | ~v1_funct_2(C_198, A_197, B_196) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_58])).
% 22.10/13.66  tff(c_705, plain, ('#skF_3'='#skF_4' | k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_tarski('#skF_2') | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_66, c_696])).
% 22.10/13.66  tff(c_709, plain, ('#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_519, c_705])).
% 22.10/13.66  tff(c_711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_502, c_709])).
% 22.10/13.66  tff(c_713, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_472])).
% 22.10/13.66  tff(c_40, plain, (![A_45, B_46, C_47]: (k1_mcart_1(A_45)=B_46 | ~r2_hidden(A_45, k2_zfmisc_1(k1_tarski(B_46), C_47)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 22.10/13.66  tff(c_872, plain, (![A_230, B_231, C_232]: (k1_mcart_1('#skF_1'(A_230))=B_231 | ~m1_subset_1(A_230, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_231), C_232))) | k1_xboole_0=A_230)), inference(resolution, [status(thm)], [c_202, c_40])).
% 22.10/13.66  tff(c_878, plain, (k1_mcart_1('#skF_1'('#skF_4'))='#skF_2' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_872])).
% 22.10/13.66  tff(c_881, plain, (k1_mcart_1('#skF_1'('#skF_4'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_713, c_878])).
% 22.10/13.66  tff(c_712, plain, (r2_hidden(k1_mcart_1('#skF_1'('#skF_4')), k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_472])).
% 22.10/13.66  tff(c_888, plain, (r2_hidden('#skF_2', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_881, c_712])).
% 22.10/13.66  tff(c_1124, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_888])).
% 22.10/13.66  tff(c_1259, plain, (![D_274, C_275, B_276, A_277]: (r2_hidden(k1_funct_1(D_274, C_275), B_276) | k1_xboole_0=B_276 | ~r2_hidden(C_275, A_277) | ~m1_subset_1(D_274, k1_zfmisc_1(k2_zfmisc_1(A_277, B_276))) | ~v1_funct_2(D_274, A_277, B_276) | ~v1_funct_1(D_274))), inference(cnfTransformation, [status(thm)], [f_124])).
% 22.10/13.66  tff(c_93741, plain, (![D_1991, B_1992]: (r2_hidden(k1_funct_1(D_1991, '#skF_2'), B_1992) | k1_xboole_0=B_1992 | ~m1_subset_1(D_1991, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_1992))) | ~v1_funct_2(D_1991, k1_relat_1('#skF_4'), B_1992) | ~v1_funct_1(D_1991))), inference(resolution, [status(thm)], [c_1124, c_1259])).
% 22.10/13.66  tff(c_93860, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1127, c_93741])).
% 22.10/13.66  tff(c_93867, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1128, c_93860])).
% 22.10/13.66  tff(c_93869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_93867])).
% 22.10/13.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.10/13.66  
% 22.10/13.66  Inference rules
% 22.10/13.66  ----------------------
% 22.10/13.66  #Ref     : 0
% 22.10/13.66  #Sup     : 24095
% 22.10/13.66  #Fact    : 10
% 22.10/13.66  #Define  : 0
% 22.10/13.66  #Split   : 15
% 22.10/13.66  #Chain   : 0
% 22.10/13.66  #Close   : 0
% 22.10/13.66  
% 22.10/13.66  Ordering : KBO
% 22.10/13.66  
% 22.10/13.66  Simplification rules
% 22.10/13.66  ----------------------
% 22.10/13.66  #Subsume      : 10722
% 22.10/13.66  #Demod        : 19809
% 22.10/13.66  #Tautology    : 9323
% 22.10/13.66  #SimpNegUnit  : 355
% 22.10/13.66  #BackRed      : 74
% 22.10/13.66  
% 22.10/13.66  #Partial instantiations: 0
% 22.10/13.66  #Strategies tried      : 1
% 22.10/13.66  
% 22.10/13.66  Timing (in seconds)
% 22.10/13.66  ----------------------
% 22.10/13.66  Preprocessing        : 0.35
% 22.10/13.66  Parsing              : 0.18
% 22.10/13.66  CNF conversion       : 0.02
% 22.10/13.66  Main loop            : 12.55
% 22.10/13.66  Inferencing          : 2.48
% 22.10/13.66  Reduction            : 4.32
% 22.10/13.66  Demodulation         : 2.82
% 22.10/13.66  BG Simplification    : 0.19
% 22.10/13.66  Subsumption          : 5.10
% 22.10/13.66  Abstraction          : 0.46
% 22.10/13.66  MUC search           : 0.00
% 22.10/13.66  Cooper               : 0.00
% 22.10/13.66  Total                : 12.94
% 22.10/13.66  Index Insertion      : 0.00
% 22.10/13.66  Index Deletion       : 0.00
% 22.10/13.66  Index Matching       : 0.00
% 22.10/13.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
