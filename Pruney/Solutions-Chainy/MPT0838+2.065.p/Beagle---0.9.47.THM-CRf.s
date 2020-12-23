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
% DateTime   : Thu Dec  3 10:08:18 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 212 expanded)
%              Number of leaves         :   39 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 421 expanded)
%              Number of equality atoms :   33 ( 100 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_50,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ! [A_31,B_32] : v1_relat_1(k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_89,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_95,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_99,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_95])).

tff(c_36,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) = k1_xboole_0
      | k1_relat_1(A_33) != k1_xboole_0
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_106,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_36])).

tff(c_108,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_34,plain,(
    ! [A_33] :
      ( k1_relat_1(A_33) = k1_xboole_0
      | k2_relat_1(A_33) != k1_xboole_0
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_107,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_34])).

tff(c_109,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_107])).

tff(c_150,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_159,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_150])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_297,plain,(
    ! [A_117,C_118] :
      ( r2_hidden(k4_tarski('#skF_4'(A_117,k2_relat_1(A_117),C_118),C_118),A_117)
      | ~ r2_hidden(C_118,k2_relat_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_94,C_95,B_96] :
      ( m1_subset_1(A_94,C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_220,plain,(
    ! [A_94,B_3,A_2] :
      ( m1_subset_1(A_94,B_3)
      | ~ r2_hidden(A_94,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_215])).

tff(c_548,plain,(
    ! [A_162,C_163,B_164] :
      ( m1_subset_1(k4_tarski('#skF_4'(A_162,k2_relat_1(A_162),C_163),C_163),B_164)
      | ~ r1_tarski(A_162,B_164)
      | ~ r2_hidden(C_163,k2_relat_1(A_162)) ) ),
    inference(resolution,[status(thm)],[c_297,c_220])).

tff(c_243,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_252,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_243])).

tff(c_48,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k2_relset_1('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(D_56,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_253,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k2_relat_1('#skF_7'))
      | ~ m1_subset_1(D_56,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_48])).

tff(c_316,plain,(
    ! [C_118] :
      ( ~ m1_subset_1(k4_tarski('#skF_4'(k2_relat_1('#skF_7'),k2_relat_1(k2_relat_1('#skF_7')),C_118),C_118),'#skF_6')
      | ~ r2_hidden(C_118,k2_relat_1(k2_relat_1('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_297,c_253])).

tff(c_586,plain,(
    ! [C_163] :
      ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
      | ~ r2_hidden(C_163,k2_relat_1(k2_relat_1('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_548,c_316])).

tff(c_596,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_599,plain,
    ( ~ v5_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_14,c_596])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_159,c_599])).

tff(c_605,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_606,plain,(
    ! [A_165,B_166] :
      ( r2_hidden(k4_tarski('#skF_2'(A_165,B_166),'#skF_1'(A_165,B_166)),A_165)
      | r2_hidden('#skF_3'(A_165,B_166),B_166)
      | k2_relat_1(A_165) = B_166 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_315,plain,(
    ! [C_118] :
      ( r2_hidden(k4_tarski('#skF_4'(k1_xboole_0,k1_xboole_0,C_118),C_118),k1_xboole_0)
      | ~ r2_hidden(C_118,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_297])).

tff(c_369,plain,(
    ! [C_129] :
      ( r2_hidden(k4_tarski('#skF_4'(k1_xboole_0,k1_xboole_0,C_129),C_129),k1_xboole_0)
      | ~ r2_hidden(C_129,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_315])).

tff(c_38,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_377,plain,(
    ! [C_129] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_4'(k1_xboole_0,k1_xboole_0,C_129),C_129))
      | ~ r2_hidden(C_129,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_369,c_38])).

tff(c_385,plain,(
    ! [C_129] : ~ r2_hidden(C_129,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_377])).

tff(c_610,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_166),B_166)
      | k2_relat_1(k1_xboole_0) = B_166 ) ),
    inference(resolution,[status(thm)],[c_606,c_385])).

tff(c_672,plain,(
    ! [B_170] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_170),B_170)
      | k1_xboole_0 = B_170 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_610])).

tff(c_753,plain,(
    ! [B_176,B_177] :
      ( m1_subset_1('#skF_3'(k1_xboole_0,B_176),B_177)
      | ~ r1_tarski(B_176,B_177)
      | k1_xboole_0 = B_176 ) ),
    inference(resolution,[status(thm)],[c_672,c_220])).

tff(c_688,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_672,c_253])).

tff(c_700,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_688])).

tff(c_756,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_753,c_700])).

tff(c_786,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_756])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_786])).

tff(c_790,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_968,plain,(
    ! [A_220,B_221,C_222] :
      ( k1_relset_1(A_220,B_221,C_222) = k1_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_975,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_968])).

tff(c_978,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_975])).

tff(c_980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:23:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.43  
% 2.96/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.96/1.43  
% 2.96/1.43  %Foreground sorts:
% 2.96/1.43  
% 2.96/1.43  
% 2.96/1.43  %Background operators:
% 2.96/1.43  
% 2.96/1.43  
% 2.96/1.43  %Foreground operators:
% 2.96/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.96/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.96/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.96/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.96/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.96/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.96/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.96/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.96/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.96/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.96/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.96/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.43  
% 2.96/1.45  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.96/1.45  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.96/1.45  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.96/1.45  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.96/1.45  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.96/1.45  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.96/1.45  tff(f_58, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.96/1.45  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.96/1.45  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.96/1.45  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.96/1.45  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.96/1.45  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.96/1.45  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.96/1.45  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.96/1.45  tff(c_50, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.96/1.45  tff(c_28, plain, (![A_31, B_32]: (v1_relat_1(k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.45  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.96/1.45  tff(c_89, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.96/1.45  tff(c_95, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_89])).
% 2.96/1.45  tff(c_99, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_95])).
% 2.96/1.45  tff(c_36, plain, (![A_33]: (k2_relat_1(A_33)=k1_xboole_0 | k1_relat_1(A_33)!=k1_xboole_0 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.96/1.45  tff(c_106, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_36])).
% 2.96/1.45  tff(c_108, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 2.96/1.45  tff(c_34, plain, (![A_33]: (k1_relat_1(A_33)=k1_xboole_0 | k2_relat_1(A_33)!=k1_xboole_0 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.96/1.45  tff(c_107, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_34])).
% 2.96/1.45  tff(c_109, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_107])).
% 2.96/1.45  tff(c_150, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.45  tff(c_159, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_150])).
% 2.96/1.45  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.96/1.45  tff(c_297, plain, (![A_117, C_118]: (r2_hidden(k4_tarski('#skF_4'(A_117, k2_relat_1(A_117), C_118), C_118), A_117) | ~r2_hidden(C_118, k2_relat_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.96/1.45  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.45  tff(c_215, plain, (![A_94, C_95, B_96]: (m1_subset_1(A_94, C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.45  tff(c_220, plain, (![A_94, B_3, A_2]: (m1_subset_1(A_94, B_3) | ~r2_hidden(A_94, A_2) | ~r1_tarski(A_2, B_3))), inference(resolution, [status(thm)], [c_6, c_215])).
% 2.96/1.45  tff(c_548, plain, (![A_162, C_163, B_164]: (m1_subset_1(k4_tarski('#skF_4'(A_162, k2_relat_1(A_162), C_163), C_163), B_164) | ~r1_tarski(A_162, B_164) | ~r2_hidden(C_163, k2_relat_1(A_162)))), inference(resolution, [status(thm)], [c_297, c_220])).
% 2.96/1.45  tff(c_243, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.96/1.45  tff(c_252, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_243])).
% 2.96/1.45  tff(c_48, plain, (![D_56]: (~r2_hidden(D_56, k2_relset_1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1(D_56, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.96/1.45  tff(c_253, plain, (![D_56]: (~r2_hidden(D_56, k2_relat_1('#skF_7')) | ~m1_subset_1(D_56, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_48])).
% 2.96/1.45  tff(c_316, plain, (![C_118]: (~m1_subset_1(k4_tarski('#skF_4'(k2_relat_1('#skF_7'), k2_relat_1(k2_relat_1('#skF_7')), C_118), C_118), '#skF_6') | ~r2_hidden(C_118, k2_relat_1(k2_relat_1('#skF_7'))))), inference(resolution, [status(thm)], [c_297, c_253])).
% 2.96/1.45  tff(c_586, plain, (![C_163]: (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden(C_163, k2_relat_1(k2_relat_1('#skF_7'))))), inference(resolution, [status(thm)], [c_548, c_316])).
% 2.96/1.45  tff(c_596, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_586])).
% 2.96/1.45  tff(c_599, plain, (~v5_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_14, c_596])).
% 2.96/1.45  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_159, c_599])).
% 2.96/1.45  tff(c_605, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_586])).
% 2.96/1.45  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.45  tff(c_606, plain, (![A_165, B_166]: (r2_hidden(k4_tarski('#skF_2'(A_165, B_166), '#skF_1'(A_165, B_166)), A_165) | r2_hidden('#skF_3'(A_165, B_166), B_166) | k2_relat_1(A_165)=B_166)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.96/1.45  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.45  tff(c_315, plain, (![C_118]: (r2_hidden(k4_tarski('#skF_4'(k1_xboole_0, k1_xboole_0, C_118), C_118), k1_xboole_0) | ~r2_hidden(C_118, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_297])).
% 2.96/1.45  tff(c_369, plain, (![C_129]: (r2_hidden(k4_tarski('#skF_4'(k1_xboole_0, k1_xboole_0, C_129), C_129), k1_xboole_0) | ~r2_hidden(C_129, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_315])).
% 2.96/1.45  tff(c_38, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.96/1.45  tff(c_377, plain, (![C_129]: (~r1_tarski(k1_xboole_0, k4_tarski('#skF_4'(k1_xboole_0, k1_xboole_0, C_129), C_129)) | ~r2_hidden(C_129, k1_xboole_0))), inference(resolution, [status(thm)], [c_369, c_38])).
% 2.96/1.45  tff(c_385, plain, (![C_129]: (~r2_hidden(C_129, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_377])).
% 2.96/1.45  tff(c_610, plain, (![B_166]: (r2_hidden('#skF_3'(k1_xboole_0, B_166), B_166) | k2_relat_1(k1_xboole_0)=B_166)), inference(resolution, [status(thm)], [c_606, c_385])).
% 2.96/1.45  tff(c_672, plain, (![B_170]: (r2_hidden('#skF_3'(k1_xboole_0, B_170), B_170) | k1_xboole_0=B_170)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_610])).
% 2.96/1.45  tff(c_753, plain, (![B_176, B_177]: (m1_subset_1('#skF_3'(k1_xboole_0, B_176), B_177) | ~r1_tarski(B_176, B_177) | k1_xboole_0=B_176)), inference(resolution, [status(thm)], [c_672, c_220])).
% 2.96/1.45  tff(c_688, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_672, c_253])).
% 2.96/1.45  tff(c_700, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_109, c_688])).
% 2.96/1.45  tff(c_756, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_753, c_700])).
% 2.96/1.45  tff(c_786, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_605, c_756])).
% 2.96/1.45  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_786])).
% 2.96/1.45  tff(c_790, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 2.96/1.45  tff(c_968, plain, (![A_220, B_221, C_222]: (k1_relset_1(A_220, B_221, C_222)=k1_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.96/1.45  tff(c_975, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_968])).
% 2.96/1.45  tff(c_978, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_790, c_975])).
% 2.96/1.45  tff(c_980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_978])).
% 2.96/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.45  
% 2.96/1.45  Inference rules
% 2.96/1.45  ----------------------
% 2.96/1.45  #Ref     : 0
% 2.96/1.45  #Sup     : 179
% 2.96/1.45  #Fact    : 0
% 2.96/1.45  #Define  : 0
% 2.96/1.45  #Split   : 7
% 2.96/1.45  #Chain   : 0
% 2.96/1.45  #Close   : 0
% 2.96/1.45  
% 2.96/1.45  Ordering : KBO
% 2.96/1.45  
% 2.96/1.45  Simplification rules
% 2.96/1.45  ----------------------
% 2.96/1.45  #Subsume      : 37
% 2.96/1.45  #Demod        : 109
% 2.96/1.45  #Tautology    : 65
% 2.96/1.45  #SimpNegUnit  : 19
% 2.96/1.45  #BackRed      : 13
% 2.96/1.45  
% 2.96/1.45  #Partial instantiations: 0
% 2.96/1.45  #Strategies tried      : 1
% 2.96/1.45  
% 2.96/1.45  Timing (in seconds)
% 2.96/1.45  ----------------------
% 2.96/1.45  Preprocessing        : 0.33
% 2.96/1.45  Parsing              : 0.17
% 2.96/1.45  CNF conversion       : 0.02
% 2.96/1.45  Main loop            : 0.37
% 2.96/1.45  Inferencing          : 0.14
% 2.96/1.45  Reduction            : 0.11
% 2.96/1.45  Demodulation         : 0.08
% 2.96/1.45  BG Simplification    : 0.02
% 2.96/1.45  Subsumption          : 0.06
% 2.96/1.45  Abstraction          : 0.02
% 2.96/1.45  MUC search           : 0.00
% 2.96/1.45  Cooper               : 0.00
% 2.96/1.45  Total                : 0.73
% 2.96/1.45  Index Insertion      : 0.00
% 2.96/1.45  Index Deletion       : 0.00
% 2.96/1.45  Index Matching       : 0.00
% 2.96/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
