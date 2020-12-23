%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:18 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 224 expanded)
%              Number of leaves         :   39 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 448 expanded)
%              Number of equality atoms :   34 ( 108 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    ! [C_117,A_118] :
      ( r2_hidden(k4_tarski(C_117,'#skF_4'(A_118,k1_relat_1(A_118),C_117)),A_118)
      | ~ r2_hidden(C_117,k1_relat_1(A_118)) ) ),
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

tff(c_542,plain,(
    ! [C_162,A_163,B_164] :
      ( m1_subset_1(k4_tarski(C_162,'#skF_4'(A_163,k1_relat_1(A_163),C_162)),B_164)
      | ~ r1_tarski(A_163,B_164)
      | ~ r2_hidden(C_162,k1_relat_1(A_163)) ) ),
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

tff(c_313,plain,(
    ! [C_117] :
      ( ~ m1_subset_1(k4_tarski(C_117,'#skF_4'(k2_relat_1('#skF_7'),k1_relat_1(k2_relat_1('#skF_7')),C_117)),'#skF_6')
      | ~ r2_hidden(C_117,k1_relat_1(k2_relat_1('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_297,c_253])).

tff(c_577,plain,(
    ! [C_162] :
      ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
      | ~ r2_hidden(C_162,k1_relat_1(k2_relat_1('#skF_7'))) ) ),
    inference(resolution,[status(thm)],[c_542,c_313])).

tff(c_587,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_590,plain,
    ( ~ v5_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_14,c_587])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_159,c_590])).

tff(c_596,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_597,plain,(
    ! [A_165,B_166] :
      ( r2_hidden(k4_tarski('#skF_1'(A_165,B_166),'#skF_2'(A_165,B_166)),A_165)
      | r2_hidden('#skF_3'(A_165,B_166),B_166)
      | k1_relat_1(A_165) = B_166 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_312,plain,(
    ! [C_117] :
      ( r2_hidden(k4_tarski(C_117,'#skF_4'(k1_xboole_0,k1_xboole_0,C_117)),k1_xboole_0)
      | ~ r2_hidden(C_117,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_297])).

tff(c_366,plain,(
    ! [C_129] :
      ( r2_hidden(k4_tarski(C_129,'#skF_4'(k1_xboole_0,k1_xboole_0,C_129)),k1_xboole_0)
      | ~ r2_hidden(C_129,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_312])).

tff(c_38,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_374,plain,(
    ! [C_129] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_129,'#skF_4'(k1_xboole_0,k1_xboole_0,C_129)))
      | ~ r2_hidden(C_129,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_366,c_38])).

tff(c_382,plain,(
    ! [C_129] : ~ r2_hidden(C_129,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_374])).

tff(c_601,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_166),B_166)
      | k1_relat_1(k1_xboole_0) = B_166 ) ),
    inference(resolution,[status(thm)],[c_597,c_382])).

tff(c_663,plain,(
    ! [B_170] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_170),B_170)
      | k1_xboole_0 = B_170 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_601])).

tff(c_733,plain,(
    ! [B_175,B_176] :
      ( m1_subset_1('#skF_3'(k1_xboole_0,B_175),B_176)
      | ~ r1_tarski(B_175,B_176)
      | k1_xboole_0 = B_175 ) ),
    inference(resolution,[status(thm)],[c_663,c_220])).

tff(c_679,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_663,c_253])).

tff(c_691,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_679])).

tff(c_736,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_733,c_691])).

tff(c_766,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_736])).

tff(c_768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_766])).

tff(c_769,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_776,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_107])).

tff(c_961,plain,(
    ! [A_218,B_219,C_220] :
      ( k1_relset_1(A_218,B_219,C_220) = k1_relat_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_968,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_961])).

tff(c_971,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_968])).

tff(c_973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:04:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.46  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.13/1.46  
% 3.13/1.46  %Foreground sorts:
% 3.13/1.46  
% 3.13/1.46  
% 3.13/1.46  %Background operators:
% 3.13/1.46  
% 3.13/1.46  
% 3.13/1.46  %Foreground operators:
% 3.13/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.13/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.13/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.13/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.13/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.13/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.13/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.13/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.46  
% 3.13/1.48  tff(f_109, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.13/1.48  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.13/1.48  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.13/1.48  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.13/1.48  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.13/1.48  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.13/1.48  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.13/1.48  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.13/1.48  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.13/1.48  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.13/1.48  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.13/1.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.13/1.48  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.13/1.48  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.13/1.48  tff(c_50, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.13/1.48  tff(c_28, plain, (![A_31, B_32]: (v1_relat_1(k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.13/1.48  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.13/1.48  tff(c_89, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.48  tff(c_95, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_89])).
% 3.13/1.48  tff(c_99, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_95])).
% 3.13/1.48  tff(c_36, plain, (![A_33]: (k2_relat_1(A_33)=k1_xboole_0 | k1_relat_1(A_33)!=k1_xboole_0 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.48  tff(c_106, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_36])).
% 3.13/1.48  tff(c_108, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 3.13/1.48  tff(c_34, plain, (![A_33]: (k1_relat_1(A_33)=k1_xboole_0 | k2_relat_1(A_33)!=k1_xboole_0 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.48  tff(c_107, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_34])).
% 3.13/1.48  tff(c_109, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_107])).
% 3.13/1.48  tff(c_150, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.13/1.48  tff(c_159, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_150])).
% 3.13/1.48  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.48  tff(c_297, plain, (![C_117, A_118]: (r2_hidden(k4_tarski(C_117, '#skF_4'(A_118, k1_relat_1(A_118), C_117)), A_118) | ~r2_hidden(C_117, k1_relat_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.13/1.48  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.48  tff(c_215, plain, (![A_94, C_95, B_96]: (m1_subset_1(A_94, C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.13/1.48  tff(c_220, plain, (![A_94, B_3, A_2]: (m1_subset_1(A_94, B_3) | ~r2_hidden(A_94, A_2) | ~r1_tarski(A_2, B_3))), inference(resolution, [status(thm)], [c_6, c_215])).
% 3.13/1.48  tff(c_542, plain, (![C_162, A_163, B_164]: (m1_subset_1(k4_tarski(C_162, '#skF_4'(A_163, k1_relat_1(A_163), C_162)), B_164) | ~r1_tarski(A_163, B_164) | ~r2_hidden(C_162, k1_relat_1(A_163)))), inference(resolution, [status(thm)], [c_297, c_220])).
% 3.13/1.48  tff(c_243, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.13/1.48  tff(c_252, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_243])).
% 3.13/1.48  tff(c_48, plain, (![D_56]: (~r2_hidden(D_56, k2_relset_1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1(D_56, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.13/1.48  tff(c_253, plain, (![D_56]: (~r2_hidden(D_56, k2_relat_1('#skF_7')) | ~m1_subset_1(D_56, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_48])).
% 3.13/1.48  tff(c_313, plain, (![C_117]: (~m1_subset_1(k4_tarski(C_117, '#skF_4'(k2_relat_1('#skF_7'), k1_relat_1(k2_relat_1('#skF_7')), C_117)), '#skF_6') | ~r2_hidden(C_117, k1_relat_1(k2_relat_1('#skF_7'))))), inference(resolution, [status(thm)], [c_297, c_253])).
% 3.13/1.48  tff(c_577, plain, (![C_162]: (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden(C_162, k1_relat_1(k2_relat_1('#skF_7'))))), inference(resolution, [status(thm)], [c_542, c_313])).
% 3.13/1.48  tff(c_587, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_577])).
% 3.13/1.48  tff(c_590, plain, (~v5_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_14, c_587])).
% 3.13/1.48  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_159, c_590])).
% 3.13/1.48  tff(c_596, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_577])).
% 3.13/1.48  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.13/1.48  tff(c_597, plain, (![A_165, B_166]: (r2_hidden(k4_tarski('#skF_1'(A_165, B_166), '#skF_2'(A_165, B_166)), A_165) | r2_hidden('#skF_3'(A_165, B_166), B_166) | k1_relat_1(A_165)=B_166)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.13/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.48  tff(c_312, plain, (![C_117]: (r2_hidden(k4_tarski(C_117, '#skF_4'(k1_xboole_0, k1_xboole_0, C_117)), k1_xboole_0) | ~r2_hidden(C_117, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_297])).
% 3.13/1.48  tff(c_366, plain, (![C_129]: (r2_hidden(k4_tarski(C_129, '#skF_4'(k1_xboole_0, k1_xboole_0, C_129)), k1_xboole_0) | ~r2_hidden(C_129, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_312])).
% 3.13/1.48  tff(c_38, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.13/1.48  tff(c_374, plain, (![C_129]: (~r1_tarski(k1_xboole_0, k4_tarski(C_129, '#skF_4'(k1_xboole_0, k1_xboole_0, C_129))) | ~r2_hidden(C_129, k1_xboole_0))), inference(resolution, [status(thm)], [c_366, c_38])).
% 3.13/1.48  tff(c_382, plain, (![C_129]: (~r2_hidden(C_129, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_374])).
% 3.13/1.48  tff(c_601, plain, (![B_166]: (r2_hidden('#skF_3'(k1_xboole_0, B_166), B_166) | k1_relat_1(k1_xboole_0)=B_166)), inference(resolution, [status(thm)], [c_597, c_382])).
% 3.13/1.48  tff(c_663, plain, (![B_170]: (r2_hidden('#skF_3'(k1_xboole_0, B_170), B_170) | k1_xboole_0=B_170)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_601])).
% 3.13/1.48  tff(c_733, plain, (![B_175, B_176]: (m1_subset_1('#skF_3'(k1_xboole_0, B_175), B_176) | ~r1_tarski(B_175, B_176) | k1_xboole_0=B_175)), inference(resolution, [status(thm)], [c_663, c_220])).
% 3.13/1.48  tff(c_679, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_663, c_253])).
% 3.13/1.48  tff(c_691, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_109, c_679])).
% 3.13/1.48  tff(c_736, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_733, c_691])).
% 3.13/1.48  tff(c_766, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_596, c_736])).
% 3.13/1.48  tff(c_768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_766])).
% 3.13/1.48  tff(c_769, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 3.13/1.48  tff(c_776, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_769, c_107])).
% 3.13/1.48  tff(c_961, plain, (![A_218, B_219, C_220]: (k1_relset_1(A_218, B_219, C_220)=k1_relat_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.13/1.48  tff(c_968, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_961])).
% 3.13/1.48  tff(c_971, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_776, c_968])).
% 3.13/1.48  tff(c_973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_971])).
% 3.13/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  Inference rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Ref     : 0
% 3.13/1.48  #Sup     : 176
% 3.13/1.48  #Fact    : 0
% 3.13/1.48  #Define  : 0
% 3.13/1.48  #Split   : 6
% 3.13/1.48  #Chain   : 0
% 3.13/1.48  #Close   : 0
% 3.13/1.48  
% 3.13/1.48  Ordering : KBO
% 3.13/1.48  
% 3.13/1.48  Simplification rules
% 3.13/1.48  ----------------------
% 3.13/1.48  #Subsume      : 36
% 3.13/1.48  #Demod        : 116
% 3.13/1.48  #Tautology    : 66
% 3.13/1.48  #SimpNegUnit  : 19
% 3.13/1.48  #BackRed      : 13
% 3.13/1.48  
% 3.13/1.48  #Partial instantiations: 0
% 3.13/1.48  #Strategies tried      : 1
% 3.13/1.48  
% 3.13/1.48  Timing (in seconds)
% 3.13/1.48  ----------------------
% 3.13/1.48  Preprocessing        : 0.33
% 3.13/1.48  Parsing              : 0.16
% 3.13/1.48  CNF conversion       : 0.02
% 3.13/1.48  Main loop            : 0.37
% 3.13/1.48  Inferencing          : 0.14
% 3.13/1.48  Reduction            : 0.11
% 3.13/1.48  Demodulation         : 0.08
% 3.13/1.48  BG Simplification    : 0.02
% 3.13/1.48  Subsumption          : 0.06
% 3.13/1.48  Abstraction          : 0.02
% 3.13/1.48  MUC search           : 0.00
% 3.13/1.48  Cooper               : 0.00
% 3.13/1.49  Total                : 0.73
% 3.13/1.49  Index Insertion      : 0.00
% 3.13/1.49  Index Deletion       : 0.00
% 3.13/1.49  Index Matching       : 0.00
% 3.13/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
