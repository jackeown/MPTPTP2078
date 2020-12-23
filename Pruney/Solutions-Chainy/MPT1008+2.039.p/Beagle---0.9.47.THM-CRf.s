%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:31 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 274 expanded)
%              Number of leaves         :   47 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 560 expanded)
%              Number of equality atoms :   73 ( 233 expanded)
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

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_106,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_114,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_106])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_34,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_133,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_114,c_34])).

tff(c_147,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_481,plain,(
    ! [B_121,A_122] :
      ( k1_tarski(k1_funct_1(B_121,A_122)) = k2_relat_1(B_121)
      | k1_tarski(A_122) != k1_relat_1(B_121)
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_306,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_314,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_306])).

tff(c_68,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_385,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_68])).

tff(c_487,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_385])).

tff(c_497,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_76,c_487])).

tff(c_164,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_172,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_164])).

tff(c_261,plain,(
    ! [B_99,A_100] :
      ( r1_tarski(k1_relat_1(B_99),A_100)
      | ~ v4_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k1_tarski(B_14) = A_13
      | k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_tarski(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_732,plain,(
    ! [B_149,B_150] :
      ( k1_tarski(B_149) = k1_relat_1(B_150)
      | k1_relat_1(B_150) = k1_xboole_0
      | ~ v4_relat_1(B_150,k1_tarski(B_149))
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_261,c_16])).

tff(c_742,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_172,c_732])).

tff(c_750,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_742])).

tff(c_752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_497,c_750])).

tff(c_753,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_754,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_777,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_754])).

tff(c_1127,plain,(
    ! [B_207,A_208] :
      ( k1_tarski(k1_funct_1(B_207,A_208)) = k2_relat_1(B_207)
      | k1_tarski(A_208) != k1_relat_1(B_207)
      | ~ v1_funct_1(B_207)
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_760,plain,(
    ! [A_15] : m1_subset_1('#skF_6',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_22])).

tff(c_1098,plain,(
    ! [A_200,B_201,C_202] :
      ( k2_relset_1(A_200,B_201,C_202) = k2_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1103,plain,(
    ! [A_200,B_201] : k2_relset_1(A_200,B_201,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_760,c_1098])).

tff(c_1119,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_68])).

tff(c_1133,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1127,c_1119])).

tff(c_1143,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_76,c_777,c_1133])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_762,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_70])).

tff(c_74,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_66,plain,(
    ! [B_53,A_52,C_54] :
      ( k1_xboole_0 = B_53
      | k1_relset_1(A_52,B_53,C_54) = A_52
      | ~ v1_funct_2(C_54,A_52,B_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1552,plain,(
    ! [B_258,A_259,C_260] :
      ( B_258 = '#skF_6'
      | k1_relset_1(A_259,B_258,C_260) = A_259
      | ~ v1_funct_2(C_260,A_259,B_258)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_259,B_258))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_66])).

tff(c_1558,plain,(
    ! [B_261,A_262] :
      ( B_261 = '#skF_6'
      | k1_relset_1(A_262,B_261,'#skF_6') = A_262
      | ~ v1_funct_2('#skF_6',A_262,B_261) ) ),
    inference(resolution,[status(thm)],[c_760,c_1552])).

tff(c_1570,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1558])).

tff(c_1578,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_1570])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_761,plain,(
    ! [A_6] : r1_tarski('#skF_6',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_8])).

tff(c_1747,plain,(
    ! [D_279,A_280,B_281,C_282] :
      ( r2_hidden(k4_tarski(D_279,'#skF_3'(A_280,B_281,C_282,D_279)),C_282)
      | ~ r2_hidden(D_279,B_281)
      | k1_relset_1(B_281,A_280,C_282) != B_281
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(B_281,A_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    ! [B_29,A_28] :
      ( ~ r1_tarski(B_29,A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1901,plain,(
    ! [C_290,D_291,A_292,B_293] :
      ( ~ r1_tarski(C_290,k4_tarski(D_291,'#skF_3'(A_292,B_293,C_290,D_291)))
      | ~ r2_hidden(D_291,B_293)
      | k1_relset_1(B_293,A_292,C_290) != B_293
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(B_293,A_292))) ) ),
    inference(resolution,[status(thm)],[c_1747,c_40])).

tff(c_1917,plain,(
    ! [D_291,B_293,A_292] :
      ( ~ r2_hidden(D_291,B_293)
      | k1_relset_1(B_293,A_292,'#skF_6') != B_293
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_293,A_292))) ) ),
    inference(resolution,[status(thm)],[c_761,c_1901])).

tff(c_1924,plain,(
    ! [D_294,B_295,A_296] :
      ( ~ r2_hidden(D_294,B_295)
      | k1_relset_1(B_295,A_296,'#skF_6') != B_295 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_1917])).

tff(c_1940,plain,(
    ! [A_297,A_298,B_299] :
      ( k1_relset_1(A_297,A_298,'#skF_6') != A_297
      | r1_tarski(A_297,B_299) ) ),
    inference(resolution,[status(thm)],[c_6,c_1924])).

tff(c_1951,plain,(
    ! [B_300] : r1_tarski(k1_tarski('#skF_4'),B_300) ),
    inference(superposition,[status(thm),theory(equality)],[c_1578,c_1940])).

tff(c_827,plain,(
    ! [C_165,A_166,B_167] :
      ( v4_relat_1(C_165,A_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_833,plain,(
    ! [A_168] : v4_relat_1('#skF_6',A_168) ),
    inference(resolution,[status(thm)],[c_760,c_827])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_836,plain,(
    ! [A_168] :
      ( k7_relat_1('#skF_6',A_168) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_833,c_30])).

tff(c_839,plain,(
    ! [A_168] : k7_relat_1('#skF_6',A_168) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_836])).

tff(c_937,plain,(
    ! [B_188,A_189] :
      ( k1_relat_1(k7_relat_1(B_188,A_189)) = A_189
      | ~ r1_tarski(A_189,k1_relat_1(B_188))
      | ~ v1_relat_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_948,plain,(
    ! [A_189] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_189)) = A_189
      | ~ r1_tarski(A_189,'#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_777,c_937])).

tff(c_956,plain,(
    ! [A_189] :
      ( A_189 = '#skF_6'
      | ~ r1_tarski(A_189,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_777,c_839,c_948])).

tff(c_1985,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1951,c_956])).

tff(c_2012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1143,c_1985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.63  
% 3.62/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.62/1.63  
% 3.62/1.63  %Foreground sorts:
% 3.62/1.63  
% 3.62/1.63  
% 3.62/1.63  %Background operators:
% 3.62/1.63  
% 3.62/1.63  
% 3.62/1.63  %Foreground operators:
% 3.62/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.62/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.62/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.62/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.62/1.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.62/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.62/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.62/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.62/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.62/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.62/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.62/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.62/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.62/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.62/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.62/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.62/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.62/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.62/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.62/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.62/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.63  
% 3.97/1.65  tff(f_149, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.97/1.65  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.97/1.65  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.97/1.65  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.97/1.65  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.97/1.65  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.97/1.65  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.97/1.65  tff(f_46, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.97/1.65  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.97/1.65  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.97/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.97/1.65  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.97/1.65  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 3.97/1.65  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.97/1.65  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.97/1.65  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 3.97/1.65  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.97/1.65  tff(c_106, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.97/1.65  tff(c_114, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_106])).
% 3.97/1.65  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.97/1.65  tff(c_34, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.97/1.65  tff(c_133, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_114, c_34])).
% 3.97/1.65  tff(c_147, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_133])).
% 3.97/1.65  tff(c_481, plain, (![B_121, A_122]: (k1_tarski(k1_funct_1(B_121, A_122))=k2_relat_1(B_121) | k1_tarski(A_122)!=k1_relat_1(B_121) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.97/1.65  tff(c_306, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.97/1.65  tff(c_314, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_306])).
% 3.97/1.65  tff(c_68, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.97/1.65  tff(c_385, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_68])).
% 3.97/1.65  tff(c_487, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_481, c_385])).
% 3.97/1.65  tff(c_497, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_76, c_487])).
% 3.97/1.65  tff(c_164, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.97/1.65  tff(c_172, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_164])).
% 3.97/1.65  tff(c_261, plain, (![B_99, A_100]: (r1_tarski(k1_relat_1(B_99), A_100) | ~v4_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.97/1.65  tff(c_16, plain, (![B_14, A_13]: (k1_tarski(B_14)=A_13 | k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.97/1.65  tff(c_732, plain, (![B_149, B_150]: (k1_tarski(B_149)=k1_relat_1(B_150) | k1_relat_1(B_150)=k1_xboole_0 | ~v4_relat_1(B_150, k1_tarski(B_149)) | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_261, c_16])).
% 3.97/1.65  tff(c_742, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_172, c_732])).
% 3.97/1.65  tff(c_750, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_742])).
% 3.97/1.65  tff(c_752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_497, c_750])).
% 3.97/1.65  tff(c_753, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_133])).
% 3.97/1.65  tff(c_754, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_133])).
% 3.97/1.65  tff(c_777, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_754])).
% 3.97/1.65  tff(c_1127, plain, (![B_207, A_208]: (k1_tarski(k1_funct_1(B_207, A_208))=k2_relat_1(B_207) | k1_tarski(A_208)!=k1_relat_1(B_207) | ~v1_funct_1(B_207) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.97/1.65  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.97/1.65  tff(c_760, plain, (![A_15]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_753, c_22])).
% 3.97/1.65  tff(c_1098, plain, (![A_200, B_201, C_202]: (k2_relset_1(A_200, B_201, C_202)=k2_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.97/1.65  tff(c_1103, plain, (![A_200, B_201]: (k2_relset_1(A_200, B_201, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_760, c_1098])).
% 3.97/1.65  tff(c_1119, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_68])).
% 3.97/1.65  tff(c_1133, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1127, c_1119])).
% 3.97/1.65  tff(c_1143, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_76, c_777, c_1133])).
% 3.97/1.65  tff(c_70, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.97/1.65  tff(c_762, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_70])).
% 3.97/1.65  tff(c_74, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.97/1.65  tff(c_66, plain, (![B_53, A_52, C_54]: (k1_xboole_0=B_53 | k1_relset_1(A_52, B_53, C_54)=A_52 | ~v1_funct_2(C_54, A_52, B_53) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.97/1.65  tff(c_1552, plain, (![B_258, A_259, C_260]: (B_258='#skF_6' | k1_relset_1(A_259, B_258, C_260)=A_259 | ~v1_funct_2(C_260, A_259, B_258) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_259, B_258))))), inference(demodulation, [status(thm), theory('equality')], [c_753, c_66])).
% 3.97/1.65  tff(c_1558, plain, (![B_261, A_262]: (B_261='#skF_6' | k1_relset_1(A_262, B_261, '#skF_6')=A_262 | ~v1_funct_2('#skF_6', A_262, B_261))), inference(resolution, [status(thm)], [c_760, c_1552])).
% 3.97/1.65  tff(c_1570, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1558])).
% 3.97/1.65  tff(c_1578, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_762, c_1570])).
% 3.97/1.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.97/1.65  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.97/1.65  tff(c_761, plain, (![A_6]: (r1_tarski('#skF_6', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_753, c_8])).
% 3.97/1.65  tff(c_1747, plain, (![D_279, A_280, B_281, C_282]: (r2_hidden(k4_tarski(D_279, '#skF_3'(A_280, B_281, C_282, D_279)), C_282) | ~r2_hidden(D_279, B_281) | k1_relset_1(B_281, A_280, C_282)!=B_281 | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(B_281, A_280))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.97/1.65  tff(c_40, plain, (![B_29, A_28]: (~r1_tarski(B_29, A_28) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.65  tff(c_1901, plain, (![C_290, D_291, A_292, B_293]: (~r1_tarski(C_290, k4_tarski(D_291, '#skF_3'(A_292, B_293, C_290, D_291))) | ~r2_hidden(D_291, B_293) | k1_relset_1(B_293, A_292, C_290)!=B_293 | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(B_293, A_292))))), inference(resolution, [status(thm)], [c_1747, c_40])).
% 3.97/1.65  tff(c_1917, plain, (![D_291, B_293, A_292]: (~r2_hidden(D_291, B_293) | k1_relset_1(B_293, A_292, '#skF_6')!=B_293 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_293, A_292))))), inference(resolution, [status(thm)], [c_761, c_1901])).
% 3.97/1.65  tff(c_1924, plain, (![D_294, B_295, A_296]: (~r2_hidden(D_294, B_295) | k1_relset_1(B_295, A_296, '#skF_6')!=B_295)), inference(demodulation, [status(thm), theory('equality')], [c_760, c_1917])).
% 3.97/1.65  tff(c_1940, plain, (![A_297, A_298, B_299]: (k1_relset_1(A_297, A_298, '#skF_6')!=A_297 | r1_tarski(A_297, B_299))), inference(resolution, [status(thm)], [c_6, c_1924])).
% 3.97/1.65  tff(c_1951, plain, (![B_300]: (r1_tarski(k1_tarski('#skF_4'), B_300))), inference(superposition, [status(thm), theory('equality')], [c_1578, c_1940])).
% 3.97/1.65  tff(c_827, plain, (![C_165, A_166, B_167]: (v4_relat_1(C_165, A_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.97/1.65  tff(c_833, plain, (![A_168]: (v4_relat_1('#skF_6', A_168))), inference(resolution, [status(thm)], [c_760, c_827])).
% 3.97/1.65  tff(c_30, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.97/1.65  tff(c_836, plain, (![A_168]: (k7_relat_1('#skF_6', A_168)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_833, c_30])).
% 3.97/1.65  tff(c_839, plain, (![A_168]: (k7_relat_1('#skF_6', A_168)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_836])).
% 3.97/1.65  tff(c_937, plain, (![B_188, A_189]: (k1_relat_1(k7_relat_1(B_188, A_189))=A_189 | ~r1_tarski(A_189, k1_relat_1(B_188)) | ~v1_relat_1(B_188))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.97/1.65  tff(c_948, plain, (![A_189]: (k1_relat_1(k7_relat_1('#skF_6', A_189))=A_189 | ~r1_tarski(A_189, '#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_777, c_937])).
% 3.97/1.65  tff(c_956, plain, (![A_189]: (A_189='#skF_6' | ~r1_tarski(A_189, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_777, c_839, c_948])).
% 3.97/1.65  tff(c_1985, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_1951, c_956])).
% 3.97/1.65  tff(c_2012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1143, c_1985])).
% 3.97/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.65  
% 3.97/1.65  Inference rules
% 3.97/1.65  ----------------------
% 3.97/1.65  #Ref     : 0
% 3.97/1.65  #Sup     : 419
% 3.97/1.65  #Fact    : 0
% 3.97/1.65  #Define  : 0
% 3.97/1.65  #Split   : 2
% 3.97/1.65  #Chain   : 0
% 3.97/1.65  #Close   : 0
% 3.97/1.65  
% 3.97/1.65  Ordering : KBO
% 3.97/1.65  
% 3.97/1.65  Simplification rules
% 3.97/1.65  ----------------------
% 3.97/1.65  #Subsume      : 65
% 3.97/1.65  #Demod        : 226
% 3.97/1.65  #Tautology    : 157
% 3.97/1.65  #SimpNegUnit  : 3
% 3.97/1.65  #BackRed      : 11
% 3.97/1.65  
% 3.97/1.65  #Partial instantiations: 0
% 3.97/1.65  #Strategies tried      : 1
% 3.97/1.65  
% 3.97/1.65  Timing (in seconds)
% 3.97/1.65  ----------------------
% 3.97/1.65  Preprocessing        : 0.35
% 3.97/1.65  Parsing              : 0.18
% 3.97/1.65  CNF conversion       : 0.02
% 3.97/1.65  Main loop            : 0.53
% 3.97/1.65  Inferencing          : 0.19
% 3.97/1.65  Reduction            : 0.16
% 3.97/1.65  Demodulation         : 0.11
% 3.97/1.65  BG Simplification    : 0.03
% 3.97/1.65  Subsumption          : 0.10
% 3.97/1.65  Abstraction          : 0.02
% 3.97/1.65  MUC search           : 0.00
% 3.97/1.65  Cooper               : 0.00
% 3.97/1.65  Total                : 0.92
% 3.97/1.65  Index Insertion      : 0.00
% 3.97/1.65  Index Deletion       : 0.00
% 3.97/1.65  Index Matching       : 0.00
% 3.97/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
