%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:17 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 162 expanded)
%              Number of leaves         :   52 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 324 expanded)
%              Number of equality atoms :   48 ( 101 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_51,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_108,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    k1_funct_1('#skF_10','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_102,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_298,plain,(
    ! [C_147,B_148,A_149] :
      ( v5_relat_1(C_147,B_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_307,plain,(
    v5_relat_1('#skF_10',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_102,c_298])).

tff(c_100,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_220,plain,(
    ! [B_126,A_127] :
      ( v1_relat_1(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_127))
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_226,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_102,c_220])).

tff(c_230,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_226])).

tff(c_48,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v5_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_106,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_104,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_375,plain,(
    ! [A_162,B_163,C_164] :
      ( k1_relset_1(A_162,B_163,C_164) = k1_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_384,plain,(
    k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_102,c_375])).

tff(c_1598,plain,(
    ! [B_367,A_368,C_369] :
      ( k1_xboole_0 = B_367
      | k1_relset_1(A_368,B_367,C_369) = A_368
      | ~ v1_funct_2(C_369,A_368,B_367)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(A_368,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1605,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_102,c_1598])).

tff(c_1609,plain,
    ( k1_tarski('#skF_8') = k1_xboole_0
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_384,c_1605])).

tff(c_1610,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1609])).

tff(c_52,plain,(
    ! [A_30] :
      ( k9_relat_1(A_30,k1_relat_1(A_30)) = k2_relat_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1615,plain,
    ( k9_relat_1('#skF_10','#skF_7') = k2_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1610,c_52])).

tff(c_1619,plain,(
    k9_relat_1('#skF_10','#skF_7') = k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_1615])).

tff(c_1733,plain,(
    ! [A_391,E_392,B_393] :
      ( r2_hidden(k1_funct_1(A_391,E_392),k9_relat_1(A_391,B_393))
      | ~ r2_hidden(E_392,B_393)
      | ~ r2_hidden(E_392,k1_relat_1(A_391))
      | ~ v1_funct_1(A_391)
      | ~ v1_relat_1(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1741,plain,(
    ! [E_392] :
      ( r2_hidden(k1_funct_1('#skF_10',E_392),k2_relat_1('#skF_10'))
      | ~ r2_hidden(E_392,'#skF_7')
      | ~ r2_hidden(E_392,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1619,c_1733])).

tff(c_1749,plain,(
    ! [E_394] :
      ( r2_hidden(k1_funct_1('#skF_10',E_394),k2_relat_1('#skF_10'))
      | ~ r2_hidden(E_394,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_106,c_1610,c_1741])).

tff(c_40,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_343,plain,(
    ! [A_156,C_157,B_158] :
      ( m1_subset_1(A_156,C_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(C_157))
      | ~ r2_hidden(A_156,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_348,plain,(
    ! [A_156,B_19,A_18] :
      ( m1_subset_1(A_156,B_19)
      | ~ r2_hidden(A_156,A_18)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_40,c_343])).

tff(c_1765,plain,(
    ! [E_397,B_398] :
      ( m1_subset_1(k1_funct_1('#skF_10',E_397),B_398)
      | ~ r1_tarski(k2_relat_1('#skF_10'),B_398)
      | ~ r2_hidden(E_397,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1749,c_348])).

tff(c_1768,plain,(
    ! [E_397,A_26] :
      ( m1_subset_1(k1_funct_1('#skF_10',E_397),A_26)
      | ~ r2_hidden(E_397,'#skF_7')
      | ~ v5_relat_1('#skF_10',A_26)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_48,c_1765])).

tff(c_1772,plain,(
    ! [E_399,A_400] :
      ( m1_subset_1(k1_funct_1('#skF_10',E_399),A_400)
      | ~ r2_hidden(E_399,'#skF_7')
      | ~ v5_relat_1('#skF_10',A_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_1768])).

tff(c_34,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_tarski(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1395,plain,(
    ! [E_330,C_331,B_332,A_333] :
      ( E_330 = C_331
      | E_330 = B_332
      | E_330 = A_333
      | ~ r2_hidden(E_330,k1_enumset1(A_333,B_332,C_331)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1442,plain,(
    ! [E_339,B_340,A_341] :
      ( E_339 = B_340
      | E_339 = A_341
      | E_339 = A_341
      | ~ r2_hidden(E_339,k2_tarski(A_341,B_340)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1395])).

tff(c_1461,plain,(
    ! [E_342,A_343] :
      ( E_342 = A_343
      | E_342 = A_343
      | E_342 = A_343
      | ~ r2_hidden(E_342,k1_tarski(A_343)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1442])).

tff(c_1465,plain,(
    ! [A_343,A_16] :
      ( A_343 = A_16
      | v1_xboole_0(k1_tarski(A_343))
      | ~ m1_subset_1(A_16,k1_tarski(A_343)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1461])).

tff(c_1471,plain,(
    ! [A_343,A_16] :
      ( A_343 = A_16
      | ~ m1_subset_1(A_16,k1_tarski(A_343)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1465])).

tff(c_1848,plain,(
    ! [E_401,A_402] :
      ( k1_funct_1('#skF_10',E_401) = A_402
      | ~ r2_hidden(E_401,'#skF_7')
      | ~ v5_relat_1('#skF_10',k1_tarski(A_402)) ) ),
    inference(resolution,[status(thm)],[c_1772,c_1471])).

tff(c_1856,plain,(
    ! [A_403] :
      ( k1_funct_1('#skF_10','#skF_9') = A_403
      | ~ v5_relat_1('#skF_10',k1_tarski(A_403)) ) ),
    inference(resolution,[status(thm)],[c_100,c_1848])).

tff(c_1859,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_307,c_1856])).

tff(c_1863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1859])).

tff(c_1864,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1609])).

tff(c_140,plain,(
    ! [A_103,B_104] : k1_enumset1(A_103,A_103,B_104) = k2_tarski(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [E_8,B_3,C_4] : r2_hidden(E_8,k1_enumset1(E_8,B_3,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_161,plain,(
    ! [A_105,B_106] : r2_hidden(A_105,k2_tarski(A_105,B_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10])).

tff(c_169,plain,(
    ! [A_107] : r2_hidden(A_107,k1_tarski(A_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_161])).

tff(c_78,plain,(
    ! [B_74,A_73] :
      ( ~ r1_tarski(B_74,A_73)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_173,plain,(
    ! [A_107] : ~ r1_tarski(k1_tarski(A_107),A_107) ),
    inference(resolution,[status(thm)],[c_169,c_78])).

tff(c_1898,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_173])).

tff(c_1910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.96  
% 4.67/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.97  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 4.67/1.97  
% 4.67/1.97  %Foreground sorts:
% 4.67/1.97  
% 4.67/1.97  
% 4.67/1.97  %Background operators:
% 4.67/1.97  
% 4.67/1.97  
% 4.67/1.97  %Foreground operators:
% 4.67/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.67/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.67/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.67/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.97  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.67/1.97  tff('#skF_7', type, '#skF_7': $i).
% 4.67/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.67/1.97  tff('#skF_10', type, '#skF_10': $i).
% 4.67/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.67/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.67/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.67/1.97  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.67/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.67/1.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.67/1.97  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.67/1.97  tff('#skF_9', type, '#skF_9': $i).
% 4.67/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.67/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.67/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.67/1.97  tff('#skF_8', type, '#skF_8': $i).
% 4.67/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.67/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.67/1.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.67/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.67/1.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.67/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.67/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.67/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.97  
% 4.95/1.98  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.95/1.98  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.95/1.98  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.95/1.98  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.95/1.98  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.95/1.98  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.95/1.98  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.95/1.98  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.95/1.98  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 4.95/1.98  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 4.95/1.98  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.95/1.98  tff(f_67, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.95/1.98  tff(f_51, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.95/1.98  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.95/1.98  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.95/1.98  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.95/1.98  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.95/1.98  tff(f_108, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.95/1.98  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.95/1.98  tff(c_98, plain, (k1_funct_1('#skF_10', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.95/1.98  tff(c_102, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.95/1.98  tff(c_298, plain, (![C_147, B_148, A_149]: (v5_relat_1(C_147, B_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.95/1.98  tff(c_307, plain, (v5_relat_1('#skF_10', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_102, c_298])).
% 4.95/1.98  tff(c_100, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.95/1.98  tff(c_50, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.95/1.98  tff(c_220, plain, (![B_126, A_127]: (v1_relat_1(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_127)) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.95/1.98  tff(c_226, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_102, c_220])).
% 4.95/1.98  tff(c_230, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_226])).
% 4.95/1.98  tff(c_48, plain, (![B_27, A_26]: (r1_tarski(k2_relat_1(B_27), A_26) | ~v5_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.95/1.98  tff(c_106, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.95/1.98  tff(c_104, plain, (v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.95/1.98  tff(c_375, plain, (![A_162, B_163, C_164]: (k1_relset_1(A_162, B_163, C_164)=k1_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.95/1.98  tff(c_384, plain, (k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_102, c_375])).
% 4.95/1.98  tff(c_1598, plain, (![B_367, A_368, C_369]: (k1_xboole_0=B_367 | k1_relset_1(A_368, B_367, C_369)=A_368 | ~v1_funct_2(C_369, A_368, B_367) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(A_368, B_367))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.95/1.98  tff(c_1605, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relset_1('#skF_7', k1_tarski('#skF_8'), '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_102, c_1598])).
% 4.95/1.98  tff(c_1609, plain, (k1_tarski('#skF_8')=k1_xboole_0 | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_384, c_1605])).
% 4.95/1.98  tff(c_1610, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_1609])).
% 4.95/1.98  tff(c_52, plain, (![A_30]: (k9_relat_1(A_30, k1_relat_1(A_30))=k2_relat_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.95/1.98  tff(c_1615, plain, (k9_relat_1('#skF_10', '#skF_7')=k2_relat_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1610, c_52])).
% 4.95/1.98  tff(c_1619, plain, (k9_relat_1('#skF_10', '#skF_7')=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_1615])).
% 4.95/1.98  tff(c_1733, plain, (![A_391, E_392, B_393]: (r2_hidden(k1_funct_1(A_391, E_392), k9_relat_1(A_391, B_393)) | ~r2_hidden(E_392, B_393) | ~r2_hidden(E_392, k1_relat_1(A_391)) | ~v1_funct_1(A_391) | ~v1_relat_1(A_391))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.95/1.98  tff(c_1741, plain, (![E_392]: (r2_hidden(k1_funct_1('#skF_10', E_392), k2_relat_1('#skF_10')) | ~r2_hidden(E_392, '#skF_7') | ~r2_hidden(E_392, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1619, c_1733])).
% 4.95/1.98  tff(c_1749, plain, (![E_394]: (r2_hidden(k1_funct_1('#skF_10', E_394), k2_relat_1('#skF_10')) | ~r2_hidden(E_394, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_106, c_1610, c_1741])).
% 4.95/1.98  tff(c_40, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.95/1.98  tff(c_343, plain, (![A_156, C_157, B_158]: (m1_subset_1(A_156, C_157) | ~m1_subset_1(B_158, k1_zfmisc_1(C_157)) | ~r2_hidden(A_156, B_158))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.95/1.98  tff(c_348, plain, (![A_156, B_19, A_18]: (m1_subset_1(A_156, B_19) | ~r2_hidden(A_156, A_18) | ~r1_tarski(A_18, B_19))), inference(resolution, [status(thm)], [c_40, c_343])).
% 4.95/1.98  tff(c_1765, plain, (![E_397, B_398]: (m1_subset_1(k1_funct_1('#skF_10', E_397), B_398) | ~r1_tarski(k2_relat_1('#skF_10'), B_398) | ~r2_hidden(E_397, '#skF_7'))), inference(resolution, [status(thm)], [c_1749, c_348])).
% 4.95/1.98  tff(c_1768, plain, (![E_397, A_26]: (m1_subset_1(k1_funct_1('#skF_10', E_397), A_26) | ~r2_hidden(E_397, '#skF_7') | ~v5_relat_1('#skF_10', A_26) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_48, c_1765])).
% 4.95/1.98  tff(c_1772, plain, (![E_399, A_400]: (m1_subset_1(k1_funct_1('#skF_10', E_399), A_400) | ~r2_hidden(E_399, '#skF_7') | ~v5_relat_1('#skF_10', A_400))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_1768])).
% 4.95/1.98  tff(c_34, plain, (![A_15]: (~v1_xboole_0(k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.95/1.98  tff(c_36, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.95/1.98  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.95/1.98  tff(c_30, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.95/1.98  tff(c_1395, plain, (![E_330, C_331, B_332, A_333]: (E_330=C_331 | E_330=B_332 | E_330=A_333 | ~r2_hidden(E_330, k1_enumset1(A_333, B_332, C_331)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.95/1.98  tff(c_1442, plain, (![E_339, B_340, A_341]: (E_339=B_340 | E_339=A_341 | E_339=A_341 | ~r2_hidden(E_339, k2_tarski(A_341, B_340)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1395])).
% 4.95/1.98  tff(c_1461, plain, (![E_342, A_343]: (E_342=A_343 | E_342=A_343 | E_342=A_343 | ~r2_hidden(E_342, k1_tarski(A_343)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1442])).
% 4.95/1.98  tff(c_1465, plain, (![A_343, A_16]: (A_343=A_16 | v1_xboole_0(k1_tarski(A_343)) | ~m1_subset_1(A_16, k1_tarski(A_343)))), inference(resolution, [status(thm)], [c_36, c_1461])).
% 4.95/1.98  tff(c_1471, plain, (![A_343, A_16]: (A_343=A_16 | ~m1_subset_1(A_16, k1_tarski(A_343)))), inference(negUnitSimplification, [status(thm)], [c_34, c_1465])).
% 4.95/1.98  tff(c_1848, plain, (![E_401, A_402]: (k1_funct_1('#skF_10', E_401)=A_402 | ~r2_hidden(E_401, '#skF_7') | ~v5_relat_1('#skF_10', k1_tarski(A_402)))), inference(resolution, [status(thm)], [c_1772, c_1471])).
% 4.95/1.98  tff(c_1856, plain, (![A_403]: (k1_funct_1('#skF_10', '#skF_9')=A_403 | ~v5_relat_1('#skF_10', k1_tarski(A_403)))), inference(resolution, [status(thm)], [c_100, c_1848])).
% 4.95/1.98  tff(c_1859, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_307, c_1856])).
% 4.95/1.98  tff(c_1863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_1859])).
% 4.95/1.98  tff(c_1864, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1609])).
% 4.95/1.98  tff(c_140, plain, (![A_103, B_104]: (k1_enumset1(A_103, A_103, B_104)=k2_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.95/1.98  tff(c_10, plain, (![E_8, B_3, C_4]: (r2_hidden(E_8, k1_enumset1(E_8, B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.95/1.98  tff(c_161, plain, (![A_105, B_106]: (r2_hidden(A_105, k2_tarski(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_10])).
% 4.95/1.98  tff(c_169, plain, (![A_107]: (r2_hidden(A_107, k1_tarski(A_107)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_161])).
% 4.95/1.98  tff(c_78, plain, (![B_74, A_73]: (~r1_tarski(B_74, A_73) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.95/1.98  tff(c_173, plain, (![A_107]: (~r1_tarski(k1_tarski(A_107), A_107))), inference(resolution, [status(thm)], [c_169, c_78])).
% 4.95/1.98  tff(c_1898, plain, (~r1_tarski(k1_xboole_0, '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1864, c_173])).
% 4.95/1.98  tff(c_1910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1898])).
% 4.95/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.98  
% 4.95/1.98  Inference rules
% 4.95/1.98  ----------------------
% 4.95/1.98  #Ref     : 0
% 4.95/1.98  #Sup     : 335
% 4.95/1.98  #Fact    : 0
% 4.95/1.98  #Define  : 0
% 4.95/1.98  #Split   : 23
% 4.95/1.98  #Chain   : 0
% 4.95/1.98  #Close   : 0
% 4.95/1.98  
% 4.95/1.98  Ordering : KBO
% 4.95/1.98  
% 4.95/1.98  Simplification rules
% 4.95/1.98  ----------------------
% 4.95/1.98  #Subsume      : 91
% 4.95/1.98  #Demod        : 108
% 4.95/1.98  #Tautology    : 71
% 4.95/1.98  #SimpNegUnit  : 82
% 4.95/1.98  #BackRed      : 66
% 4.95/1.98  
% 4.95/1.98  #Partial instantiations: 0
% 4.95/1.98  #Strategies tried      : 1
% 4.95/1.98  
% 4.95/1.98  Timing (in seconds)
% 4.95/1.98  ----------------------
% 4.95/1.99  Preprocessing        : 0.39
% 4.95/1.99  Parsing              : 0.17
% 4.95/1.99  CNF conversion       : 0.03
% 4.95/1.99  Main loop            : 0.75
% 4.95/1.99  Inferencing          : 0.27
% 4.95/1.99  Reduction            : 0.24
% 4.95/1.99  Demodulation         : 0.16
% 4.95/1.99  BG Simplification    : 0.03
% 4.95/1.99  Subsumption          : 0.14
% 4.95/1.99  Abstraction          : 0.05
% 4.95/1.99  MUC search           : 0.00
% 4.95/1.99  Cooper               : 0.00
% 4.95/1.99  Total                : 1.18
% 4.95/1.99  Index Insertion      : 0.00
% 4.95/1.99  Index Deletion       : 0.00
% 4.95/1.99  Index Matching       : 0.00
% 4.95/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
