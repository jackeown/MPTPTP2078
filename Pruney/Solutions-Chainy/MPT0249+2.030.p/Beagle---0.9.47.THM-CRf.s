%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:27 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 119 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 199 expanded)
%              Number of equality atoms :   32 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_50,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_72,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_69])).

tff(c_205,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_224,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_205])).

tff(c_230,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_234,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_230])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_281,plain,(
    ! [C_70,B_71,A_72] :
      ( r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1493,plain,(
    ! [A_1407,B_1408] :
      ( r2_hidden('#skF_2'(A_1407),B_1408)
      | ~ r1_tarski(A_1407,B_1408)
      | k1_xboole_0 = A_1407 ) ),
    inference(resolution,[status(thm)],[c_8,c_281])).

tff(c_20,plain,(
    ! [C_19,A_15] :
      ( C_19 = A_15
      | ~ r2_hidden(C_19,k1_tarski(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1606,plain,(
    ! [A_1516,A_1517] :
      ( A_1516 = '#skF_2'(A_1517)
      | ~ r1_tarski(A_1517,k1_tarski(A_1516))
      | k1_xboole_0 = A_1517 ) ),
    inference(resolution,[status(thm)],[c_1493,c_20])).

tff(c_1628,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_72,c_1606])).

tff(c_1641,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1628])).

tff(c_1649,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1641,c_8])).

tff(c_1654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_234,c_1649])).

tff(c_1655,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_159,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,k2_xboole_0(C_56,B_57))
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_169,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,k1_tarski('#skF_5'))
      | ~ r1_tarski(A_55,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_159])).

tff(c_1757,plain,(
    ! [A_1573] :
      ( r1_tarski(A_1573,'#skF_6')
      | ~ r1_tarski(A_1573,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_169])).

tff(c_1767,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_1757])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1769,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_1767,c_10])).

tff(c_1772,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1769])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_186,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,k1_tarski('#skF_5'))
      | ~ r1_tarski(A_59,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_159])).

tff(c_40,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(A_30,B_31)
      | ~ r1_tarski(k1_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1657,plain,(
    ! [A_1568] :
      ( r2_hidden(A_1568,k1_tarski('#skF_5'))
      | ~ r1_tarski(k1_tarski(A_1568),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_186,c_40])).

tff(c_1828,plain,(
    ! [A_1579] :
      ( A_1579 = '#skF_5'
      | ~ r1_tarski(k1_tarski(A_1579),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1657,c_20])).

tff(c_1856,plain,(
    ! [A_1581] :
      ( A_1581 = '#skF_5'
      | ~ r2_hidden(A_1581,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_1828])).

tff(c_1868,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_8,c_1856])).

tff(c_1873,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1868])).

tff(c_1877,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1873,c_8])).

tff(c_1880,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1877])).

tff(c_1890,plain,(
    ! [B_1582] :
      ( r1_tarski('#skF_6',B_1582)
      | ~ r2_hidden('#skF_5',B_1582) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1655,c_42])).

tff(c_1893,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_1880,c_1890])).

tff(c_1918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1772,c_1893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:59:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.63  
% 3.55/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.63  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 3.55/1.63  
% 3.55/1.63  %Foreground sorts:
% 3.55/1.63  
% 3.55/1.63  
% 3.55/1.63  %Background operators:
% 3.55/1.63  
% 3.55/1.63  
% 3.55/1.63  %Foreground operators:
% 3.55/1.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.55/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.55/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.55/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.55/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.55/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.55/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.55/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.55/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.55/1.63  
% 3.55/1.64  tff(f_86, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.55/1.64  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.55/1.64  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.55/1.64  tff(f_52, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.55/1.64  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.55/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.55/1.64  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.55/1.64  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.55/1.64  tff(c_50, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.55/1.64  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.64  tff(c_48, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.55/1.64  tff(c_42, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.55/1.64  tff(c_52, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.55/1.64  tff(c_69, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.55/1.64  tff(c_72, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_69])).
% 3.55/1.64  tff(c_205, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.64  tff(c_224, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_72, c_205])).
% 3.55/1.64  tff(c_230, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_224])).
% 3.55/1.64  tff(c_234, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_230])).
% 3.55/1.64  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.64  tff(c_281, plain, (![C_70, B_71, A_72]: (r2_hidden(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.64  tff(c_1493, plain, (![A_1407, B_1408]: (r2_hidden('#skF_2'(A_1407), B_1408) | ~r1_tarski(A_1407, B_1408) | k1_xboole_0=A_1407)), inference(resolution, [status(thm)], [c_8, c_281])).
% 3.55/1.64  tff(c_20, plain, (![C_19, A_15]: (C_19=A_15 | ~r2_hidden(C_19, k1_tarski(A_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.64  tff(c_1606, plain, (![A_1516, A_1517]: (A_1516='#skF_2'(A_1517) | ~r1_tarski(A_1517, k1_tarski(A_1516)) | k1_xboole_0=A_1517)), inference(resolution, [status(thm)], [c_1493, c_20])).
% 3.55/1.64  tff(c_1628, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_72, c_1606])).
% 3.55/1.64  tff(c_1641, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_48, c_1628])).
% 3.55/1.64  tff(c_1649, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1641, c_8])).
% 3.55/1.64  tff(c_1654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_234, c_1649])).
% 3.55/1.64  tff(c_1655, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_224])).
% 3.55/1.64  tff(c_159, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, k2_xboole_0(C_56, B_57)) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.55/1.64  tff(c_169, plain, (![A_55]: (r1_tarski(A_55, k1_tarski('#skF_5')) | ~r1_tarski(A_55, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_159])).
% 3.55/1.64  tff(c_1757, plain, (![A_1573]: (r1_tarski(A_1573, '#skF_6') | ~r1_tarski(A_1573, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_169])).
% 3.55/1.64  tff(c_1767, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_14, c_1757])).
% 3.55/1.64  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.64  tff(c_1769, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_1767, c_10])).
% 3.55/1.64  tff(c_1772, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_50, c_1769])).
% 3.55/1.64  tff(c_46, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.55/1.64  tff(c_186, plain, (![A_59]: (r1_tarski(A_59, k1_tarski('#skF_5')) | ~r1_tarski(A_59, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_159])).
% 3.55/1.64  tff(c_40, plain, (![A_30, B_31]: (r2_hidden(A_30, B_31) | ~r1_tarski(k1_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.55/1.64  tff(c_1657, plain, (![A_1568]: (r2_hidden(A_1568, k1_tarski('#skF_5')) | ~r1_tarski(k1_tarski(A_1568), '#skF_7'))), inference(resolution, [status(thm)], [c_186, c_40])).
% 3.55/1.64  tff(c_1828, plain, (![A_1579]: (A_1579='#skF_5' | ~r1_tarski(k1_tarski(A_1579), '#skF_7'))), inference(resolution, [status(thm)], [c_1657, c_20])).
% 3.55/1.64  tff(c_1856, plain, (![A_1581]: (A_1581='#skF_5' | ~r2_hidden(A_1581, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_1828])).
% 3.55/1.64  tff(c_1868, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_8, c_1856])).
% 3.55/1.64  tff(c_1873, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_46, c_1868])).
% 3.55/1.64  tff(c_1877, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1873, c_8])).
% 3.55/1.64  tff(c_1880, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_1877])).
% 3.55/1.64  tff(c_1890, plain, (![B_1582]: (r1_tarski('#skF_6', B_1582) | ~r2_hidden('#skF_5', B_1582))), inference(superposition, [status(thm), theory('equality')], [c_1655, c_42])).
% 3.55/1.64  tff(c_1893, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_1880, c_1890])).
% 3.55/1.64  tff(c_1918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1772, c_1893])).
% 3.55/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.64  
% 3.55/1.64  Inference rules
% 3.55/1.64  ----------------------
% 3.55/1.64  #Ref     : 0
% 3.55/1.64  #Sup     : 292
% 3.55/1.64  #Fact    : 0
% 3.55/1.64  #Define  : 0
% 3.55/1.64  #Split   : 2
% 3.55/1.64  #Chain   : 0
% 3.55/1.64  #Close   : 0
% 3.55/1.64  
% 3.55/1.64  Ordering : KBO
% 3.55/1.64  
% 3.55/1.64  Simplification rules
% 3.55/1.64  ----------------------
% 3.55/1.64  #Subsume      : 22
% 3.55/1.64  #Demod        : 46
% 3.55/1.64  #Tautology    : 85
% 3.55/1.64  #SimpNegUnit  : 22
% 3.55/1.64  #BackRed      : 4
% 3.55/1.64  
% 3.55/1.64  #Partial instantiations: 855
% 3.55/1.64  #Strategies tried      : 1
% 3.55/1.64  
% 3.55/1.64  Timing (in seconds)
% 3.55/1.64  ----------------------
% 3.55/1.64  Preprocessing        : 0.34
% 3.55/1.64  Parsing              : 0.18
% 3.55/1.64  CNF conversion       : 0.03
% 3.55/1.64  Main loop            : 0.50
% 3.55/1.64  Inferencing          : 0.24
% 3.55/1.64  Reduction            : 0.13
% 3.55/1.65  Demodulation         : 0.09
% 3.55/1.65  BG Simplification    : 0.03
% 3.55/1.65  Subsumption          : 0.08
% 3.55/1.65  Abstraction          : 0.02
% 3.55/1.65  MUC search           : 0.00
% 3.55/1.65  Cooper               : 0.00
% 3.55/1.65  Total                : 0.88
% 3.55/1.65  Index Insertion      : 0.00
% 3.55/1.65  Index Deletion       : 0.00
% 3.55/1.65  Index Matching       : 0.00
% 3.55/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
