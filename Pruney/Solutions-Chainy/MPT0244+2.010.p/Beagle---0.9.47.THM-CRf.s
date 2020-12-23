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
% DateTime   : Thu Dec  3 09:49:57 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 183 expanded)
%              Number of leaves         :   26 (  67 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 328 expanded)
%              Number of equality atoms :   61 ( 175 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_81,plain,(
    k1_tarski('#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_56,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_219,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_221,plain,
    ( k1_tarski('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_219,c_10])).

tff(c_224,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_221])).

tff(c_228,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_224])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_229,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_265,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_2'(A_66),B_67)
      | ~ r1_tarski(A_66,B_67)
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_8,c_229])).

tff(c_36,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_156,plain,(
    ! [D_48,B_49,A_50] :
      ( D_48 = B_49
      | D_48 = A_50
      | ~ r2_hidden(D_48,k2_tarski(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_170,plain,(
    ! [D_48,A_17] :
      ( D_48 = A_17
      | D_48 = A_17
      | ~ r2_hidden(D_48,k1_tarski(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_156])).

tff(c_371,plain,(
    ! [A_79,A_80] :
      ( A_79 = '#skF_2'(A_80)
      | ~ r1_tarski(A_80,k1_tarski(A_79))
      | k1_xboole_0 = A_80 ) ),
    inference(resolution,[status(thm)],[c_265,c_170])).

tff(c_378,plain,
    ( '#skF_2'('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_219,c_371])).

tff(c_394,plain,(
    '#skF_2'('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_378])).

tff(c_405,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_8])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_228,c_405])).

tff(c_411,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_413,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_148,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_414,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_148])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_414])).

tff(c_418,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_425,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_16])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_148])).

tff(c_446,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_449,plain,
    ( k1_tarski('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_446,c_10])).

tff(c_452,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_449])).

tff(c_459,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_452])).

tff(c_482,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_573,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_2'(A_107),B_108)
      | ~ r1_tarski(A_107,B_108)
      | k1_xboole_0 = A_107 ) ),
    inference(resolution,[status(thm)],[c_8,c_482])).

tff(c_518,plain,(
    ! [D_98,B_99,A_100] :
      ( D_98 = B_99
      | D_98 = A_100
      | ~ r2_hidden(D_98,k2_tarski(A_100,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_532,plain,(
    ! [D_98,A_17] :
      ( D_98 = A_17
      | D_98 = A_17
      | ~ r2_hidden(D_98,k1_tarski(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_518])).

tff(c_724,plain,(
    ! [A_120,A_121] :
      ( A_120 = '#skF_2'(A_121)
      | ~ r1_tarski(A_121,k1_tarski(A_120))
      | k1_xboole_0 = A_121 ) ),
    inference(resolution,[status(thm)],[c_573,c_532])).

tff(c_734,plain,
    ( '#skF_2'('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_446,c_724])).

tff(c_751,plain,(
    '#skF_2'('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_734])).

tff(c_762,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_8])).

tff(c_767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_459,c_762])).

tff(c_769,plain,(
    k1_tarski('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_778,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_48])).

tff(c_779,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_782,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_16])).

tff(c_768,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_768])).

tff(c_790,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_790,c_768])).

tff(c_804,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_835,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_804,c_52])).

tff(c_836,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_806,plain,(
    ! [A_10] : r1_tarski('#skF_7',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_16])).

tff(c_838,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_806])).

tff(c_803,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_803])).

tff(c_851,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_853,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_803])).

tff(c_856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.37  
% 2.52/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.37  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 2.52/1.37  
% 2.52/1.37  %Foreground sorts:
% 2.52/1.37  
% 2.52/1.37  
% 2.52/1.37  %Background operators:
% 2.52/1.37  
% 2.52/1.37  
% 2.52/1.37  %Foreground operators:
% 2.52/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.52/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.52/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.52/1.37  
% 2.77/1.39  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.77/1.39  tff(f_74, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.77/1.39  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.77/1.39  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.77/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.77/1.39  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.77/1.39  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.77/1.39  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.39  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.39  tff(c_50, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_80, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_50])).
% 2.77/1.39  tff(c_44, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.77/1.39  tff(c_46, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_81, plain, (k1_tarski('#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_46])).
% 2.77/1.39  tff(c_56, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_219, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.77/1.39  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.39  tff(c_221, plain, (k1_tarski('#skF_8')='#skF_7' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_219, c_10])).
% 2.77/1.39  tff(c_224, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_81, c_221])).
% 2.77/1.39  tff(c_228, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_44, c_224])).
% 2.77/1.39  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.77/1.39  tff(c_229, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.39  tff(c_265, plain, (![A_66, B_67]: (r2_hidden('#skF_2'(A_66), B_67) | ~r1_tarski(A_66, B_67) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_8, c_229])).
% 2.77/1.39  tff(c_36, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.39  tff(c_156, plain, (![D_48, B_49, A_50]: (D_48=B_49 | D_48=A_50 | ~r2_hidden(D_48, k2_tarski(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.39  tff(c_170, plain, (![D_48, A_17]: (D_48=A_17 | D_48=A_17 | ~r2_hidden(D_48, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_156])).
% 2.77/1.39  tff(c_371, plain, (![A_79, A_80]: (A_79='#skF_2'(A_80) | ~r1_tarski(A_80, k1_tarski(A_79)) | k1_xboole_0=A_80)), inference(resolution, [status(thm)], [c_265, c_170])).
% 2.77/1.39  tff(c_378, plain, ('#skF_2'('#skF_7')='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_219, c_371])).
% 2.77/1.39  tff(c_394, plain, ('#skF_2'('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_80, c_378])).
% 2.77/1.39  tff(c_405, plain, (r2_hidden('#skF_8', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_394, c_8])).
% 2.77/1.39  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_228, c_405])).
% 2.77/1.39  tff(c_411, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_56])).
% 2.77/1.39  tff(c_413, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_411])).
% 2.77/1.39  tff(c_54, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_148, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.77/1.39  tff(c_414, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_148])).
% 2.77/1.39  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_414])).
% 2.77/1.39  tff(c_418, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_411])).
% 2.77/1.39  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.77/1.39  tff(c_425, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_16])).
% 2.77/1.39  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_425, c_148])).
% 2.77/1.39  tff(c_446, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_54])).
% 2.77/1.39  tff(c_449, plain, (k1_tarski('#skF_8')='#skF_7' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_446, c_10])).
% 2.77/1.39  tff(c_452, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_81, c_449])).
% 2.77/1.39  tff(c_459, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_44, c_452])).
% 2.77/1.39  tff(c_482, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.39  tff(c_573, plain, (![A_107, B_108]: (r2_hidden('#skF_2'(A_107), B_108) | ~r1_tarski(A_107, B_108) | k1_xboole_0=A_107)), inference(resolution, [status(thm)], [c_8, c_482])).
% 2.77/1.39  tff(c_518, plain, (![D_98, B_99, A_100]: (D_98=B_99 | D_98=A_100 | ~r2_hidden(D_98, k2_tarski(A_100, B_99)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.39  tff(c_532, plain, (![D_98, A_17]: (D_98=A_17 | D_98=A_17 | ~r2_hidden(D_98, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_518])).
% 2.77/1.39  tff(c_724, plain, (![A_120, A_121]: (A_120='#skF_2'(A_121) | ~r1_tarski(A_121, k1_tarski(A_120)) | k1_xboole_0=A_121)), inference(resolution, [status(thm)], [c_573, c_532])).
% 2.77/1.39  tff(c_734, plain, ('#skF_2'('#skF_7')='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_446, c_724])).
% 2.77/1.39  tff(c_751, plain, ('#skF_2'('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_80, c_734])).
% 2.77/1.39  tff(c_762, plain, (r2_hidden('#skF_8', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_751, c_8])).
% 2.77/1.39  tff(c_767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_459, c_762])).
% 2.77/1.39  tff(c_769, plain, (k1_tarski('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_46])).
% 2.77/1.39  tff(c_48, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_778, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_769, c_48])).
% 2.77/1.39  tff(c_779, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_778])).
% 2.77/1.39  tff(c_782, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_779, c_16])).
% 2.77/1.39  tff(c_768, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_46])).
% 2.77/1.39  tff(c_789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_782, c_768])).
% 2.77/1.39  tff(c_790, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_778])).
% 2.77/1.39  tff(c_802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_790, c_768])).
% 2.77/1.39  tff(c_804, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_50])).
% 2.77/1.39  tff(c_52, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_835, plain, (k1_tarski('#skF_6')='#skF_5' | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_804, c_804, c_52])).
% 2.77/1.39  tff(c_836, plain, ('#skF_7'='#skF_5'), inference(splitLeft, [status(thm)], [c_835])).
% 2.77/1.39  tff(c_806, plain, (![A_10]: (r1_tarski('#skF_7', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_804, c_16])).
% 2.77/1.39  tff(c_838, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_806])).
% 2.77/1.39  tff(c_803, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_50])).
% 2.77/1.39  tff(c_850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_838, c_803])).
% 2.77/1.39  tff(c_851, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_835])).
% 2.77/1.39  tff(c_853, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_851, c_803])).
% 2.77/1.39  tff(c_856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_853])).
% 2.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  Inference rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Ref     : 0
% 2.77/1.39  #Sup     : 172
% 2.77/1.39  #Fact    : 0
% 2.77/1.39  #Define  : 0
% 2.77/1.39  #Split   : 8
% 2.77/1.39  #Chain   : 0
% 2.77/1.39  #Close   : 0
% 2.77/1.39  
% 2.77/1.39  Ordering : KBO
% 2.77/1.39  
% 2.77/1.39  Simplification rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Subsume      : 23
% 2.77/1.39  #Demod        : 54
% 2.77/1.39  #Tautology    : 90
% 2.77/1.39  #SimpNegUnit  : 20
% 2.77/1.39  #BackRed      : 18
% 2.77/1.39  
% 2.77/1.39  #Partial instantiations: 0
% 2.77/1.39  #Strategies tried      : 1
% 2.77/1.39  
% 2.77/1.39  Timing (in seconds)
% 2.77/1.39  ----------------------
% 2.77/1.39  Preprocessing        : 0.30
% 2.77/1.39  Parsing              : 0.16
% 2.77/1.39  CNF conversion       : 0.02
% 2.77/1.39  Main loop            : 0.32
% 2.77/1.39  Inferencing          : 0.12
% 2.77/1.39  Reduction            : 0.09
% 2.77/1.39  Demodulation         : 0.06
% 2.77/1.39  BG Simplification    : 0.02
% 2.77/1.39  Subsumption          : 0.06
% 2.77/1.39  Abstraction          : 0.02
% 2.77/1.39  MUC search           : 0.00
% 2.77/1.39  Cooper               : 0.00
% 2.77/1.39  Total                : 0.65
% 2.77/1.39  Index Insertion      : 0.00
% 2.77/1.39  Index Deletion       : 0.00
% 2.77/1.39  Index Matching       : 0.00
% 2.77/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
