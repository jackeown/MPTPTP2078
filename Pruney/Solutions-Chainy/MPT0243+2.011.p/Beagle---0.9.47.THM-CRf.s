%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:55 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 239 expanded)
%              Number of leaves         :   29 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 423 expanded)
%              Number of equality atoms :   12 (  98 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_73,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,(
    ! [B_40,A_39] : r2_hidden(B_40,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_26])).

tff(c_66,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | r1_tarski(k2_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_99,plain,(
    r1_tarski(k2_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_100,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    k3_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k2_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_99,c_100])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_131,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,'#skF_10')
      | ~ r2_hidden(D_57,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_141,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_79,c_131])).

tff(c_28,plain,(
    ! [E_18,A_12,C_14] : r2_hidden(E_18,k1_enumset1(A_12,E_18,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    ! [A_39,B_40] : r2_hidden(A_39,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_28])).

tff(c_140,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_82,c_131])).

tff(c_60,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_143,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_60])).

tff(c_144,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_144])).

tff(c_147,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_56,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_tarski(A_26),B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_62,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_151,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_141,c_62])).

tff(c_48,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_180,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_tarski(k2_xboole_0(A_66,C_67),B_68)
      | ~ r1_tarski(C_67,B_68)
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_292,plain,(
    ! [A_82,B_83,B_84] :
      ( r1_tarski(k2_tarski(A_82,B_83),B_84)
      | ~ r1_tarski(k1_tarski(B_83),B_84)
      | ~ r1_tarski(k1_tarski(A_82),B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_180])).

tff(c_58,plain,
    ( ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_178,plain,(
    ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_141,c_58])).

tff(c_299,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7')
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_292,c_178])).

tff(c_301,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_304,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_301])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_304])).

tff(c_309,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_313,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_309])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_313])).

tff(c_318,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_319,plain,(
    ~ r1_tarski(k2_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_68,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | r1_tarski(k2_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_336,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_68])).

tff(c_377,plain,(
    ! [A_106,C_107,B_108] :
      ( r1_tarski(k2_xboole_0(A_106,C_107),B_108)
      | ~ r1_tarski(C_107,B_108)
      | ~ r1_tarski(A_106,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_415,plain,(
    ! [A_116,B_117,B_118] :
      ( r1_tarski(k2_tarski(A_116,B_117),B_118)
      | ~ r1_tarski(k1_tarski(B_117),B_118)
      | ~ r1_tarski(k1_tarski(A_116),B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_377])).

tff(c_64,plain,
    ( ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_7')
    | r1_tarski(k2_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_363,plain,(
    ~ r1_tarski(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_64])).

tff(c_425,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7')
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_415,c_363])).

tff(c_428,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_431,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_428])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_431])).

tff(c_436,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_436])).

tff(c_444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:39:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.36  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.48/1.36  
% 2.48/1.36  %Foreground sorts:
% 2.48/1.36  
% 2.48/1.36  
% 2.48/1.36  %Background operators:
% 2.48/1.36  
% 2.48/1.36  
% 2.48/1.36  %Foreground operators:
% 2.48/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.48/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.36  tff('#skF_10', type, '#skF_10': $i).
% 2.48/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.48/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.48/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.48/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.48/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.36  
% 2.77/1.38  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.77/1.38  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.77/1.38  tff(f_76, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.77/1.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.77/1.38  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.77/1.38  tff(f_69, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.77/1.38  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.77/1.38  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.77/1.38  tff(c_73, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.38  tff(c_26, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.38  tff(c_79, plain, (![B_40, A_39]: (r2_hidden(B_40, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_26])).
% 2.77/1.38  tff(c_66, plain, (r2_hidden('#skF_6', '#skF_7') | r1_tarski(k2_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.38  tff(c_99, plain, (r1_tarski(k2_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(splitLeft, [status(thm)], [c_66])).
% 2.77/1.38  tff(c_100, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.38  tff(c_107, plain, (k3_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k2_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_99, c_100])).
% 2.77/1.38  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.77/1.38  tff(c_131, plain, (![D_57]: (r2_hidden(D_57, '#skF_10') | ~r2_hidden(D_57, k2_tarski('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 2.77/1.38  tff(c_141, plain, (r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_79, c_131])).
% 2.77/1.38  tff(c_28, plain, (![E_18, A_12, C_14]: (r2_hidden(E_18, k1_enumset1(A_12, E_18, C_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.38  tff(c_82, plain, (![A_39, B_40]: (r2_hidden(A_39, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_28])).
% 2.77/1.38  tff(c_140, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_82, c_131])).
% 2.77/1.38  tff(c_60, plain, (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.38  tff(c_143, plain, (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_60])).
% 2.77/1.38  tff(c_144, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_143])).
% 2.77/1.38  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_144])).
% 2.77/1.38  tff(c_147, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_143])).
% 2.77/1.38  tff(c_56, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), B_27) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.77/1.38  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.38  tff(c_151, plain, (r2_hidden('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_141, c_62])).
% 2.77/1.38  tff(c_48, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.38  tff(c_180, plain, (![A_66, C_67, B_68]: (r1_tarski(k2_xboole_0(A_66, C_67), B_68) | ~r1_tarski(C_67, B_68) | ~r1_tarski(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.38  tff(c_292, plain, (![A_82, B_83, B_84]: (r1_tarski(k2_tarski(A_82, B_83), B_84) | ~r1_tarski(k1_tarski(B_83), B_84) | ~r1_tarski(k1_tarski(A_82), B_84))), inference(superposition, [status(thm), theory('equality')], [c_48, c_180])).
% 2.77/1.38  tff(c_58, plain, (~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.38  tff(c_178, plain, (~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_141, c_58])).
% 2.77/1.38  tff(c_299, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7') | ~r1_tarski(k1_tarski('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_292, c_178])).
% 2.77/1.38  tff(c_301, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_299])).
% 2.77/1.38  tff(c_304, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_301])).
% 2.77/1.38  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_304])).
% 2.77/1.38  tff(c_309, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_299])).
% 2.77/1.38  tff(c_313, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_309])).
% 2.77/1.38  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_313])).
% 2.77/1.38  tff(c_318, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_66])).
% 2.77/1.38  tff(c_319, plain, (~r1_tarski(k2_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(splitRight, [status(thm)], [c_66])).
% 2.77/1.38  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_7') | r1_tarski(k2_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.38  tff(c_336, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_319, c_68])).
% 2.77/1.38  tff(c_377, plain, (![A_106, C_107, B_108]: (r1_tarski(k2_xboole_0(A_106, C_107), B_108) | ~r1_tarski(C_107, B_108) | ~r1_tarski(A_106, B_108))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.38  tff(c_415, plain, (![A_116, B_117, B_118]: (r1_tarski(k2_tarski(A_116, B_117), B_118) | ~r1_tarski(k1_tarski(B_117), B_118) | ~r1_tarski(k1_tarski(A_116), B_118))), inference(superposition, [status(thm), theory('equality')], [c_48, c_377])).
% 2.77/1.38  tff(c_64, plain, (~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_7') | r1_tarski(k2_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.38  tff(c_363, plain, (~r1_tarski(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_319, c_64])).
% 2.77/1.38  tff(c_425, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7') | ~r1_tarski(k1_tarski('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_415, c_363])).
% 2.77/1.38  tff(c_428, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_425])).
% 2.77/1.38  tff(c_431, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_428])).
% 2.77/1.38  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_336, c_431])).
% 2.77/1.38  tff(c_436, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_425])).
% 2.77/1.38  tff(c_440, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_436])).
% 2.77/1.38  tff(c_444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_440])).
% 2.77/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  Inference rules
% 2.77/1.38  ----------------------
% 2.77/1.38  #Ref     : 0
% 2.77/1.38  #Sup     : 75
% 2.77/1.38  #Fact    : 0
% 2.77/1.38  #Define  : 0
% 2.77/1.38  #Split   : 4
% 2.77/1.38  #Chain   : 0
% 2.77/1.38  #Close   : 0
% 2.77/1.38  
% 2.77/1.38  Ordering : KBO
% 2.77/1.38  
% 2.77/1.38  Simplification rules
% 2.77/1.38  ----------------------
% 2.77/1.38  #Subsume      : 1
% 2.77/1.38  #Demod        : 16
% 2.77/1.38  #Tautology    : 43
% 2.77/1.38  #SimpNegUnit  : 2
% 2.77/1.38  #BackRed      : 0
% 2.77/1.38  
% 2.77/1.38  #Partial instantiations: 0
% 2.77/1.38  #Strategies tried      : 1
% 2.77/1.38  
% 2.77/1.38  Timing (in seconds)
% 2.77/1.38  ----------------------
% 2.77/1.38  Preprocessing        : 0.33
% 2.77/1.38  Parsing              : 0.16
% 2.77/1.38  CNF conversion       : 0.03
% 2.77/1.38  Main loop            : 0.30
% 2.77/1.38  Inferencing          : 0.11
% 2.77/1.38  Reduction            : 0.08
% 2.77/1.38  Demodulation         : 0.06
% 2.77/1.38  BG Simplification    : 0.02
% 2.77/1.39  Subsumption          : 0.06
% 2.77/1.39  Abstraction          : 0.02
% 2.77/1.39  MUC search           : 0.00
% 2.77/1.39  Cooper               : 0.00
% 2.77/1.39  Total                : 0.66
% 2.77/1.39  Index Insertion      : 0.00
% 2.77/1.39  Index Deletion       : 0.00
% 2.77/1.39  Index Matching       : 0.00
% 2.77/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
