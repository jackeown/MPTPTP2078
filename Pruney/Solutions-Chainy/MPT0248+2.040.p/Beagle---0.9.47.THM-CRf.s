%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:09 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 121 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 318 expanded)
%              Number of equality atoms :   71 ( 294 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_33,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_48])).

tff(c_10,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_343,plain,(
    ! [B_36,C_37,A_38] :
      ( k2_tarski(B_36,C_37) = A_38
      | k1_tarski(C_37) = A_38
      | k1_tarski(B_36) = A_38
      | k1_xboole_0 = A_38
      | ~ r1_tarski(A_38,k2_tarski(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_356,plain,(
    ! [A_8,A_38] :
      ( k2_tarski(A_8,A_8) = A_38
      | k1_tarski(A_8) = A_38
      | k1_tarski(A_8) = A_38
      | k1_xboole_0 = A_38
      | ~ r1_tarski(A_38,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_343])).

tff(c_2004,plain,(
    ! [A_63,A_64] :
      ( k1_tarski(A_63) = A_64
      | k1_tarski(A_63) = A_64
      | k1_tarski(A_63) = A_64
      | k1_xboole_0 = A_64
      | ~ r1_tarski(A_64,k1_tarski(A_63)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_356])).

tff(c_2014,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_51,c_2004])).

tff(c_2025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_33,c_33,c_33,c_2014])).

tff(c_2026,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2027,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2028,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2027,c_6])).

tff(c_2141,plain,(
    ! [A_78,B_79] :
      ( k2_xboole_0(A_78,B_79) = B_79
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2169,plain,(
    ! [A_5] : k2_xboole_0('#skF_2',A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_2028,c_2141])).

tff(c_2182,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2169,c_30])).

tff(c_2184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2026,c_2182])).

tff(c_2185,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_2186,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2285,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2186,c_28])).

tff(c_2233,plain,(
    ! [B_89,A_90] : k2_xboole_0(B_89,A_90) = k2_xboole_0(A_90,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2191,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_30])).

tff(c_2254,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2233,c_2191])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2289,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2254,c_8])).

tff(c_2586,plain,(
    ! [B_108,C_109,A_110] :
      ( k2_tarski(B_108,C_109) = A_110
      | k1_tarski(C_109) = A_110
      | k1_tarski(B_108) = A_110
      | k1_xboole_0 = A_110
      | ~ r1_tarski(A_110,k2_tarski(B_108,C_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2605,plain,(
    ! [A_8,A_110] :
      ( k2_tarski(A_8,A_8) = A_110
      | k1_tarski(A_8) = A_110
      | k1_tarski(A_8) = A_110
      | k1_xboole_0 = A_110
      | ~ r1_tarski(A_110,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2586])).

tff(c_4197,plain,(
    ! [A_138,A_139] :
      ( k1_tarski(A_138) = A_139
      | k1_tarski(A_138) = A_139
      | k1_tarski(A_138) = A_139
      | k1_xboole_0 = A_139
      | ~ r1_tarski(A_139,k1_tarski(A_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2605])).

tff(c_4204,plain,(
    ! [A_139] :
      ( k1_tarski('#skF_1') = A_139
      | k1_tarski('#skF_1') = A_139
      | k1_tarski('#skF_1') = A_139
      | k1_xboole_0 = A_139
      | ~ r1_tarski(A_139,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_4197])).

tff(c_4769,plain,(
    ! [A_144] :
      ( A_144 = '#skF_2'
      | A_144 = '#skF_2'
      | A_144 = '#skF_2'
      | k1_xboole_0 = A_144
      | ~ r1_tarski(A_144,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2186,c_2186,c_4204])).

tff(c_4776,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2289,c_4769])).

tff(c_4788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2185,c_2285,c_2285,c_2285,c_4776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.79  
% 4.41/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.79  %$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.41/1.79  
% 4.41/1.79  %Foreground sorts:
% 4.41/1.79  
% 4.41/1.79  
% 4.41/1.79  %Background operators:
% 4.41/1.79  
% 4.41/1.79  
% 4.41/1.79  %Foreground operators:
% 4.41/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.41/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.41/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.41/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.41/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.41/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.79  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.41/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.41/1.79  
% 4.41/1.80  tff(f_73, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.41/1.80  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.41/1.80  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.41/1.80  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.41/1.80  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.41/1.80  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.41/1.80  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.41/1.80  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.41/1.80  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 4.41/1.80  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.41/1.80  tff(c_33, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 4.41/1.80  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.41/1.80  tff(c_48, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.41/1.80  tff(c_51, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_48])).
% 4.41/1.80  tff(c_10, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.41/1.80  tff(c_343, plain, (![B_36, C_37, A_38]: (k2_tarski(B_36, C_37)=A_38 | k1_tarski(C_37)=A_38 | k1_tarski(B_36)=A_38 | k1_xboole_0=A_38 | ~r1_tarski(A_38, k2_tarski(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.41/1.80  tff(c_356, plain, (![A_8, A_38]: (k2_tarski(A_8, A_8)=A_38 | k1_tarski(A_8)=A_38 | k1_tarski(A_8)=A_38 | k1_xboole_0=A_38 | ~r1_tarski(A_38, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_343])).
% 4.41/1.80  tff(c_2004, plain, (![A_63, A_64]: (k1_tarski(A_63)=A_64 | k1_tarski(A_63)=A_64 | k1_tarski(A_63)=A_64 | k1_xboole_0=A_64 | ~r1_tarski(A_64, k1_tarski(A_63)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_356])).
% 4.41/1.80  tff(c_2014, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_51, c_2004])).
% 4.41/1.80  tff(c_2025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_33, c_33, c_33, c_2014])).
% 4.41/1.80  tff(c_2026, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 4.41/1.80  tff(c_2027, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 4.41/1.80  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.41/1.80  tff(c_2028, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2027, c_6])).
% 4.41/1.80  tff(c_2141, plain, (![A_78, B_79]: (k2_xboole_0(A_78, B_79)=B_79 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.80  tff(c_2169, plain, (![A_5]: (k2_xboole_0('#skF_2', A_5)=A_5)), inference(resolution, [status(thm)], [c_2028, c_2141])).
% 4.41/1.80  tff(c_2182, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2169, c_30])).
% 4.41/1.80  tff(c_2184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2026, c_2182])).
% 4.41/1.80  tff(c_2185, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 4.41/1.80  tff(c_2186, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 4.41/1.80  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.41/1.80  tff(c_2285, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2186, c_28])).
% 4.41/1.80  tff(c_2233, plain, (![B_89, A_90]: (k2_xboole_0(B_89, A_90)=k2_xboole_0(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.41/1.80  tff(c_2191, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_30])).
% 4.41/1.80  tff(c_2254, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2233, c_2191])).
% 4.41/1.80  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.41/1.80  tff(c_2289, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2254, c_8])).
% 4.41/1.80  tff(c_2586, plain, (![B_108, C_109, A_110]: (k2_tarski(B_108, C_109)=A_110 | k1_tarski(C_109)=A_110 | k1_tarski(B_108)=A_110 | k1_xboole_0=A_110 | ~r1_tarski(A_110, k2_tarski(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.41/1.80  tff(c_2605, plain, (![A_8, A_110]: (k2_tarski(A_8, A_8)=A_110 | k1_tarski(A_8)=A_110 | k1_tarski(A_8)=A_110 | k1_xboole_0=A_110 | ~r1_tarski(A_110, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2586])).
% 4.41/1.80  tff(c_4197, plain, (![A_138, A_139]: (k1_tarski(A_138)=A_139 | k1_tarski(A_138)=A_139 | k1_tarski(A_138)=A_139 | k1_xboole_0=A_139 | ~r1_tarski(A_139, k1_tarski(A_138)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2605])).
% 4.41/1.80  tff(c_4204, plain, (![A_139]: (k1_tarski('#skF_1')=A_139 | k1_tarski('#skF_1')=A_139 | k1_tarski('#skF_1')=A_139 | k1_xboole_0=A_139 | ~r1_tarski(A_139, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2186, c_4197])).
% 4.41/1.80  tff(c_4769, plain, (![A_144]: (A_144='#skF_2' | A_144='#skF_2' | A_144='#skF_2' | k1_xboole_0=A_144 | ~r1_tarski(A_144, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2186, c_2186, c_4204])).
% 4.41/1.80  tff(c_4776, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2289, c_4769])).
% 4.41/1.80  tff(c_4788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2185, c_2285, c_2285, c_2285, c_4776])).
% 4.41/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.80  
% 4.41/1.80  Inference rules
% 4.41/1.80  ----------------------
% 4.41/1.80  #Ref     : 0
% 4.41/1.80  #Sup     : 1155
% 4.41/1.80  #Fact    : 0
% 4.41/1.80  #Define  : 0
% 4.41/1.80  #Split   : 3
% 4.41/1.80  #Chain   : 0
% 4.41/1.80  #Close   : 0
% 4.41/1.80  
% 4.41/1.80  Ordering : KBO
% 4.41/1.80  
% 4.41/1.80  Simplification rules
% 4.41/1.80  ----------------------
% 4.41/1.80  #Subsume      : 84
% 4.41/1.80  #Demod        : 1805
% 4.41/1.80  #Tautology    : 960
% 4.41/1.80  #SimpNegUnit  : 6
% 4.41/1.80  #BackRed      : 6
% 4.41/1.80  
% 4.41/1.80  #Partial instantiations: 0
% 4.41/1.80  #Strategies tried      : 1
% 4.41/1.80  
% 4.41/1.80  Timing (in seconds)
% 4.41/1.80  ----------------------
% 4.41/1.80  Preprocessing        : 0.28
% 4.41/1.80  Parsing              : 0.15
% 4.41/1.80  CNF conversion       : 0.02
% 4.41/1.80  Main loop            : 0.76
% 4.41/1.80  Inferencing          : 0.22
% 4.41/1.80  Reduction            : 0.40
% 4.41/1.80  Demodulation         : 0.34
% 4.41/1.80  BG Simplification    : 0.02
% 4.41/1.80  Subsumption          : 0.08
% 4.41/1.80  Abstraction          : 0.04
% 4.41/1.80  MUC search           : 0.00
% 4.41/1.80  Cooper               : 0.00
% 4.41/1.80  Total                : 1.07
% 4.41/1.80  Index Insertion      : 0.00
% 4.41/1.81  Index Deletion       : 0.00
% 4.41/1.81  Index Matching       : 0.00
% 4.41/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
