%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:15 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 131 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 182 expanded)
%              Number of equality atoms :   24 (  90 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_68,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_5'),k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_70])).

tff(c_256,plain,(
    ! [B_68,A_69] :
      ( k1_tarski(B_68) = A_69
      | k1_xboole_0 = A_69
      | ~ r1_tarski(A_69,k1_tarski(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_267,plain,
    ( k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7')
    | k2_tarski('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_256])).

tff(c_292,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_103,plain,(
    ! [B_49,A_50] : k2_tarski(B_49,A_50) = k2_tarski(A_50,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_26,B_27] : r1_tarski(k1_tarski(A_26),k2_tarski(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_118,plain,(
    ! [A_50,B_49] : r1_tarski(k1_tarski(A_50),k2_tarski(B_49,A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_64])).

tff(c_305,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_118])).

tff(c_62,plain,(
    ! [B_25] : r1_tarski(k1_xboole_0,k1_tarski(B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_200,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_214,plain,(
    ! [B_25] :
      ( k1_tarski(B_25) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_25),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_62,c_200])).

tff(c_323,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_305,c_214])).

tff(c_66,plain,(
    ! [B_29,A_28] :
      ( B_29 = A_28
      | ~ r1_tarski(k1_tarski(A_28),k1_tarski(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_341,plain,(
    ! [B_29] :
      ( B_29 = '#skF_5'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_66])).

tff(c_385,plain,(
    ! [B_77] : B_77 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_341])).

tff(c_212,plain,
    ( k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7')
    | ~ r1_tarski(k1_tarski('#skF_7'),k2_tarski('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_71,c_200])).

tff(c_219,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),k2_tarski('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_293,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_219])).

tff(c_397,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_293])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_323,c_397])).

tff(c_472,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_475,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_219])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_475])).

tff(c_480,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_487,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_118])).

tff(c_504,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_487,c_66])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n008.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:58:00 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.30  
% 2.26/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.30  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.26/1.30  
% 2.26/1.30  %Foreground sorts:
% 2.26/1.30  
% 2.26/1.30  
% 2.26/1.30  %Background operators:
% 2.26/1.30  
% 2.26/1.30  
% 2.26/1.30  %Foreground operators:
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.26/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.26/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.26/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.26/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.26/1.30  
% 2.26/1.31  tff(f_80, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.26/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.26/1.31  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.26/1.31  tff(f_69, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.26/1.31  tff(f_71, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.26/1.31  tff(f_75, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.26/1.31  tff(c_68, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.26/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.31  tff(c_8, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.31  tff(c_70, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.26/1.31  tff(c_71, plain, (r1_tarski(k2_tarski('#skF_6', '#skF_5'), k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_70])).
% 2.26/1.31  tff(c_256, plain, (![B_68, A_69]: (k1_tarski(B_68)=A_69 | k1_xboole_0=A_69 | ~r1_tarski(A_69, k1_tarski(B_68)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.26/1.31  tff(c_267, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7') | k2_tarski('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_256])).
% 2.26/1.31  tff(c_292, plain, (k2_tarski('#skF_6', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_267])).
% 2.26/1.31  tff(c_103, plain, (![B_49, A_50]: (k2_tarski(B_49, A_50)=k2_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.31  tff(c_64, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), k2_tarski(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.26/1.31  tff(c_118, plain, (![A_50, B_49]: (r1_tarski(k1_tarski(A_50), k2_tarski(B_49, A_50)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_64])).
% 2.26/1.31  tff(c_305, plain, (r1_tarski(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_292, c_118])).
% 2.26/1.31  tff(c_62, plain, (![B_25]: (r1_tarski(k1_xboole_0, k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.26/1.31  tff(c_200, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.31  tff(c_214, plain, (![B_25]: (k1_tarski(B_25)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_25), k1_xboole_0))), inference(resolution, [status(thm)], [c_62, c_200])).
% 2.26/1.31  tff(c_323, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_305, c_214])).
% 2.26/1.31  tff(c_66, plain, (![B_29, A_28]: (B_29=A_28 | ~r1_tarski(k1_tarski(A_28), k1_tarski(B_29)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.26/1.31  tff(c_341, plain, (![B_29]: (B_29='#skF_5' | ~r1_tarski(k1_xboole_0, k1_tarski(B_29)))), inference(superposition, [status(thm), theory('equality')], [c_323, c_66])).
% 2.26/1.31  tff(c_385, plain, (![B_77]: (B_77='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_341])).
% 2.26/1.31  tff(c_212, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski('#skF_7'), k2_tarski('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_71, c_200])).
% 2.26/1.31  tff(c_219, plain, (~r1_tarski(k1_tarski('#skF_7'), k2_tarski('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_212])).
% 2.26/1.31  tff(c_293, plain, (~r1_tarski(k1_tarski('#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_292, c_219])).
% 2.26/1.31  tff(c_397, plain, (~r1_tarski(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_385, c_293])).
% 2.26/1.31  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_323, c_397])).
% 2.26/1.31  tff(c_472, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_267])).
% 2.26/1.31  tff(c_475, plain, (~r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_472, c_219])).
% 2.26/1.31  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_475])).
% 2.26/1.31  tff(c_480, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_212])).
% 2.26/1.31  tff(c_487, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_480, c_118])).
% 2.26/1.31  tff(c_504, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_487, c_66])).
% 2.26/1.31  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_504])).
% 2.26/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.31  
% 2.26/1.31  Inference rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Ref     : 0
% 2.26/1.31  #Sup     : 121
% 2.26/1.31  #Fact    : 0
% 2.26/1.31  #Define  : 0
% 2.26/1.31  #Split   : 2
% 2.26/1.31  #Chain   : 0
% 2.26/1.31  #Close   : 0
% 2.26/1.31  
% 2.26/1.31  Ordering : KBO
% 2.26/1.31  
% 2.26/1.31  Simplification rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Subsume      : 6
% 2.26/1.31  #Demod        : 37
% 2.26/1.31  #Tautology    : 53
% 2.26/1.31  #SimpNegUnit  : 1
% 2.26/1.31  #BackRed      : 7
% 2.26/1.31  
% 2.26/1.31  #Partial instantiations: 30
% 2.26/1.31  #Strategies tried      : 1
% 2.26/1.31  
% 2.26/1.31  Timing (in seconds)
% 2.26/1.31  ----------------------
% 2.26/1.31  Preprocessing        : 0.30
% 2.26/1.31  Parsing              : 0.15
% 2.26/1.31  CNF conversion       : 0.02
% 2.26/1.31  Main loop            : 0.27
% 2.26/1.31  Inferencing          : 0.10
% 2.26/1.31  Reduction            : 0.09
% 2.26/1.31  Demodulation         : 0.07
% 2.26/1.31  BG Simplification    : 0.02
% 2.26/1.31  Subsumption          : 0.05
% 2.26/1.31  Abstraction          : 0.01
% 2.26/1.31  MUC search           : 0.00
% 2.26/1.31  Cooper               : 0.00
% 2.26/1.31  Total                : 0.59
% 2.26/1.31  Index Insertion      : 0.00
% 2.26/1.31  Index Deletion       : 0.00
% 2.26/1.31  Index Matching       : 0.00
% 2.26/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
