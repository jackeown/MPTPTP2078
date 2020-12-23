%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:02 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  71 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_67,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_50,plain,(
    ! [B_41] : k2_zfmisc_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_98,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_136,plain,(
    ! [B_64,A_65] :
      ( k1_xboole_0 = B_64
      | k1_xboole_0 = A_65
      | k2_zfmisc_1(A_65,B_64) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_139,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_136])).

tff(c_148,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_139])).

tff(c_32,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_113,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [E_48,A_49,B_50] : r2_hidden(E_48,k1_enumset1(A_49,B_50,E_48)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_49,B_50,E_48] : ~ v1_xboole_0(k1_enumset1(A_49,B_50,E_48)) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_133,plain,(
    ! [A_62,B_63] : ~ v1_xboole_0(k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_96])).

tff(c_159,plain,(
    ! [A_66] : ~ v1_xboole_0(k1_tarski(A_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_133])).

tff(c_161,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_159])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_165,plain,(
    k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_205,plain,(
    ! [B_78,A_79] :
      ( k1_xboole_0 = B_78
      | k1_xboole_0 = A_79
      | k2_zfmisc_1(A_79,B_78) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_208,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_205])).

tff(c_217,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_208])).

tff(c_166,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_222,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_166])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:08:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.35  
% 2.16/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.35  %$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.16/1.35  
% 2.16/1.35  %Foreground sorts:
% 2.16/1.35  
% 2.16/1.35  
% 2.16/1.35  %Background operators:
% 2.16/1.35  
% 2.16/1.35  
% 2.16/1.35  %Foreground operators:
% 2.16/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.16/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.16/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.35  
% 2.16/1.36  tff(f_67, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.16/1.36  tff(f_77, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.16/1.36  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.16/1.36  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.16/1.36  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.16/1.36  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.16/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.16/1.36  tff(c_50, plain, (![B_41]: (k2_zfmisc_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.36  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.16/1.36  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.36  tff(c_52, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.16/1.36  tff(c_98, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 2.16/1.36  tff(c_136, plain, (![B_64, A_65]: (k1_xboole_0=B_64 | k1_xboole_0=A_65 | k2_zfmisc_1(A_65, B_64)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.36  tff(c_139, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98, c_136])).
% 2.16/1.36  tff(c_148, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_139])).
% 2.16/1.36  tff(c_32, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.36  tff(c_113, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.36  tff(c_92, plain, (![E_48, A_49, B_50]: (r2_hidden(E_48, k1_enumset1(A_49, B_50, E_48)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.36  tff(c_96, plain, (![A_49, B_50, E_48]: (~v1_xboole_0(k1_enumset1(A_49, B_50, E_48)))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.16/1.36  tff(c_133, plain, (![A_62, B_63]: (~v1_xboole_0(k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_96])).
% 2.16/1.36  tff(c_159, plain, (![A_66]: (~v1_xboole_0(k1_tarski(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_133])).
% 2.16/1.36  tff(c_161, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_159])).
% 2.16/1.36  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_161])).
% 2.16/1.36  tff(c_165, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.16/1.36  tff(c_205, plain, (![B_78, A_79]: (k1_xboole_0=B_78 | k1_xboole_0=A_79 | k2_zfmisc_1(A_79, B_78)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.36  tff(c_208, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_165, c_205])).
% 2.16/1.36  tff(c_217, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_208])).
% 2.16/1.36  tff(c_166, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.16/1.36  tff(c_222, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_217, c_166])).
% 2.16/1.36  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_222])).
% 2.16/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.36  
% 2.16/1.36  Inference rules
% 2.16/1.36  ----------------------
% 2.16/1.36  #Ref     : 0
% 2.16/1.36  #Sup     : 41
% 2.16/1.36  #Fact    : 0
% 2.16/1.36  #Define  : 0
% 2.16/1.36  #Split   : 1
% 2.16/1.36  #Chain   : 0
% 2.16/1.36  #Close   : 0
% 2.16/1.36  
% 2.16/1.36  Ordering : KBO
% 2.16/1.36  
% 2.16/1.36  Simplification rules
% 2.16/1.36  ----------------------
% 2.16/1.36  #Subsume      : 4
% 2.16/1.36  #Demod        : 6
% 2.16/1.36  #Tautology    : 24
% 2.16/1.36  #SimpNegUnit  : 2
% 2.16/1.36  #BackRed      : 3
% 2.16/1.36  
% 2.16/1.36  #Partial instantiations: 0
% 2.16/1.36  #Strategies tried      : 1
% 2.16/1.36  
% 2.16/1.36  Timing (in seconds)
% 2.16/1.36  ----------------------
% 2.16/1.36  Preprocessing        : 0.38
% 2.16/1.36  Parsing              : 0.19
% 2.16/1.36  CNF conversion       : 0.03
% 2.16/1.36  Main loop            : 0.16
% 2.16/1.36  Inferencing          : 0.05
% 2.16/1.36  Reduction            : 0.05
% 2.16/1.36  Demodulation         : 0.03
% 2.16/1.36  BG Simplification    : 0.02
% 2.16/1.36  Subsumption          : 0.04
% 2.16/1.36  Abstraction          : 0.01
% 2.16/1.37  MUC search           : 0.00
% 2.16/1.37  Cooper               : 0.00
% 2.16/1.37  Total                : 0.57
% 2.16/1.37  Index Insertion      : 0.00
% 2.16/1.37  Index Deletion       : 0.00
% 2.16/1.37  Index Matching       : 0.00
% 2.16/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
