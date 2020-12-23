%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:03 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   47 (  66 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 (  93 expanded)
%              Number of equality atoms :   42 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_36,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_103,plain,(
    ! [B_35,A_36] : r2_hidden(B_35,k2_tarski(A_36,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_4])).

tff(c_106,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_103])).

tff(c_236,plain,(
    ! [A_60,B_61,C_62] :
      ( k4_xboole_0(k2_tarski(A_60,B_61),C_62) = k1_xboole_0
      | ~ r2_hidden(B_61,C_62)
      | ~ r2_hidden(A_60,C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_260,plain,(
    ! [A_65,C_66] :
      ( k4_xboole_0(k1_tarski(A_65),C_66) = k1_xboole_0
      | ~ r2_hidden(A_65,C_66)
      | ~ r2_hidden(A_65,C_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_236])).

tff(c_38,plain,(
    ! [B_17] : k4_xboole_0(k1_tarski(B_17),k1_tarski(B_17)) != k1_tarski(B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_278,plain,(
    ! [A_65] :
      ( k1_tarski(A_65) != k1_xboole_0
      | ~ r2_hidden(A_65,k1_tarski(A_65))
      | ~ r2_hidden(A_65,k1_tarski(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_38])).

tff(c_294,plain,(
    ! [A_65] : k1_tarski(A_65) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_106,c_278])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_107,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_120,plain,(
    ! [B_41,A_42] :
      ( k1_xboole_0 = B_41
      | k1_xboole_0 = A_42
      | k2_zfmisc_1(A_42,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_120])).

tff(c_132,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_123])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_132])).

tff(c_298,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_312,plain,(
    ! [B_71,A_72] :
      ( k1_xboole_0 = B_71
      | k1_xboole_0 = A_72
      | k2_zfmisc_1(A_72,B_71) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_315,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_312])).

tff(c_324,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_315])).

tff(c_299,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_329,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_299])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.15/1.30  
% 2.15/1.30  %Foreground sorts:
% 2.15/1.30  
% 2.15/1.30  
% 2.15/1.30  %Background operators:
% 2.15/1.30  
% 2.15/1.30  
% 2.15/1.30  %Foreground operators:
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.15/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.15/1.30  
% 2.15/1.31  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.15/1.31  tff(f_73, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.15/1.31  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.31  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.31  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.15/1.31  tff(f_63, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 2.15/1.31  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.15/1.31  tff(c_36, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.31  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.15/1.31  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.15/1.31  tff(c_85, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.15/1.31  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.15/1.31  tff(c_103, plain, (![B_35, A_36]: (r2_hidden(B_35, k2_tarski(A_36, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_4])).
% 2.15/1.31  tff(c_106, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_103])).
% 2.15/1.31  tff(c_236, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k2_tarski(A_60, B_61), C_62)=k1_xboole_0 | ~r2_hidden(B_61, C_62) | ~r2_hidden(A_60, C_62))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.31  tff(c_260, plain, (![A_65, C_66]: (k4_xboole_0(k1_tarski(A_65), C_66)=k1_xboole_0 | ~r2_hidden(A_65, C_66) | ~r2_hidden(A_65, C_66))), inference(superposition, [status(thm), theory('equality')], [c_26, c_236])).
% 2.15/1.31  tff(c_38, plain, (![B_17]: (k4_xboole_0(k1_tarski(B_17), k1_tarski(B_17))!=k1_tarski(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.31  tff(c_278, plain, (![A_65]: (k1_tarski(A_65)!=k1_xboole_0 | ~r2_hidden(A_65, k1_tarski(A_65)) | ~r2_hidden(A_65, k1_tarski(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_38])).
% 2.15/1.31  tff(c_294, plain, (![A_65]: (k1_tarski(A_65)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_106, c_278])).
% 2.15/1.31  tff(c_48, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.15/1.31  tff(c_107, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.15/1.31  tff(c_120, plain, (![B_41, A_42]: (k1_xboole_0=B_41 | k1_xboole_0=A_42 | k2_zfmisc_1(A_42, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.31  tff(c_123, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_107, c_120])).
% 2.15/1.31  tff(c_132, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_123])).
% 2.15/1.31  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_294, c_132])).
% 2.15/1.31  tff(c_298, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.15/1.31  tff(c_312, plain, (![B_71, A_72]: (k1_xboole_0=B_71 | k1_xboole_0=A_72 | k2_zfmisc_1(A_72, B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.31  tff(c_315, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_298, c_312])).
% 2.15/1.31  tff(c_324, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_315])).
% 2.15/1.31  tff(c_299, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.15/1.31  tff(c_329, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_324, c_299])).
% 2.15/1.31  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_329])).
% 2.15/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  Inference rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Ref     : 0
% 2.15/1.31  #Sup     : 64
% 2.15/1.31  #Fact    : 0
% 2.15/1.31  #Define  : 0
% 2.15/1.31  #Split   : 1
% 2.15/1.31  #Chain   : 0
% 2.15/1.31  #Close   : 0
% 2.15/1.31  
% 2.15/1.31  Ordering : KBO
% 2.15/1.31  
% 2.15/1.31  Simplification rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Subsume      : 5
% 2.15/1.31  #Demod        : 17
% 2.15/1.31  #Tautology    : 43
% 2.15/1.31  #SimpNegUnit  : 5
% 2.15/1.31  #BackRed      : 4
% 2.15/1.31  
% 2.15/1.31  #Partial instantiations: 0
% 2.15/1.31  #Strategies tried      : 1
% 2.15/1.31  
% 2.15/1.31  Timing (in seconds)
% 2.15/1.31  ----------------------
% 2.15/1.32  Preprocessing        : 0.32
% 2.15/1.32  Parsing              : 0.16
% 2.15/1.32  CNF conversion       : 0.02
% 2.15/1.32  Main loop            : 0.23
% 2.15/1.32  Inferencing          : 0.08
% 2.15/1.32  Reduction            : 0.07
% 2.15/1.32  Demodulation         : 0.05
% 2.15/1.32  BG Simplification    : 0.02
% 2.15/1.32  Subsumption          : 0.05
% 2.15/1.32  Abstraction          : 0.01
% 2.15/1.32  MUC search           : 0.00
% 2.15/1.32  Cooper               : 0.00
% 2.15/1.32  Total                : 0.58
% 2.15/1.32  Index Insertion      : 0.00
% 2.15/1.32  Index Deletion       : 0.00
% 2.15/1.32  Index Matching       : 0.00
% 2.15/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
