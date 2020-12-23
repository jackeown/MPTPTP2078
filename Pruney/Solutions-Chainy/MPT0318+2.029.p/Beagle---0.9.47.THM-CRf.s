%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:05 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  70 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_28,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_97,plain,(
    ! [A_29,B_30] : k4_xboole_0(k1_tarski(A_29),k2_tarski(A_29,B_30)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_107,plain,(
    ! [A_31] : k4_xboole_0(k1_tarski(A_31),k1_tarski(A_31)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_97])).

tff(c_34,plain,(
    ! [C_16,B_15] : ~ r2_hidden(C_16,k4_xboole_0(B_15,k1_tarski(C_16))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    ! [A_31] : ~ r2_hidden(A_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_34])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_83,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_118,plain,(
    ! [B_33,A_34] :
      ( k1_xboole_0 = B_33
      | k1_xboole_0 = A_34
      | k2_zfmisc_1(A_34,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_121,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_118])).

tff(c_130,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_121])).

tff(c_65,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_4])).

tff(c_152,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_71])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_152])).

tff(c_159,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_195,plain,(
    ! [B_41,A_42] :
      ( k1_xboole_0 = B_41
      | k1_xboole_0 = A_42
      | k2_zfmisc_1(A_42,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_198,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_195])).

tff(c_207,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_198])).

tff(c_160,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_212,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_160])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.17  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.84/1.17  
% 1.84/1.17  %Foreground sorts:
% 1.84/1.17  
% 1.84/1.17  
% 1.84/1.17  %Background operators:
% 1.84/1.17  
% 1.84/1.17  
% 1.84/1.17  %Foreground operators:
% 1.84/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.17  
% 1.84/1.18  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.84/1.18  tff(f_63, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.84/1.18  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.84/1.18  tff(f_46, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.84/1.18  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.84/1.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.84/1.18  tff(c_28, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.18  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.18  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.18  tff(c_97, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), k2_tarski(A_29, B_30))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.18  tff(c_107, plain, (![A_31]: (k4_xboole_0(k1_tarski(A_31), k1_tarski(A_31))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_97])).
% 1.84/1.18  tff(c_34, plain, (![C_16, B_15]: (~r2_hidden(C_16, k4_xboole_0(B_15, k1_tarski(C_16))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.18  tff(c_112, plain, (![A_31]: (~r2_hidden(A_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_107, c_34])).
% 1.84/1.18  tff(c_38, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.84/1.18  tff(c_83, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 1.84/1.18  tff(c_118, plain, (![B_33, A_34]: (k1_xboole_0=B_33 | k1_xboole_0=A_34 | k2_zfmisc_1(A_34, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.18  tff(c_121, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_83, c_118])).
% 1.84/1.18  tff(c_130, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_121])).
% 1.84/1.18  tff(c_65, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.18  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.18  tff(c_71, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_4])).
% 1.84/1.18  tff(c_152, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_71])).
% 1.84/1.18  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_152])).
% 1.84/1.18  tff(c_159, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 1.84/1.18  tff(c_195, plain, (![B_41, A_42]: (k1_xboole_0=B_41 | k1_xboole_0=A_42 | k2_zfmisc_1(A_42, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.18  tff(c_198, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_159, c_195])).
% 1.84/1.18  tff(c_207, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_198])).
% 1.84/1.18  tff(c_160, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 1.84/1.18  tff(c_212, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_207, c_160])).
% 1.84/1.18  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_212])).
% 1.84/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  Inference rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Ref     : 0
% 1.84/1.18  #Sup     : 43
% 1.84/1.18  #Fact    : 0
% 1.84/1.18  #Define  : 0
% 1.84/1.18  #Split   : 1
% 1.84/1.18  #Chain   : 0
% 1.84/1.18  #Close   : 0
% 1.84/1.18  
% 1.84/1.18  Ordering : KBO
% 1.84/1.18  
% 1.84/1.18  Simplification rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Subsume      : 0
% 1.84/1.18  #Demod        : 8
% 1.84/1.18  #Tautology    : 31
% 1.84/1.18  #SimpNegUnit  : 3
% 1.84/1.18  #BackRed      : 3
% 1.84/1.18  
% 1.84/1.18  #Partial instantiations: 0
% 1.84/1.18  #Strategies tried      : 1
% 1.84/1.18  
% 1.84/1.18  Timing (in seconds)
% 1.84/1.18  ----------------------
% 1.92/1.18  Preprocessing        : 0.29
% 1.92/1.18  Parsing              : 0.15
% 1.92/1.18  CNF conversion       : 0.02
% 1.92/1.18  Main loop            : 0.14
% 1.92/1.18  Inferencing          : 0.04
% 1.92/1.18  Reduction            : 0.05
% 1.92/1.18  Demodulation         : 0.04
% 1.92/1.18  BG Simplification    : 0.01
% 1.92/1.18  Subsumption          : 0.03
% 1.92/1.18  Abstraction          : 0.01
% 1.92/1.18  MUC search           : 0.00
% 1.92/1.18  Cooper               : 0.00
% 1.92/1.18  Total                : 0.45
% 1.92/1.18  Index Insertion      : 0.00
% 1.92/1.18  Index Deletion       : 0.00
% 1.92/1.18  Index Matching       : 0.00
% 1.92/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
