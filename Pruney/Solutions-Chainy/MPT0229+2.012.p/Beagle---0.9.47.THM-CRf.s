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
% DateTime   : Thu Dec  3 09:48:55 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   49 (  75 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 ( 105 expanded)
%              Number of equality atoms :   36 (  71 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_48,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,(
    ! [B_54,A_55] :
      ( k1_tarski(B_54) = A_55
      | k1_xboole_0 = A_55
      | ~ r1_tarski(A_55,k1_tarski(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,
    ( k1_tarski('#skF_3') = k1_tarski('#skF_4')
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_139,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,B_47)
      | k4_xboole_0(A_46,B_47) != A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [B_24] : ~ r1_xboole_0(k1_tarski(B_24),k1_tarski(B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_108,plain,(
    ! [B_24] : k4_xboole_0(k1_tarski(B_24),k1_tarski(B_24)) != k1_tarski(B_24) ),
    inference(resolution,[status(thm)],[c_104,c_46])).

tff(c_148,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_108])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_2,c_139,c_148])).

tff(c_175,plain,(
    k1_tarski('#skF_3') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_32,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [E_10,B_5,C_6] : r2_hidden(E_10,k1_enumset1(E_10,B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,(
    ! [A_41,B_42] : r2_hidden(A_41,k2_tarski(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_14])).

tff(c_96,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_93])).

tff(c_192,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_96])).

tff(c_34,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_227,plain,(
    ! [E_60,C_61,B_62,A_63] :
      ( E_60 = C_61
      | E_60 = B_62
      | E_60 = A_63
      | ~ r2_hidden(E_60,k1_enumset1(A_63,B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_246,plain,(
    ! [E_64,B_65,A_66] :
      ( E_64 = B_65
      | E_64 = A_66
      | E_64 = A_66
      | ~ r2_hidden(E_64,k2_tarski(A_66,B_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_227])).

tff(c_261,plain,(
    ! [E_71,A_72] :
      ( E_71 = A_72
      | E_71 = A_72
      | E_71 = A_72
      | ~ r2_hidden(E_71,k1_tarski(A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_246])).

tff(c_264,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_192,c_261])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_48,c_264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.04/1.26  
% 2.04/1.26  %Foreground sorts:
% 2.04/1.26  
% 2.04/1.26  
% 2.04/1.26  %Background operators:
% 2.04/1.26  
% 2.04/1.26  
% 2.04/1.26  %Foreground operators:
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.04/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.04/1.26  
% 2.04/1.27  tff(f_70, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.04/1.27  tff(f_60, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.04/1.27  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.04/1.27  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.04/1.27  tff(f_65, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.04/1.27  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.27  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.04/1.27  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.04/1.27  tff(c_48, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.27  tff(c_50, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.27  tff(c_124, plain, (![B_54, A_55]: (k1_tarski(B_54)=A_55 | k1_xboole_0=A_55 | ~r1_tarski(A_55, k1_tarski(B_54)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.04/1.27  tff(c_136, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4') | k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_124])).
% 2.04/1.27  tff(c_139, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_136])).
% 2.04/1.27  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.27  tff(c_104, plain, (![A_46, B_47]: (r1_xboole_0(A_46, B_47) | k4_xboole_0(A_46, B_47)!=A_46)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.27  tff(c_46, plain, (![B_24]: (~r1_xboole_0(k1_tarski(B_24), k1_tarski(B_24)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.04/1.27  tff(c_108, plain, (![B_24]: (k4_xboole_0(k1_tarski(B_24), k1_tarski(B_24))!=k1_tarski(B_24))), inference(resolution, [status(thm)], [c_104, c_46])).
% 2.04/1.27  tff(c_148, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_139, c_108])).
% 2.04/1.27  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_2, c_139, c_148])).
% 2.04/1.27  tff(c_175, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_136])).
% 2.04/1.27  tff(c_32, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.27  tff(c_75, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.27  tff(c_14, plain, (![E_10, B_5, C_6]: (r2_hidden(E_10, k1_enumset1(E_10, B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.27  tff(c_93, plain, (![A_41, B_42]: (r2_hidden(A_41, k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_14])).
% 2.04/1.27  tff(c_96, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_93])).
% 2.04/1.27  tff(c_192, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_96])).
% 2.04/1.27  tff(c_34, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.27  tff(c_227, plain, (![E_60, C_61, B_62, A_63]: (E_60=C_61 | E_60=B_62 | E_60=A_63 | ~r2_hidden(E_60, k1_enumset1(A_63, B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.27  tff(c_246, plain, (![E_64, B_65, A_66]: (E_64=B_65 | E_64=A_66 | E_64=A_66 | ~r2_hidden(E_64, k2_tarski(A_66, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_227])).
% 2.04/1.27  tff(c_261, plain, (![E_71, A_72]: (E_71=A_72 | E_71=A_72 | E_71=A_72 | ~r2_hidden(E_71, k1_tarski(A_72)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_246])).
% 2.04/1.27  tff(c_264, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_192, c_261])).
% 2.04/1.27  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_48, c_264])).
% 2.04/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.27  
% 2.04/1.27  Inference rules
% 2.04/1.27  ----------------------
% 2.04/1.27  #Ref     : 0
% 2.04/1.27  #Sup     : 52
% 2.04/1.27  #Fact    : 0
% 2.04/1.27  #Define  : 0
% 2.04/1.27  #Split   : 1
% 2.04/1.27  #Chain   : 0
% 2.04/1.27  #Close   : 0
% 2.04/1.27  
% 2.04/1.27  Ordering : KBO
% 2.04/1.27  
% 2.04/1.27  Simplification rules
% 2.04/1.27  ----------------------
% 2.04/1.27  #Subsume      : 5
% 2.04/1.27  #Demod        : 23
% 2.04/1.27  #Tautology    : 28
% 2.04/1.27  #SimpNegUnit  : 1
% 2.04/1.27  #BackRed      : 3
% 2.04/1.27  
% 2.04/1.27  #Partial instantiations: 0
% 2.04/1.27  #Strategies tried      : 1
% 2.04/1.27  
% 2.04/1.27  Timing (in seconds)
% 2.04/1.27  ----------------------
% 2.04/1.27  Preprocessing        : 0.32
% 2.04/1.27  Parsing              : 0.16
% 2.04/1.27  CNF conversion       : 0.02
% 2.04/1.27  Main loop            : 0.17
% 2.04/1.27  Inferencing          : 0.06
% 2.04/1.27  Reduction            : 0.06
% 2.04/1.27  Demodulation         : 0.04
% 2.04/1.27  BG Simplification    : 0.01
% 2.04/1.27  Subsumption          : 0.03
% 2.04/1.27  Abstraction          : 0.01
% 2.04/1.27  MUC search           : 0.00
% 2.04/1.28  Cooper               : 0.00
% 2.04/1.28  Total                : 0.52
% 2.04/1.28  Index Insertion      : 0.00
% 2.04/1.28  Index Deletion       : 0.00
% 2.04/1.28  Index Matching       : 0.00
% 2.04/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
