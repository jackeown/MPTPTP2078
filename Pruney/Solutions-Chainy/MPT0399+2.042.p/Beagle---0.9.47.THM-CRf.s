%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:37 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  66 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_setfam_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden('#skF_4'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(C_35,A_33)
      | ~ r1_setfam_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [B_20,A_21] :
      ( ~ r2_hidden(B_20,A_21)
      | k4_xboole_0(A_21,k1_tarski(B_20)) != A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,(
    ! [B_20] : ~ r2_hidden(B_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_34])).

tff(c_86,plain,(
    ! [C_36,A_37] :
      ( ~ r2_hidden(C_36,A_37)
      | ~ r1_setfam_1(A_37,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_80,c_39])).

tff(c_99,plain,(
    ! [A_38,B_39] :
      ( ~ r1_setfam_1(A_38,k1_xboole_0)
      | r1_setfam_1(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_107,plain,(
    ! [B_39] : r1_setfam_1('#skF_5',B_39) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_164,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_54)
      | r2_hidden('#skF_2'(A_53,B_54),A_53)
      | B_54 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_194,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_55),B_55)
      | k1_xboole_0 = B_55 ) ),
    inference(resolution,[status(thm)],[c_164,c_39])).

tff(c_85,plain,(
    ! [C_35,A_33] :
      ( ~ r2_hidden(C_35,A_33)
      | ~ r1_setfam_1(A_33,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_80,c_39])).

tff(c_209,plain,(
    ! [B_56] :
      ( ~ r1_setfam_1(B_56,k1_xboole_0)
      | k1_xboole_0 = B_56 ) ),
    inference(resolution,[status(thm)],[c_194,c_85])).

tff(c_213,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_107,c_209])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.51  
% 2.28/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.52  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 2.28/1.52  
% 2.28/1.52  %Foreground sorts:
% 2.28/1.52  
% 2.28/1.52  
% 2.28/1.52  %Background operators:
% 2.28/1.52  
% 2.28/1.52  
% 2.28/1.52  %Foreground operators:
% 2.28/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.52  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.28/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.28/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.28/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.28/1.52  
% 2.28/1.53  tff(f_56, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.28/1.53  tff(f_51, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.28/1.53  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.28/1.53  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.28/1.53  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.28/1.53  tff(c_24, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.53  tff(c_26, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.53  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_setfam_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.53  tff(c_80, plain, (![A_33, B_34, C_35]: (r2_hidden('#skF_4'(A_33, B_34, C_35), B_34) | ~r2_hidden(C_35, A_33) | ~r1_setfam_1(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.53  tff(c_10, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.28/1.53  tff(c_34, plain, (![B_20, A_21]: (~r2_hidden(B_20, A_21) | k4_xboole_0(A_21, k1_tarski(B_20))!=A_21)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.53  tff(c_39, plain, (![B_20]: (~r2_hidden(B_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_34])).
% 2.28/1.53  tff(c_86, plain, (![C_36, A_37]: (~r2_hidden(C_36, A_37) | ~r1_setfam_1(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_39])).
% 2.28/1.53  tff(c_99, plain, (![A_38, B_39]: (~r1_setfam_1(A_38, k1_xboole_0) | r1_setfam_1(A_38, B_39))), inference(resolution, [status(thm)], [c_22, c_86])).
% 2.28/1.53  tff(c_107, plain, (![B_39]: (r1_setfam_1('#skF_5', B_39))), inference(resolution, [status(thm)], [c_26, c_99])).
% 2.28/1.53  tff(c_164, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), B_54) | r2_hidden('#skF_2'(A_53, B_54), A_53) | B_54=A_53)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.53  tff(c_194, plain, (![B_55]: (r2_hidden('#skF_1'(k1_xboole_0, B_55), B_55) | k1_xboole_0=B_55)), inference(resolution, [status(thm)], [c_164, c_39])).
% 2.28/1.53  tff(c_85, plain, (![C_35, A_33]: (~r2_hidden(C_35, A_33) | ~r1_setfam_1(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_39])).
% 2.28/1.53  tff(c_209, plain, (![B_56]: (~r1_setfam_1(B_56, k1_xboole_0) | k1_xboole_0=B_56)), inference(resolution, [status(thm)], [c_194, c_85])).
% 2.28/1.53  tff(c_213, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_107, c_209])).
% 2.28/1.53  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_213])).
% 2.28/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.53  
% 2.28/1.53  Inference rules
% 2.28/1.53  ----------------------
% 2.28/1.53  #Ref     : 0
% 2.28/1.53  #Sup     : 38
% 2.28/1.53  #Fact    : 0
% 2.28/1.53  #Define  : 0
% 2.28/1.53  #Split   : 0
% 2.28/1.53  #Chain   : 0
% 2.28/1.53  #Close   : 0
% 2.28/1.53  
% 2.28/1.53  Ordering : KBO
% 2.28/1.53  
% 2.28/1.53  Simplification rules
% 2.28/1.53  ----------------------
% 2.28/1.53  #Subsume      : 6
% 2.28/1.53  #Demod        : 5
% 2.28/1.53  #Tautology    : 15
% 2.28/1.53  #SimpNegUnit  : 3
% 2.28/1.53  #BackRed      : 0
% 2.28/1.53  
% 2.28/1.53  #Partial instantiations: 0
% 2.28/1.53  #Strategies tried      : 1
% 2.28/1.53  
% 2.28/1.53  Timing (in seconds)
% 2.28/1.53  ----------------------
% 2.28/1.54  Preprocessing        : 0.47
% 2.28/1.54  Parsing              : 0.24
% 2.28/1.54  CNF conversion       : 0.03
% 2.28/1.54  Main loop            : 0.24
% 2.28/1.54  Inferencing          : 0.11
% 2.28/1.54  Reduction            : 0.06
% 2.28/1.54  Demodulation         : 0.04
% 2.28/1.54  BG Simplification    : 0.02
% 2.28/1.54  Subsumption          : 0.04
% 2.28/1.54  Abstraction          : 0.01
% 2.28/1.54  MUC search           : 0.00
% 2.28/1.54  Cooper               : 0.00
% 2.28/1.54  Total                : 0.75
% 2.28/1.54  Index Insertion      : 0.00
% 2.28/1.54  Index Deletion       : 0.00
% 2.28/1.54  Index Matching       : 0.00
% 2.28/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
