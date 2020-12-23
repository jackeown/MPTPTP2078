%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:46 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   46 (  70 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  92 expanded)
%              Number of equality atoms :   23 (  49 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_xboole_0(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),B_18)
      | r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = A_34
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(k1_tarski(A_46),B_47) = k1_tarski(A_46)
      | r2_hidden(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_34,c_92])).

tff(c_38,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_38])).

tff(c_156,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_28,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [D_38,B_39,A_40] :
      ( D_38 = B_39
      | D_38 = A_40
      | ~ r2_hidden(D_38,k2_tarski(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_119,plain,(
    ! [D_38,A_12] :
      ( D_38 = A_12
      | D_38 = A_12
      | ~ r2_hidden(D_38,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_110])).

tff(c_159,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_156,c_119])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_159])).

tff(c_164,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_57,plain,(
    ! [D_21,B_22] : r2_hidden(D_21,k2_tarski(D_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_57])).

tff(c_207,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_60])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,B_16)
      | ~ r1_xboole_0(k1_tarski(A_15),B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_238,plain,(
    ! [B_52] :
      ( ~ r2_hidden('#skF_3',B_52)
      | ~ r1_xboole_0(k1_xboole_0,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_32])).

tff(c_258,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_207,c_238])).

tff(c_265,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_258])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:36:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.08/1.26  
% 2.08/1.26  %Foreground sorts:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Background operators:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Foreground operators:
% 2.08/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.26  
% 2.08/1.28  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.08/1.28  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.08/1.28  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.08/1.28  tff(f_56, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.08/1.28  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.28  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.08/1.28  tff(f_51, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.08/1.28  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.28  tff(c_8, plain, (![A_4, B_5]: (r1_xboole_0(A_4, B_5) | k4_xboole_0(A_4, B_5)!=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.28  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.28  tff(c_34, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), B_18) | r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.28  tff(c_92, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=A_34 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.28  tff(c_131, plain, (![A_46, B_47]: (k4_xboole_0(k1_tarski(A_46), B_47)=k1_tarski(A_46) | r2_hidden(A_46, B_47))), inference(resolution, [status(thm)], [c_34, c_92])).
% 2.08/1.28  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.28  tff(c_137, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_38])).
% 2.08/1.28  tff(c_156, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_137])).
% 2.08/1.28  tff(c_28, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.28  tff(c_110, plain, (![D_38, B_39, A_40]: (D_38=B_39 | D_38=A_40 | ~r2_hidden(D_38, k2_tarski(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.28  tff(c_119, plain, (![D_38, A_12]: (D_38=A_12 | D_38=A_12 | ~r2_hidden(D_38, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_110])).
% 2.08/1.28  tff(c_159, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_156, c_119])).
% 2.08/1.28  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_159])).
% 2.08/1.28  tff(c_164, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_137])).
% 2.08/1.28  tff(c_57, plain, (![D_21, B_22]: (r2_hidden(D_21, k2_tarski(D_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.28  tff(c_60, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_57])).
% 2.08/1.28  tff(c_207, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_164, c_60])).
% 2.08/1.28  tff(c_32, plain, (![A_15, B_16]: (~r2_hidden(A_15, B_16) | ~r1_xboole_0(k1_tarski(A_15), B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.28  tff(c_238, plain, (![B_52]: (~r2_hidden('#skF_3', B_52) | ~r1_xboole_0(k1_xboole_0, B_52))), inference(superposition, [status(thm), theory('equality')], [c_164, c_32])).
% 2.08/1.28  tff(c_258, plain, (~r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_207, c_238])).
% 2.08/1.28  tff(c_265, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_258])).
% 2.08/1.28  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_265])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 53
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 2
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 1
% 2.08/1.28  #Demod        : 9
% 2.08/1.28  #Tautology    : 29
% 2.08/1.28  #SimpNegUnit  : 2
% 2.08/1.28  #BackRed      : 2
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.31
% 2.08/1.28  Parsing              : 0.16
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.19
% 2.08/1.28  Inferencing          : 0.07
% 2.08/1.28  Reduction            : 0.06
% 2.08/1.28  Demodulation         : 0.04
% 2.08/1.28  BG Simplification    : 0.01
% 2.08/1.28  Subsumption          : 0.03
% 2.08/1.28  Abstraction          : 0.01
% 2.08/1.28  MUC search           : 0.00
% 2.08/1.28  Cooper               : 0.00
% 2.08/1.28  Total                : 0.53
% 2.08/1.28  Index Insertion      : 0.00
% 2.08/1.28  Index Deletion       : 0.00
% 2.08/1.28  Index Matching       : 0.00
% 2.08/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
