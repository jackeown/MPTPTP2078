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
% DateTime   : Thu Dec  3 09:48:21 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  56 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_178,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_3'(A_55,B_56),k3_xboole_0(A_55,B_56))
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_140,plain,(
    ! [D_40,A_41,B_42] :
      ( r2_hidden(D_40,A_41)
      | ~ r2_hidden(D_40,k4_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_143,plain,(
    ! [D_40,A_14,B_15] :
      ( r2_hidden(D_40,A_14)
      | ~ r2_hidden(D_40,k3_xboole_0(A_14,B_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_227,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63),A_62)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_178,c_143])).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),k1_tarski(B_25))
      | B_25 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_119,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [C_38] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5'))
      | ~ r2_hidden(C_38,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_119])).

tff(c_129,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_132,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_129])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_132])).

tff(c_137,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_276,plain,(
    ! [B_67] : r1_xboole_0(k1_tarski('#skF_4'),B_67) ),
    inference(resolution,[status(thm)],[c_227,c_137])).

tff(c_34,plain,(
    ! [B_23] : ~ r1_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_284,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_276,c_34])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.99/1.22  
% 1.99/1.22  %Foreground sorts:
% 1.99/1.22  
% 1.99/1.22  
% 1.99/1.22  %Background operators:
% 1.99/1.22  
% 1.99/1.22  
% 1.99/1.22  %Foreground operators:
% 1.99/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.99/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.22  
% 2.10/1.23  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.23  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.10/1.23  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.10/1.23  tff(f_74, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.10/1.23  tff(f_69, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.10/1.23  tff(f_64, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.10/1.23  tff(c_178, plain, (![A_55, B_56]: (r2_hidden('#skF_3'(A_55, B_56), k3_xboole_0(A_55, B_56)) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.23  tff(c_26, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.23  tff(c_140, plain, (![D_40, A_41, B_42]: (r2_hidden(D_40, A_41) | ~r2_hidden(D_40, k4_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.23  tff(c_143, plain, (![D_40, A_14, B_15]: (r2_hidden(D_40, A_14) | ~r2_hidden(D_40, k3_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_140])).
% 2.10/1.23  tff(c_227, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63), A_62) | r1_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_178, c_143])).
% 2.10/1.23  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.10/1.23  tff(c_36, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), k1_tarski(B_25)) | B_25=A_24)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.10/1.23  tff(c_40, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.10/1.23  tff(c_119, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.23  tff(c_122, plain, (![C_38]: (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')) | ~r2_hidden(C_38, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_119])).
% 2.10/1.23  tff(c_129, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_122])).
% 2.10/1.23  tff(c_132, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_129])).
% 2.10/1.23  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_132])).
% 2.10/1.23  tff(c_137, plain, (![C_38]: (~r2_hidden(C_38, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_122])).
% 2.10/1.23  tff(c_276, plain, (![B_67]: (r1_xboole_0(k1_tarski('#skF_4'), B_67))), inference(resolution, [status(thm)], [c_227, c_137])).
% 2.10/1.23  tff(c_34, plain, (![B_23]: (~r1_xboole_0(k1_tarski(B_23), k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.23  tff(c_284, plain, $false, inference(resolution, [status(thm)], [c_276, c_34])).
% 2.10/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  Inference rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Ref     : 0
% 2.10/1.23  #Sup     : 58
% 2.10/1.23  #Fact    : 0
% 2.10/1.23  #Define  : 0
% 2.10/1.23  #Split   : 1
% 2.10/1.23  #Chain   : 0
% 2.10/1.23  #Close   : 0
% 2.10/1.23  
% 2.10/1.23  Ordering : KBO
% 2.10/1.23  
% 2.10/1.23  Simplification rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Subsume      : 10
% 2.10/1.23  #Demod        : 3
% 2.10/1.23  #Tautology    : 25
% 2.10/1.23  #SimpNegUnit  : 3
% 2.10/1.23  #BackRed      : 0
% 2.10/1.23  
% 2.10/1.23  #Partial instantiations: 0
% 2.10/1.23  #Strategies tried      : 1
% 2.10/1.23  
% 2.10/1.23  Timing (in seconds)
% 2.10/1.23  ----------------------
% 2.10/1.24  Preprocessing        : 0.30
% 2.10/1.24  Parsing              : 0.16
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.17
% 2.10/1.24  Inferencing          : 0.06
% 2.10/1.24  Reduction            : 0.05
% 2.10/1.24  Demodulation         : 0.04
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.03
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.50
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
