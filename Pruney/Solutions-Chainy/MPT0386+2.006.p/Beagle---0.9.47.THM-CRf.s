%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:09 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  71 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ! [B_29,A_30] :
      ( ~ r2_hidden(B_29,A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_44])).

tff(c_100,plain,(
    ! [C_44,D_45,A_46] :
      ( r2_hidden(C_44,D_45)
      | ~ r2_hidden(D_45,A_46)
      | ~ r2_hidden(C_44,k1_setfam_1(A_46))
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [C_44] :
      ( r2_hidden(C_44,'#skF_7')
      | ~ r2_hidden(C_44,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_38,c_100])).

tff(c_133,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_136,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_12])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_136])).

tff(c_141,plain,(
    ! [C_51] :
      ( r2_hidden(C_51,'#skF_7')
      | ~ r2_hidden(C_51,k1_setfam_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_246,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_2'(k1_setfam_1('#skF_8'),B_59),'#skF_7')
      | r1_tarski(k1_setfam_1('#skF_8'),B_59) ) ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_254,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_246,c_8])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.34  
% 2.12/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.34  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.12/1.34  
% 2.12/1.34  %Foreground sorts:
% 2.12/1.34  
% 2.12/1.34  
% 2.12/1.34  %Background operators:
% 2.12/1.34  
% 2.12/1.34  
% 2.12/1.34  %Foreground operators:
% 2.12/1.34  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.12/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.12/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.12/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.12/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.12/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.12/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.12/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.34  
% 2.12/1.35  tff(f_63, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.12/1.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.12/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.12/1.35  tff(f_58, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.12/1.35  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.35  tff(c_36, plain, (~r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.12/1.35  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.35  tff(c_38, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.12/1.35  tff(c_44, plain, (![B_29, A_30]: (~r2_hidden(B_29, A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.35  tff(c_48, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_38, c_44])).
% 2.12/1.35  tff(c_100, plain, (![C_44, D_45, A_46]: (r2_hidden(C_44, D_45) | ~r2_hidden(D_45, A_46) | ~r2_hidden(C_44, k1_setfam_1(A_46)) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.35  tff(c_112, plain, (![C_44]: (r2_hidden(C_44, '#skF_7') | ~r2_hidden(C_44, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_38, c_100])).
% 2.12/1.35  tff(c_133, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_112])).
% 2.12/1.35  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.35  tff(c_136, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_12])).
% 2.12/1.35  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_136])).
% 2.12/1.35  tff(c_141, plain, (![C_51]: (r2_hidden(C_51, '#skF_7') | ~r2_hidden(C_51, k1_setfam_1('#skF_8')))), inference(splitRight, [status(thm)], [c_112])).
% 2.12/1.35  tff(c_246, plain, (![B_59]: (r2_hidden('#skF_2'(k1_setfam_1('#skF_8'), B_59), '#skF_7') | r1_tarski(k1_setfam_1('#skF_8'), B_59))), inference(resolution, [status(thm)], [c_10, c_141])).
% 2.12/1.35  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.35  tff(c_254, plain, (r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_246, c_8])).
% 2.12/1.35  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_254])).
% 2.12/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.35  
% 2.12/1.35  Inference rules
% 2.12/1.35  ----------------------
% 2.12/1.35  #Ref     : 0
% 2.12/1.35  #Sup     : 50
% 2.12/1.35  #Fact    : 0
% 2.12/1.35  #Define  : 0
% 2.12/1.35  #Split   : 2
% 2.12/1.35  #Chain   : 0
% 2.12/1.35  #Close   : 0
% 2.12/1.35  
% 2.12/1.35  Ordering : KBO
% 2.12/1.35  
% 2.12/1.35  Simplification rules
% 2.12/1.35  ----------------------
% 2.12/1.35  #Subsume      : 8
% 2.12/1.35  #Demod        : 7
% 2.12/1.35  #Tautology    : 8
% 2.12/1.35  #SimpNegUnit  : 3
% 2.12/1.35  #BackRed      : 3
% 2.12/1.35  
% 2.12/1.35  #Partial instantiations: 0
% 2.12/1.35  #Strategies tried      : 1
% 2.12/1.35  
% 2.12/1.35  Timing (in seconds)
% 2.12/1.35  ----------------------
% 2.12/1.35  Preprocessing        : 0.33
% 2.12/1.35  Parsing              : 0.16
% 2.12/1.35  CNF conversion       : 0.03
% 2.12/1.35  Main loop            : 0.21
% 2.12/1.35  Inferencing          : 0.08
% 2.12/1.35  Reduction            : 0.06
% 2.12/1.35  Demodulation         : 0.04
% 2.12/1.35  BG Simplification    : 0.02
% 2.12/1.35  Subsumption          : 0.05
% 2.12/1.35  Abstraction          : 0.01
% 2.12/1.35  MUC search           : 0.00
% 2.12/1.35  Cooper               : 0.00
% 2.12/1.35  Total                : 0.57
% 2.12/1.35  Index Insertion      : 0.00
% 2.12/1.35  Index Deletion       : 0.00
% 2.12/1.35  Index Matching       : 0.00
% 2.12/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
