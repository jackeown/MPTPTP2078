%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:09 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 109 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_54,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49),B_49)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_56,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_213,plain,(
    ! [C_72,D_73,A_74] :
      ( r2_hidden(C_72,D_73)
      | ~ r2_hidden(D_73,A_74)
      | ~ r2_hidden(C_72,k1_setfam_1(A_74))
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_225,plain,(
    ! [C_72] :
      ( r2_hidden(C_72,'#skF_8')
      | ~ r2_hidden(C_72,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_56,c_213])).

tff(c_226,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_130,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_8',B_59)
      | ~ r1_tarski('#skF_9',B_59) ) ),
    inference(resolution,[status(thm)],[c_56,c_130])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_16] :
      ( r2_xboole_0(k1_xboole_0,A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    ! [B_39,A_40] :
      ( ~ r2_xboole_0(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [A_41] :
      ( ~ r1_tarski(A_41,k1_xboole_0)
      | k1_xboole_0 = A_41 ) ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_74,plain,(
    ! [B_13] : k4_xboole_0(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_114,plain,(
    ! [D_51,B_52,A_53] :
      ( ~ r2_hidden(D_51,B_52)
      | ~ r2_hidden(D_51,k4_xboole_0(A_53,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    ! [D_54,B_55] :
      ( ~ r2_hidden(D_54,B_55)
      | ~ r2_hidden(D_54,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_114])).

tff(c_129,plain,(
    ~ r2_hidden('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_56,c_123])).

tff(c_153,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_137,c_129])).

tff(c_230,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_153])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_230])).

tff(c_242,plain,(
    ! [C_75] :
      ( r2_hidden(C_75,'#skF_8')
      | ~ r2_hidden(C_75,k1_setfam_1('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_264,plain,(
    ! [B_79] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_9'),B_79),'#skF_8')
      | r1_tarski(k1_setfam_1('#skF_9'),B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_242])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_274,plain,(
    r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_264,c_4])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.25  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5
% 2.13/1.25  
% 2.13/1.25  %Foreground sorts:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Background operators:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Foreground operators:
% 2.13/1.25  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.13/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.25  tff('#skF_9', type, '#skF_9': $i).
% 2.13/1.25  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.13/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.25  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.13/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.25  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.13/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.25  
% 2.13/1.26  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.13/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.13/1.26  tff(f_73, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.13/1.26  tff(f_44, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.13/1.26  tff(f_54, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 2.13/1.26  tff(f_49, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.13/1.26  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.13/1.26  tff(c_54, plain, (~r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.26  tff(c_100, plain, (![A_48, B_49]: (~r2_hidden('#skF_1'(A_48, B_49), B_49) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.26  tff(c_105, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_100])).
% 2.13/1.26  tff(c_56, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.26  tff(c_213, plain, (![C_72, D_73, A_74]: (r2_hidden(C_72, D_73) | ~r2_hidden(D_73, A_74) | ~r2_hidden(C_72, k1_setfam_1(A_74)) | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.13/1.26  tff(c_225, plain, (![C_72]: (r2_hidden(C_72, '#skF_8') | ~r2_hidden(C_72, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_56, c_213])).
% 2.13/1.26  tff(c_226, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_225])).
% 2.13/1.26  tff(c_130, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.26  tff(c_137, plain, (![B_59]: (r2_hidden('#skF_8', B_59) | ~r1_tarski('#skF_9', B_59))), inference(resolution, [status(thm)], [c_56, c_130])).
% 2.13/1.26  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.26  tff(c_30, plain, (![A_16]: (r2_xboole_0(k1_xboole_0, A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.26  tff(c_64, plain, (![B_39, A_40]: (~r2_xboole_0(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.26  tff(c_69, plain, (![A_41]: (~r1_tarski(A_41, k1_xboole_0) | k1_xboole_0=A_41)), inference(resolution, [status(thm)], [c_30, c_64])).
% 2.13/1.26  tff(c_74, plain, (![B_13]: (k4_xboole_0(k1_xboole_0, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_69])).
% 2.13/1.26  tff(c_114, plain, (![D_51, B_52, A_53]: (~r2_hidden(D_51, B_52) | ~r2_hidden(D_51, k4_xboole_0(A_53, B_52)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.13/1.26  tff(c_123, plain, (![D_54, B_55]: (~r2_hidden(D_54, B_55) | ~r2_hidden(D_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_74, c_114])).
% 2.13/1.26  tff(c_129, plain, (~r2_hidden('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_123])).
% 2.13/1.26  tff(c_153, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_137, c_129])).
% 2.13/1.26  tff(c_230, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_153])).
% 2.13/1.26  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_230])).
% 2.13/1.26  tff(c_242, plain, (![C_75]: (r2_hidden(C_75, '#skF_8') | ~r2_hidden(C_75, k1_setfam_1('#skF_9')))), inference(splitRight, [status(thm)], [c_225])).
% 2.13/1.26  tff(c_264, plain, (![B_79]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_9'), B_79), '#skF_8') | r1_tarski(k1_setfam_1('#skF_9'), B_79))), inference(resolution, [status(thm)], [c_6, c_242])).
% 2.13/1.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.26  tff(c_274, plain, (r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_264, c_4])).
% 2.13/1.26  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_274])).
% 2.13/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  Inference rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Ref     : 0
% 2.13/1.26  #Sup     : 48
% 2.13/1.26  #Fact    : 0
% 2.13/1.26  #Define  : 0
% 2.13/1.26  #Split   : 2
% 2.13/1.26  #Chain   : 0
% 2.13/1.26  #Close   : 0
% 2.13/1.26  
% 2.13/1.26  Ordering : KBO
% 2.13/1.26  
% 2.13/1.26  Simplification rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Subsume      : 8
% 2.13/1.26  #Demod        : 18
% 2.13/1.26  #Tautology    : 14
% 2.13/1.26  #SimpNegUnit  : 2
% 2.13/1.26  #BackRed      : 10
% 2.13/1.26  
% 2.13/1.26  #Partial instantiations: 0
% 2.13/1.26  #Strategies tried      : 1
% 2.13/1.26  
% 2.13/1.26  Timing (in seconds)
% 2.13/1.26  ----------------------
% 2.25/1.27  Preprocessing        : 0.29
% 2.25/1.27  Parsing              : 0.15
% 2.25/1.27  CNF conversion       : 0.03
% 2.25/1.27  Main loop            : 0.21
% 2.25/1.27  Inferencing          : 0.07
% 2.25/1.27  Reduction            : 0.06
% 2.25/1.27  Demodulation         : 0.04
% 2.25/1.27  BG Simplification    : 0.02
% 2.25/1.27  Subsumption          : 0.05
% 2.25/1.27  Abstraction          : 0.01
% 2.25/1.27  MUC search           : 0.00
% 2.25/1.27  Cooper               : 0.00
% 2.25/1.27  Total                : 0.53
% 2.25/1.27  Index Insertion      : 0.00
% 2.25/1.27  Index Deletion       : 0.00
% 2.25/1.27  Index Matching       : 0.00
% 2.25/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
