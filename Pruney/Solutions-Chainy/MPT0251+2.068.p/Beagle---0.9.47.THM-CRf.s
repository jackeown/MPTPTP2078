%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:55 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   48 (  53 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  70 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_52,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | ~ r1_tarski(k1_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_148,plain,(
    ! [A_43] : r2_hidden(A_43,k1_tarski(A_43)) ),
    inference(resolution,[status(thm)],[c_32,c_143])).

tff(c_10,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k3_xboole_0(A_8,B_9))
      | ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_167,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_287,plain,(
    ! [A_87,B_88,B_89] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_87,B_88),B_89),B_88)
      | r1_tarski(k3_xboole_0(A_87,B_88),B_89) ) ),
    inference(resolution,[status(thm)],[c_167,c_12])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_333,plain,(
    ! [A_93,B_94] : r1_tarski(k3_xboole_0(A_93,B_94),B_94) ),
    inference(resolution,[status(thm)],[c_287,c_6])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tarski(A_28),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_157,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    ! [A_28,B_29] :
      ( k1_tarski(A_28) = B_29
      | ~ r1_tarski(B_29,k1_tarski(A_28))
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_46,c_157])).

tff(c_739,plain,(
    ! [A_127,A_128] :
      ( k3_xboole_0(A_127,k1_tarski(A_128)) = k1_tarski(A_128)
      | ~ r2_hidden(A_128,k3_xboole_0(A_127,k1_tarski(A_128))) ) ),
    inference(resolution,[status(thm)],[c_333,c_162])).

tff(c_751,plain,(
    ! [A_8,D_13] :
      ( k3_xboole_0(A_8,k1_tarski(D_13)) = k1_tarski(D_13)
      | ~ r2_hidden(D_13,k1_tarski(D_13))
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_739])).

tff(c_766,plain,(
    ! [A_130,D_131] :
      ( k3_xboole_0(A_130,k1_tarski(D_131)) = k1_tarski(D_131)
      | ~ r2_hidden(D_131,A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_751])).

tff(c_34,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_835,plain,(
    ! [A_132,D_133] :
      ( k2_xboole_0(A_132,k1_tarski(D_133)) = A_132
      | ~ r2_hidden(D_133,A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_34])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_851,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_54])).

tff(c_873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.00/1.46  
% 3.00/1.46  %Foreground sorts:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Background operators:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Foreground operators:
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.00/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.00/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.00/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.46  
% 3.00/1.47  tff(f_70, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.00/1.47  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.00/1.47  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.00/1.47  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.00/1.47  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.00/1.47  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.00/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.00/1.47  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.47  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.47  tff(c_143, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | ~r1_tarski(k1_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.47  tff(c_148, plain, (![A_43]: (r2_hidden(A_43, k1_tarski(A_43)))), inference(resolution, [status(thm)], [c_32, c_143])).
% 3.00/1.47  tff(c_10, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, k3_xboole_0(A_8, B_9)) | ~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.00/1.47  tff(c_167, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.47  tff(c_12, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.00/1.47  tff(c_287, plain, (![A_87, B_88, B_89]: (r2_hidden('#skF_1'(k3_xboole_0(A_87, B_88), B_89), B_88) | r1_tarski(k3_xboole_0(A_87, B_88), B_89))), inference(resolution, [status(thm)], [c_167, c_12])).
% 3.00/1.47  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.00/1.47  tff(c_333, plain, (![A_93, B_94]: (r1_tarski(k3_xboole_0(A_93, B_94), B_94))), inference(resolution, [status(thm)], [c_287, c_6])).
% 3.00/1.47  tff(c_46, plain, (![A_28, B_29]: (r1_tarski(k1_tarski(A_28), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.47  tff(c_157, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.00/1.47  tff(c_162, plain, (![A_28, B_29]: (k1_tarski(A_28)=B_29 | ~r1_tarski(B_29, k1_tarski(A_28)) | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_46, c_157])).
% 3.00/1.47  tff(c_739, plain, (![A_127, A_128]: (k3_xboole_0(A_127, k1_tarski(A_128))=k1_tarski(A_128) | ~r2_hidden(A_128, k3_xboole_0(A_127, k1_tarski(A_128))))), inference(resolution, [status(thm)], [c_333, c_162])).
% 3.00/1.47  tff(c_751, plain, (![A_8, D_13]: (k3_xboole_0(A_8, k1_tarski(D_13))=k1_tarski(D_13) | ~r2_hidden(D_13, k1_tarski(D_13)) | ~r2_hidden(D_13, A_8))), inference(resolution, [status(thm)], [c_10, c_739])).
% 3.00/1.47  tff(c_766, plain, (![A_130, D_131]: (k3_xboole_0(A_130, k1_tarski(D_131))=k1_tarski(D_131) | ~r2_hidden(D_131, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_751])).
% 3.00/1.47  tff(c_34, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k3_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.00/1.47  tff(c_835, plain, (![A_132, D_133]: (k2_xboole_0(A_132, k1_tarski(D_133))=A_132 | ~r2_hidden(D_133, A_132))), inference(superposition, [status(thm), theory('equality')], [c_766, c_34])).
% 3.00/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.47  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.47  tff(c_54, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 3.00/1.47  tff(c_851, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_835, c_54])).
% 3.00/1.47  tff(c_873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_851])).
% 3.00/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.47  
% 3.00/1.47  Inference rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Ref     : 0
% 3.00/1.47  #Sup     : 187
% 3.00/1.47  #Fact    : 0
% 3.00/1.47  #Define  : 0
% 3.00/1.47  #Split   : 0
% 3.00/1.47  #Chain   : 0
% 3.00/1.47  #Close   : 0
% 3.00/1.47  
% 3.00/1.47  Ordering : KBO
% 3.00/1.47  
% 3.00/1.47  Simplification rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Subsume      : 23
% 3.00/1.47  #Demod        : 21
% 3.00/1.47  #Tautology    : 51
% 3.00/1.47  #SimpNegUnit  : 0
% 3.00/1.47  #BackRed      : 0
% 3.00/1.47  
% 3.00/1.47  #Partial instantiations: 0
% 3.00/1.47  #Strategies tried      : 1
% 3.00/1.47  
% 3.00/1.47  Timing (in seconds)
% 3.00/1.47  ----------------------
% 3.00/1.48  Preprocessing        : 0.31
% 3.00/1.48  Parsing              : 0.16
% 3.00/1.48  CNF conversion       : 0.02
% 3.00/1.48  Main loop            : 0.36
% 3.00/1.48  Inferencing          : 0.13
% 3.00/1.48  Reduction            : 0.10
% 3.00/1.48  Demodulation         : 0.07
% 3.00/1.48  BG Simplification    : 0.02
% 3.00/1.48  Subsumption          : 0.08
% 3.00/1.48  Abstraction          : 0.03
% 3.00/1.48  MUC search           : 0.00
% 3.00/1.48  Cooper               : 0.00
% 3.00/1.48  Total                : 0.69
% 3.00/1.48  Index Insertion      : 0.00
% 3.00/1.48  Index Deletion       : 0.00
% 3.00/1.48  Index Matching       : 0.00
% 3.00/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
