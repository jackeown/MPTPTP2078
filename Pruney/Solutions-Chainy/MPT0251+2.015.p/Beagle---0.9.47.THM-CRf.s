%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:48 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  48 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_92,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_60,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tarski(A_38),B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_229,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2897,plain,(
    ! [A_173,B_174] :
      ( k3_xboole_0(k1_tarski(A_173),B_174) = k1_tarski(A_173)
      | ~ r2_hidden(A_173,B_174) ) ),
    inference(resolution,[status(thm)],[c_54,c_229])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_600,plain,(
    ! [A_84,B_85] : k2_xboole_0(k3_xboole_0(A_84,B_85),k4_xboole_0(A_84,B_85)) = A_84 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_633,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_600])).

tff(c_2935,plain,(
    ! [A_173,B_174] :
      ( k2_xboole_0(k1_tarski(A_173),k4_xboole_0(B_174,k1_tarski(A_173))) = B_174
      | ~ r2_hidden(A_173,B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2897,c_633])).

tff(c_3036,plain,(
    ! [A_175,B_176] :
      ( k2_xboole_0(k1_tarski(A_175),B_176) = B_176
      | ~ r2_hidden(A_175,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2935])).

tff(c_42,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_163,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_294,plain,(
    ! [B_71,A_72] : k3_tarski(k2_tarski(B_71,A_72)) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_163])).

tff(c_56,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_300,plain,(
    ! [B_71,A_72] : k2_xboole_0(B_71,A_72) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_56])).

tff(c_4196,plain,(
    ! [B_197,A_198] :
      ( k2_xboole_0(B_197,k1_tarski(A_198)) = B_197
      | ~ r2_hidden(A_198,B_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3036,c_300])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_320,plain,(
    k2_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_58])).

tff(c_4252,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4196,c_320])).

tff(c_4310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.86  
% 4.23/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.23/1.86  
% 4.23/1.86  %Foreground sorts:
% 4.23/1.86  
% 4.23/1.86  
% 4.23/1.86  %Background operators:
% 4.23/1.86  
% 4.23/1.86  
% 4.23/1.86  %Foreground operators:
% 4.23/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.23/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.23/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.23/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.23/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.23/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.23/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.23/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.23/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.23/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.23/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.23/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.23/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.23/1.86  
% 4.23/1.87  tff(f_97, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.23/1.87  tff(f_68, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.23/1.87  tff(f_90, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.23/1.87  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.23/1.87  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.23/1.87  tff(f_70, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.23/1.87  tff(f_78, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.23/1.87  tff(f_92, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.23/1.87  tff(c_60, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.23/1.87  tff(c_34, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.23/1.87  tff(c_54, plain, (![A_38, B_39]: (r1_tarski(k1_tarski(A_38), B_39) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.23/1.87  tff(c_229, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.23/1.87  tff(c_2897, plain, (![A_173, B_174]: (k3_xboole_0(k1_tarski(A_173), B_174)=k1_tarski(A_173) | ~r2_hidden(A_173, B_174))), inference(resolution, [status(thm)], [c_54, c_229])).
% 4.23/1.87  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.23/1.87  tff(c_600, plain, (![A_84, B_85]: (k2_xboole_0(k3_xboole_0(A_84, B_85), k4_xboole_0(A_84, B_85))=A_84)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.23/1.87  tff(c_633, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_600])).
% 4.23/1.87  tff(c_2935, plain, (![A_173, B_174]: (k2_xboole_0(k1_tarski(A_173), k4_xboole_0(B_174, k1_tarski(A_173)))=B_174 | ~r2_hidden(A_173, B_174))), inference(superposition, [status(thm), theory('equality')], [c_2897, c_633])).
% 4.23/1.87  tff(c_3036, plain, (![A_175, B_176]: (k2_xboole_0(k1_tarski(A_175), B_176)=B_176 | ~r2_hidden(A_175, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2935])).
% 4.23/1.87  tff(c_42, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.23/1.87  tff(c_163, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.23/1.87  tff(c_294, plain, (![B_71, A_72]: (k3_tarski(k2_tarski(B_71, A_72))=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_42, c_163])).
% 4.23/1.87  tff(c_56, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.23/1.87  tff(c_300, plain, (![B_71, A_72]: (k2_xboole_0(B_71, A_72)=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_294, c_56])).
% 4.23/1.87  tff(c_4196, plain, (![B_197, A_198]: (k2_xboole_0(B_197, k1_tarski(A_198))=B_197 | ~r2_hidden(A_198, B_197))), inference(superposition, [status(thm), theory('equality')], [c_3036, c_300])).
% 4.23/1.87  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.23/1.87  tff(c_320, plain, (k2_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_300, c_58])).
% 4.23/1.87  tff(c_4252, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4196, c_320])).
% 4.23/1.87  tff(c_4310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_4252])).
% 4.23/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.87  
% 4.23/1.87  Inference rules
% 4.23/1.87  ----------------------
% 4.23/1.87  #Ref     : 0
% 4.23/1.87  #Sup     : 1042
% 4.23/1.87  #Fact    : 0
% 4.23/1.87  #Define  : 0
% 4.23/1.87  #Split   : 0
% 4.23/1.87  #Chain   : 0
% 4.23/1.87  #Close   : 0
% 4.23/1.87  
% 4.23/1.87  Ordering : KBO
% 4.23/1.87  
% 4.23/1.87  Simplification rules
% 4.23/1.87  ----------------------
% 4.23/1.87  #Subsume      : 37
% 4.23/1.87  #Demod        : 808
% 4.23/1.87  #Tautology    : 691
% 4.23/1.87  #SimpNegUnit  : 0
% 4.23/1.87  #BackRed      : 6
% 4.23/1.87  
% 4.23/1.87  #Partial instantiations: 0
% 4.23/1.87  #Strategies tried      : 1
% 4.23/1.87  
% 4.23/1.87  Timing (in seconds)
% 4.23/1.87  ----------------------
% 4.23/1.88  Preprocessing        : 0.33
% 4.23/1.88  Parsing              : 0.17
% 4.23/1.88  CNF conversion       : 0.02
% 4.23/1.88  Main loop            : 0.69
% 4.23/1.88  Inferencing          : 0.22
% 4.23/1.88  Reduction            : 0.30
% 4.23/1.88  Demodulation         : 0.25
% 4.23/1.88  BG Simplification    : 0.03
% 4.23/1.88  Subsumption          : 0.10
% 4.23/1.88  Abstraction          : 0.04
% 4.23/1.88  MUC search           : 0.00
% 4.23/1.88  Cooper               : 0.00
% 4.23/1.88  Total                : 1.04
% 4.23/1.88  Index Insertion      : 0.00
% 4.23/1.88  Index Deletion       : 0.00
% 4.23/1.88  Index Matching       : 0.00
% 4.23/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
