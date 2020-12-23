%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:59 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  41 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_34,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [B_47,A_48] : k5_xboole_0(B_47,A_48) = k5_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_48] : k5_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_488,plain,(
    ! [A_69,B_70,C_71] : k5_xboole_0(k5_xboole_0(A_69,B_70),C_71) = k5_xboole_0(A_69,k5_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_565,plain,(
    ! [A_9,C_71] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_71)) = k5_xboole_0(k1_xboole_0,C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_488])).

tff(c_581,plain,(
    ! [A_72,C_73] : k5_xboole_0(A_72,k5_xboole_0(A_72,C_73)) = C_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_565])).

tff(c_630,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_581])).

tff(c_247,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(B_60,k1_tarski(A_61)) = k1_tarski(A_61)
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_253,plain,(
    ! [A_61,B_60] :
      ( k3_xboole_0(k1_tarski(A_61),B_60) = k1_tarski(A_61)
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_2])).

tff(c_301,plain,(
    ! [A_64,B_65] : k5_xboole_0(k5_xboole_0(A_64,B_65),k3_xboole_0(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2591,plain,(
    ! [B_125,A_126] : k5_xboole_0(k5_xboole_0(B_125,A_126),k3_xboole_0(A_126,B_125)) = k2_xboole_0(A_126,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_301])).

tff(c_2733,plain,(
    ! [B_60,A_61] :
      ( k5_xboole_0(k5_xboole_0(B_60,k1_tarski(A_61)),k1_tarski(A_61)) = k2_xboole_0(k1_tarski(A_61),B_60)
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_2591])).

tff(c_2790,plain,(
    ! [A_127,B_128] :
      ( k2_xboole_0(k1_tarski(A_127),B_128) = B_128
      | ~ r2_hidden(A_127,B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_4,c_2733])).

tff(c_32,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2824,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2790,c_32])).

tff(c_2845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n003.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:23:42 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.67  
% 3.86/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.68  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.86/1.68  
% 3.86/1.68  %Foreground sorts:
% 3.86/1.68  
% 3.86/1.68  
% 3.86/1.68  %Background operators:
% 3.86/1.68  
% 3.86/1.68  
% 3.86/1.68  %Foreground operators:
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.86/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.86/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.86/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.86/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.86/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.86/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.86/1.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.86/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.86/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.86/1.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.86/1.68  
% 3.99/1.69  tff(f_62, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.99/1.69  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.99/1.69  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.99/1.69  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.99/1.69  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.99/1.69  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 3.99/1.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.99/1.69  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.99/1.69  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.99/1.69  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.69  tff(c_70, plain, (![B_47, A_48]: (k5_xboole_0(B_47, A_48)=k5_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.69  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.69  tff(c_86, plain, (![A_48]: (k5_xboole_0(k1_xboole_0, A_48)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 3.99/1.69  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.99/1.69  tff(c_488, plain, (![A_69, B_70, C_71]: (k5_xboole_0(k5_xboole_0(A_69, B_70), C_71)=k5_xboole_0(A_69, k5_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.99/1.69  tff(c_565, plain, (![A_9, C_71]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_71))=k5_xboole_0(k1_xboole_0, C_71))), inference(superposition, [status(thm), theory('equality')], [c_10, c_488])).
% 3.99/1.69  tff(c_581, plain, (![A_72, C_73]: (k5_xboole_0(A_72, k5_xboole_0(A_72, C_73))=C_73)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_565])).
% 3.99/1.69  tff(c_630, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_581])).
% 3.99/1.69  tff(c_247, plain, (![B_60, A_61]: (k3_xboole_0(B_60, k1_tarski(A_61))=k1_tarski(A_61) | ~r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.69  tff(c_253, plain, (![A_61, B_60]: (k3_xboole_0(k1_tarski(A_61), B_60)=k1_tarski(A_61) | ~r2_hidden(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_247, c_2])).
% 3.99/1.69  tff(c_301, plain, (![A_64, B_65]: (k5_xboole_0(k5_xboole_0(A_64, B_65), k3_xboole_0(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.99/1.69  tff(c_2591, plain, (![B_125, A_126]: (k5_xboole_0(k5_xboole_0(B_125, A_126), k3_xboole_0(A_126, B_125))=k2_xboole_0(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_4, c_301])).
% 3.99/1.69  tff(c_2733, plain, (![B_60, A_61]: (k5_xboole_0(k5_xboole_0(B_60, k1_tarski(A_61)), k1_tarski(A_61))=k2_xboole_0(k1_tarski(A_61), B_60) | ~r2_hidden(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_253, c_2591])).
% 3.99/1.69  tff(c_2790, plain, (![A_127, B_128]: (k2_xboole_0(k1_tarski(A_127), B_128)=B_128 | ~r2_hidden(A_127, B_128))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_4, c_2733])).
% 3.99/1.69  tff(c_32, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.99/1.69  tff(c_2824, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2790, c_32])).
% 3.99/1.69  tff(c_2845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2824])).
% 3.99/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.69  
% 3.99/1.69  Inference rules
% 3.99/1.69  ----------------------
% 3.99/1.69  #Ref     : 0
% 3.99/1.69  #Sup     : 699
% 3.99/1.69  #Fact    : 0
% 3.99/1.69  #Define  : 0
% 3.99/1.69  #Split   : 0
% 3.99/1.69  #Chain   : 0
% 3.99/1.69  #Close   : 0
% 3.99/1.69  
% 3.99/1.69  Ordering : KBO
% 3.99/1.69  
% 3.99/1.69  Simplification rules
% 3.99/1.69  ----------------------
% 3.99/1.69  #Subsume      : 53
% 3.99/1.69  #Demod        : 349
% 3.99/1.69  #Tautology    : 348
% 3.99/1.69  #SimpNegUnit  : 0
% 3.99/1.69  #BackRed      : 2
% 3.99/1.69  
% 3.99/1.69  #Partial instantiations: 0
% 3.99/1.69  #Strategies tried      : 1
% 3.99/1.69  
% 3.99/1.69  Timing (in seconds)
% 3.99/1.69  ----------------------
% 3.99/1.69  Preprocessing        : 0.31
% 3.99/1.69  Parsing              : 0.16
% 3.99/1.69  CNF conversion       : 0.02
% 3.99/1.69  Main loop            : 0.63
% 3.99/1.69  Inferencing          : 0.21
% 3.99/1.69  Reduction            : 0.27
% 3.99/1.69  Demodulation         : 0.23
% 3.99/1.69  BG Simplification    : 0.03
% 3.99/1.69  Subsumption          : 0.09
% 3.99/1.69  Abstraction          : 0.04
% 3.99/1.69  MUC search           : 0.00
% 3.99/1.69  Cooper               : 0.00
% 3.99/1.69  Total                : 0.97
% 3.99/1.69  Index Insertion      : 0.00
% 3.99/1.69  Index Deletion       : 0.00
% 3.99/1.69  Index Matching       : 0.00
% 3.99/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
