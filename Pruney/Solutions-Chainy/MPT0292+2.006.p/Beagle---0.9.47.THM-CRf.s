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
% DateTime   : Thu Dec  3 09:53:35 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  47 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_26,plain,(
    ! [A_13] : r1_tarski(k1_tarski(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    ! [A_5] : k3_tarski(k1_tarski(A_5)) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_69,plain,(
    ! [A_5] : k3_tarski(k1_tarski(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_94,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k3_tarski(A_32),k3_tarski(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_110,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,k3_tarski(B_35))
      | ~ r1_tarski(k1_tarski(A_34),B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_94])).

tff(c_118,plain,(
    ! [A_13] : r1_tarski(A_13,k3_tarski(k1_zfmisc_1(A_13))) ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_149,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_3'(A_40,B_41),A_40)
      | r1_tarski(k3_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_205,plain,(
    ! [A_55,B_56] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_55),B_56),A_55)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_55)),B_56) ) ),
    inference(resolution,[status(thm)],[c_149,c_12])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( ~ r1_tarski('#skF_3'(A_14,B_15),B_15)
      | r1_tarski(k3_tarski(A_14),B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    ! [A_59] : r1_tarski(k3_tarski(k1_zfmisc_1(A_59)),A_59) ),
    inference(resolution,[status(thm)],[c_205,c_28])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_230,plain,(
    ! [A_59] :
      ( k3_tarski(k1_zfmisc_1(A_59)) = A_59
      | ~ r1_tarski(A_59,k3_tarski(k1_zfmisc_1(A_59))) ) ),
    inference(resolution,[status(thm)],[c_228,c_4])).

tff(c_233,plain,(
    ! [A_59] : k3_tarski(k1_zfmisc_1(A_59)) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_230])).

tff(c_34,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_34])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.29  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.03/1.29  
% 2.03/1.29  %Foreground sorts:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Background operators:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Foreground operators:
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.03/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.29  
% 2.03/1.30  tff(f_46, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 2.03/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.03/1.30  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.03/1.30  tff(f_44, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.03/1.30  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.03/1.30  tff(f_53, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.03/1.30  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.03/1.30  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.03/1.30  tff(f_60, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.03/1.30  tff(c_26, plain, (![A_13]: (r1_tarski(k1_tarski(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.30  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.30  tff(c_10, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.30  tff(c_57, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.03/1.30  tff(c_66, plain, (![A_5]: (k3_tarski(k1_tarski(A_5))=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 2.03/1.30  tff(c_69, plain, (![A_5]: (k3_tarski(k1_tarski(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_66])).
% 2.03/1.30  tff(c_94, plain, (![A_32, B_33]: (r1_tarski(k3_tarski(A_32), k3_tarski(B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.03/1.30  tff(c_110, plain, (![A_34, B_35]: (r1_tarski(A_34, k3_tarski(B_35)) | ~r1_tarski(k1_tarski(A_34), B_35))), inference(superposition, [status(thm), theory('equality')], [c_69, c_94])).
% 2.03/1.30  tff(c_118, plain, (![A_13]: (r1_tarski(A_13, k3_tarski(k1_zfmisc_1(A_13))))), inference(resolution, [status(thm)], [c_26, c_110])).
% 2.03/1.30  tff(c_149, plain, (![A_40, B_41]: (r2_hidden('#skF_3'(A_40, B_41), A_40) | r1_tarski(k3_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.03/1.30  tff(c_12, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.30  tff(c_205, plain, (![A_55, B_56]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_55), B_56), A_55) | r1_tarski(k3_tarski(k1_zfmisc_1(A_55)), B_56))), inference(resolution, [status(thm)], [c_149, c_12])).
% 2.03/1.30  tff(c_28, plain, (![A_14, B_15]: (~r1_tarski('#skF_3'(A_14, B_15), B_15) | r1_tarski(k3_tarski(A_14), B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.03/1.30  tff(c_228, plain, (![A_59]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_59)), A_59))), inference(resolution, [status(thm)], [c_205, c_28])).
% 2.03/1.30  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.30  tff(c_230, plain, (![A_59]: (k3_tarski(k1_zfmisc_1(A_59))=A_59 | ~r1_tarski(A_59, k3_tarski(k1_zfmisc_1(A_59))))), inference(resolution, [status(thm)], [c_228, c_4])).
% 2.03/1.30  tff(c_233, plain, (![A_59]: (k3_tarski(k1_zfmisc_1(A_59))=A_59)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_230])).
% 2.03/1.30  tff(c_34, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.30  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_34])).
% 2.03/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  Inference rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Ref     : 0
% 2.03/1.30  #Sup     : 43
% 2.03/1.30  #Fact    : 0
% 2.03/1.30  #Define  : 0
% 2.03/1.30  #Split   : 0
% 2.03/1.30  #Chain   : 0
% 2.03/1.30  #Close   : 0
% 2.03/1.30  
% 2.03/1.30  Ordering : KBO
% 2.03/1.30  
% 2.03/1.30  Simplification rules
% 2.03/1.30  ----------------------
% 2.03/1.30  #Subsume      : 1
% 2.03/1.30  #Demod        : 23
% 2.03/1.30  #Tautology    : 18
% 2.03/1.30  #SimpNegUnit  : 0
% 2.03/1.30  #BackRed      : 7
% 2.03/1.30  
% 2.03/1.30  #Partial instantiations: 0
% 2.03/1.30  #Strategies tried      : 1
% 2.03/1.30  
% 2.03/1.30  Timing (in seconds)
% 2.03/1.30  ----------------------
% 2.03/1.30  Preprocessing        : 0.32
% 2.03/1.30  Parsing              : 0.16
% 2.03/1.30  CNF conversion       : 0.02
% 2.03/1.30  Main loop            : 0.19
% 2.03/1.30  Inferencing          : 0.07
% 2.03/1.30  Reduction            : 0.06
% 2.03/1.30  Demodulation         : 0.04
% 2.03/1.30  BG Simplification    : 0.01
% 2.03/1.30  Subsumption          : 0.04
% 2.03/1.30  Abstraction          : 0.01
% 2.03/1.30  MUC search           : 0.00
% 2.03/1.30  Cooper               : 0.00
% 2.03/1.30  Total                : 0.53
% 2.03/1.30  Index Insertion      : 0.00
% 2.03/1.30  Index Deletion       : 0.00
% 2.03/1.30  Index Matching       : 0.00
% 2.03/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
