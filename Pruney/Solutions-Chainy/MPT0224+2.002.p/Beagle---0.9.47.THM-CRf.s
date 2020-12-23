%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:29 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   44 (  46 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  45 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_57,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_121,plain,(
    ! [A_38,B_39] : k2_enumset1(A_38,A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_25] : k2_enumset1(A_25,A_25,A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [B_39] : k2_tarski(B_39,B_39) = k1_tarski(B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_26])).

tff(c_24,plain,(
    ! [A_23,B_24] : k2_enumset1(A_23,A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_374,plain,(
    ! [A_61,B_62,C_63,D_64] : k2_xboole_0(k2_tarski(A_61,B_62),k2_tarski(C_63,D_64)) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1567,plain,(
    ! [A_89,B_90,C_91,D_92] : r1_tarski(k2_tarski(A_89,B_90),k2_enumset1(A_89,B_90,C_91,D_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_20])).

tff(c_1584,plain,(
    ! [A_23,B_24] : r1_tarski(k2_tarski(A_23,A_23),k2_tarski(A_23,B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1567])).

tff(c_1594,plain,(
    ! [A_93,B_94] : r1_tarski(k1_tarski(A_93),k2_tarski(A_93,B_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1584])).

tff(c_59,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_14])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(k3_xboole_0(A_45,C_46),k3_xboole_0(B_47,C_46))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,k3_xboole_0(B_49,A_48))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_169])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194,plain,(
    ! [B_49,A_48] :
      ( k3_xboole_0(B_49,A_48) = A_48
      | ~ r1_tarski(k3_xboole_0(B_49,A_48),A_48)
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_206,plain,(
    ! [B_49,A_48] :
      ( k3_xboole_0(B_49,A_48) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_194])).

tff(c_1635,plain,(
    ! [A_98,B_99] : k3_xboole_0(k2_tarski(A_98,B_99),k1_tarski(A_98)) = k1_tarski(A_98) ),
    inference(resolution,[status(thm)],[c_1594,c_206])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1692,plain,(
    ! [A_98,B_99] : k3_xboole_0(k1_tarski(A_98),k2_tarski(A_98,B_99)) = k1_tarski(A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_2])).

tff(c_28,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  %$ r1_tarski > k2_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 3.13/1.48  
% 3.13/1.48  %Foreground sorts:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Background operators:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Foreground operators:
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.48  
% 3.13/1.49  tff(f_55, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 3.13/1.49  tff(f_57, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 3.13/1.49  tff(f_53, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 3.13/1.49  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.13/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.13/1.49  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.13/1.49  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.13/1.49  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 3.13/1.49  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.13/1.49  tff(f_60, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.13/1.49  tff(c_121, plain, (![A_38, B_39]: (k2_enumset1(A_38, A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.13/1.49  tff(c_26, plain, (![A_25]: (k2_enumset1(A_25, A_25, A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.13/1.49  tff(c_128, plain, (![B_39]: (k2_tarski(B_39, B_39)=k1_tarski(B_39))), inference(superposition, [status(thm), theory('equality')], [c_121, c_26])).
% 3.13/1.49  tff(c_24, plain, (![A_23, B_24]: (k2_enumset1(A_23, A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.13/1.49  tff(c_374, plain, (![A_61, B_62, C_63, D_64]: (k2_xboole_0(k2_tarski(A_61, B_62), k2_tarski(C_63, D_64))=k2_enumset1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.13/1.49  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.13/1.49  tff(c_1567, plain, (![A_89, B_90, C_91, D_92]: (r1_tarski(k2_tarski(A_89, B_90), k2_enumset1(A_89, B_90, C_91, D_92)))), inference(superposition, [status(thm), theory('equality')], [c_374, c_20])).
% 3.13/1.49  tff(c_1584, plain, (![A_23, B_24]: (r1_tarski(k2_tarski(A_23, A_23), k2_tarski(A_23, B_24)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1567])).
% 3.13/1.49  tff(c_1594, plain, (![A_93, B_94]: (r1_tarski(k1_tarski(A_93), k2_tarski(A_93, B_94)))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1584])).
% 3.13/1.49  tff(c_59, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.49  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.49  tff(c_74, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_59, c_14])).
% 3.13/1.49  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.49  tff(c_169, plain, (![A_45, C_46, B_47]: (r1_tarski(k3_xboole_0(A_45, C_46), k3_xboole_0(B_47, C_46)) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.13/1.49  tff(c_192, plain, (![A_48, B_49]: (r1_tarski(A_48, k3_xboole_0(B_49, A_48)) | ~r1_tarski(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_6, c_169])).
% 3.13/1.49  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.13/1.49  tff(c_194, plain, (![B_49, A_48]: (k3_xboole_0(B_49, A_48)=A_48 | ~r1_tarski(k3_xboole_0(B_49, A_48), A_48) | ~r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_192, c_8])).
% 3.13/1.49  tff(c_206, plain, (![B_49, A_48]: (k3_xboole_0(B_49, A_48)=A_48 | ~r1_tarski(A_48, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_194])).
% 3.13/1.49  tff(c_1635, plain, (![A_98, B_99]: (k3_xboole_0(k2_tarski(A_98, B_99), k1_tarski(A_98))=k1_tarski(A_98))), inference(resolution, [status(thm)], [c_1594, c_206])).
% 3.13/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.49  tff(c_1692, plain, (![A_98, B_99]: (k3_xboole_0(k1_tarski(A_98), k2_tarski(A_98, B_99))=k1_tarski(A_98))), inference(superposition, [status(thm), theory('equality')], [c_1635, c_2])).
% 3.13/1.49  tff(c_28, plain, (k3_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.13/1.49  tff(c_1731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1692, c_28])).
% 3.13/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.49  
% 3.13/1.49  Inference rules
% 3.13/1.49  ----------------------
% 3.13/1.49  #Ref     : 0
% 3.13/1.49  #Sup     : 420
% 3.13/1.49  #Fact    : 0
% 3.13/1.49  #Define  : 0
% 3.13/1.49  #Split   : 0
% 3.13/1.49  #Chain   : 0
% 3.13/1.49  #Close   : 0
% 3.13/1.49  
% 3.13/1.49  Ordering : KBO
% 3.13/1.49  
% 3.13/1.49  Simplification rules
% 3.13/1.49  ----------------------
% 3.13/1.49  #Subsume      : 34
% 3.13/1.49  #Demod        : 429
% 3.13/1.49  #Tautology    : 273
% 3.13/1.49  #SimpNegUnit  : 0
% 3.13/1.49  #BackRed      : 1
% 3.13/1.49  
% 3.13/1.49  #Partial instantiations: 0
% 3.13/1.49  #Strategies tried      : 1
% 3.13/1.49  
% 3.13/1.49  Timing (in seconds)
% 3.13/1.49  ----------------------
% 3.30/1.49  Preprocessing        : 0.29
% 3.30/1.49  Parsing              : 0.16
% 3.30/1.49  CNF conversion       : 0.02
% 3.30/1.49  Main loop            : 0.44
% 3.30/1.49  Inferencing          : 0.14
% 3.30/1.49  Reduction            : 0.19
% 3.30/1.49  Demodulation         : 0.16
% 3.30/1.49  BG Simplification    : 0.02
% 3.30/1.49  Subsumption          : 0.06
% 3.30/1.49  Abstraction          : 0.03
% 3.30/1.49  MUC search           : 0.00
% 3.30/1.49  Cooper               : 0.00
% 3.30/1.49  Total                : 0.76
% 3.30/1.50  Index Insertion      : 0.00
% 3.30/1.50  Index Deletion       : 0.00
% 3.30/1.50  Index Matching       : 0.00
% 3.30/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
