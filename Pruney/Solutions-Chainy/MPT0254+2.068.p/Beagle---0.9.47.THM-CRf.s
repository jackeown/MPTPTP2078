%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:28 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 104 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 ( 105 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,(
    ! [A_43] : k2_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(resolution,[status(thm)],[c_6,c_158])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_203,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_2])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(B_38,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_10])).

tff(c_130,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_121])).

tff(c_174,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_158])).

tff(c_226,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_174])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_291,plain,(
    ! [A_49] : r1_xboole_0(A_49,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_8])).

tff(c_38,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden(A_23,B_24)
      | ~ r1_xboole_0(k1_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_296,plain,(
    ! [A_23] : ~ r2_hidden(A_23,'#skF_4') ),
    inference(resolution,[status(thm)],[c_291,c_38])).

tff(c_277,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_40])).

tff(c_213,plain,(
    ! [B_2] : k2_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_298,plain,(
    ! [B_2] : k2_xboole_0(B_2,'#skF_4') = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_213])).

tff(c_333,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_298])).

tff(c_32,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    ! [D_30,A_31] : r2_hidden(D_30,k2_tarski(A_31,D_30)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_60])).

tff(c_367,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_63])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.23/1.34  
% 2.23/1.34  %Foreground sorts:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Background operators:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Foreground operators:
% 2.23/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.34  
% 2.23/1.36  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.23/1.36  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.23/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.23/1.36  tff(f_63, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.23/1.36  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.23/1.36  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.36  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.23/1.36  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/1.36  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.23/1.36  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.36  tff(c_158, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.36  tff(c_191, plain, (![A_43]: (k2_xboole_0(k1_xboole_0, A_43)=A_43)), inference(resolution, [status(thm)], [c_6, c_158])).
% 2.23/1.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.36  tff(c_203, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_191, c_2])).
% 2.23/1.36  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.23/1.36  tff(c_70, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.36  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.36  tff(c_121, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(B_38, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_10])).
% 2.23/1.36  tff(c_130, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_121])).
% 2.23/1.36  tff(c_174, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_158])).
% 2.23/1.36  tff(c_226, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_174])).
% 2.23/1.36  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.36  tff(c_291, plain, (![A_49]: (r1_xboole_0(A_49, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_8])).
% 2.23/1.36  tff(c_38, plain, (![A_23, B_24]: (~r2_hidden(A_23, B_24) | ~r1_xboole_0(k1_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.36  tff(c_296, plain, (![A_23]: (~r2_hidden(A_23, '#skF_4'))), inference(resolution, [status(thm)], [c_291, c_38])).
% 2.23/1.36  tff(c_277, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_40])).
% 2.23/1.36  tff(c_213, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 2.23/1.36  tff(c_298, plain, (![B_2]: (k2_xboole_0(B_2, '#skF_4')=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_226, c_213])).
% 2.23/1.36  tff(c_333, plain, (k1_tarski('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_277, c_298])).
% 2.23/1.36  tff(c_32, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.23/1.36  tff(c_60, plain, (![D_30, A_31]: (r2_hidden(D_30, k2_tarski(A_31, D_30)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.23/1.36  tff(c_63, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_60])).
% 2.23/1.36  tff(c_367, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_333, c_63])).
% 2.23/1.36  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_296, c_367])).
% 2.23/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.36  
% 2.23/1.36  Inference rules
% 2.23/1.36  ----------------------
% 2.23/1.36  #Ref     : 0
% 2.23/1.36  #Sup     : 84
% 2.23/1.36  #Fact    : 0
% 2.23/1.36  #Define  : 0
% 2.23/1.36  #Split   : 0
% 2.23/1.36  #Chain   : 0
% 2.23/1.36  #Close   : 0
% 2.23/1.36  
% 2.23/1.36  Ordering : KBO
% 2.23/1.36  
% 2.23/1.36  Simplification rules
% 2.23/1.36  ----------------------
% 2.23/1.36  #Subsume      : 0
% 2.23/1.36  #Demod        : 34
% 2.23/1.36  #Tautology    : 54
% 2.23/1.36  #SimpNegUnit  : 1
% 2.23/1.36  #BackRed      : 10
% 2.23/1.36  
% 2.23/1.36  #Partial instantiations: 0
% 2.23/1.36  #Strategies tried      : 1
% 2.23/1.36  
% 2.23/1.36  Timing (in seconds)
% 2.23/1.36  ----------------------
% 2.23/1.36  Preprocessing        : 0.34
% 2.23/1.36  Parsing              : 0.17
% 2.23/1.36  CNF conversion       : 0.02
% 2.23/1.36  Main loop            : 0.20
% 2.23/1.36  Inferencing          : 0.07
% 2.23/1.36  Reduction            : 0.08
% 2.23/1.36  Demodulation         : 0.06
% 2.23/1.36  BG Simplification    : 0.02
% 2.23/1.36  Subsumption          : 0.03
% 2.23/1.36  Abstraction          : 0.01
% 2.23/1.36  MUC search           : 0.00
% 2.23/1.36  Cooper               : 0.00
% 2.23/1.36  Total                : 0.57
% 2.23/1.36  Index Insertion      : 0.00
% 2.23/1.36  Index Deletion       : 0.00
% 2.23/1.36  Index Matching       : 0.00
% 2.23/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
