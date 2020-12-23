%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:26 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  53 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_31,B_32] : k3_xboole_0(k1_tarski(A_31),k2_tarski(A_31,B_32)) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_95,plain,(
    ! [A_7] : k3_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_52,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [B_11] : ~ r1_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [B_11] : k3_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_14])).

tff(c_98,plain,(
    ! [B_11] : k1_tarski(B_11) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_60])).

tff(c_20,plain,(
    ! [A_16] : k1_setfam_1(k1_tarski(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(k1_setfam_1(A_37),k1_setfam_1(B_38)) = k1_setfam_1(k2_xboole_0(A_37,B_38))
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_140,plain,(
    ! [A_16,B_38] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_16),B_38)) = k3_xboole_0(A_16,k1_setfam_1(B_38))
      | k1_xboole_0 = B_38
      | k1_tarski(A_16) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_128])).

tff(c_148,plain,(
    ! [A_39,B_40] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_39),B_40)) = k3_xboole_0(A_39,k1_setfam_1(B_40))
      | k1_xboole_0 = B_40 ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_140])).

tff(c_163,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,k1_setfam_1(k1_tarski(B_6))) = k1_setfam_1(k2_tarski(A_5,B_6))
      | k1_tarski(B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_148])).

tff(c_166,plain,(
    ! [A_5,B_6] :
      ( k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6)
      | k1_tarski(B_6) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_163])).

tff(c_167,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_166])).

tff(c_22,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:05:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.55  
% 2.25/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.55  %$ r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.25/1.55  
% 2.25/1.55  %Foreground sorts:
% 2.25/1.55  
% 2.25/1.55  
% 2.25/1.55  %Background operators:
% 2.25/1.55  
% 2.25/1.55  
% 2.25/1.55  %Foreground operators:
% 2.25/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.55  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.55  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.25/1.55  
% 2.25/1.57  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.25/1.57  tff(f_44, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.25/1.57  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.25/1.57  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.25/1.57  tff(f_56, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.25/1.57  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.25/1.57  tff(f_54, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.25/1.57  tff(f_59, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.25/1.57  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.57  tff(c_86, plain, (![A_31, B_32]: (k3_xboole_0(k1_tarski(A_31), k2_tarski(A_31, B_32))=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.57  tff(c_95, plain, (![A_7]: (k3_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_86])).
% 2.25/1.57  tff(c_52, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.57  tff(c_14, plain, (![B_11]: (~r1_xboole_0(k1_tarski(B_11), k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.57  tff(c_60, plain, (![B_11]: (k3_xboole_0(k1_tarski(B_11), k1_tarski(B_11))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_14])).
% 2.25/1.57  tff(c_98, plain, (![B_11]: (k1_tarski(B_11)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_60])).
% 2.25/1.57  tff(c_20, plain, (![A_16]: (k1_setfam_1(k1_tarski(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.25/1.57  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.57  tff(c_128, plain, (![A_37, B_38]: (k3_xboole_0(k1_setfam_1(A_37), k1_setfam_1(B_38))=k1_setfam_1(k2_xboole_0(A_37, B_38)) | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.25/1.57  tff(c_140, plain, (![A_16, B_38]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_16), B_38))=k3_xboole_0(A_16, k1_setfam_1(B_38)) | k1_xboole_0=B_38 | k1_tarski(A_16)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_128])).
% 2.25/1.57  tff(c_148, plain, (![A_39, B_40]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_39), B_40))=k3_xboole_0(A_39, k1_setfam_1(B_40)) | k1_xboole_0=B_40)), inference(negUnitSimplification, [status(thm)], [c_98, c_140])).
% 2.25/1.57  tff(c_163, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k1_setfam_1(k1_tarski(B_6)))=k1_setfam_1(k2_tarski(A_5, B_6)) | k1_tarski(B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_148])).
% 2.25/1.57  tff(c_166, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6) | k1_tarski(B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_163])).
% 2.25/1.57  tff(c_167, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(negUnitSimplification, [status(thm)], [c_98, c_166])).
% 2.25/1.57  tff(c_22, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.57  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_22])).
% 2.25/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.57  
% 2.25/1.57  Inference rules
% 2.25/1.57  ----------------------
% 2.25/1.57  #Ref     : 0
% 2.25/1.57  #Sup     : 34
% 2.25/1.57  #Fact    : 0
% 2.25/1.57  #Define  : 0
% 2.25/1.57  #Split   : 0
% 2.25/1.57  #Chain   : 0
% 2.25/1.57  #Close   : 0
% 2.25/1.57  
% 2.25/1.57  Ordering : KBO
% 2.25/1.57  
% 2.25/1.57  Simplification rules
% 2.25/1.57  ----------------------
% 2.25/1.57  #Subsume      : 0
% 2.25/1.57  #Demod        : 4
% 2.25/1.57  #Tautology    : 22
% 2.25/1.57  #SimpNegUnit  : 3
% 2.25/1.57  #BackRed      : 2
% 2.25/1.57  
% 2.25/1.57  #Partial instantiations: 0
% 2.25/1.57  #Strategies tried      : 1
% 2.25/1.57  
% 2.25/1.57  Timing (in seconds)
% 2.25/1.57  ----------------------
% 2.25/1.57  Preprocessing        : 0.46
% 2.25/1.57  Parsing              : 0.23
% 2.25/1.57  CNF conversion       : 0.03
% 2.25/1.57  Main loop            : 0.22
% 2.25/1.57  Inferencing          : 0.09
% 2.25/1.57  Reduction            : 0.07
% 2.25/1.57  Demodulation         : 0.05
% 2.25/1.58  BG Simplification    : 0.02
% 2.25/1.58  Subsumption          : 0.03
% 2.25/1.58  Abstraction          : 0.02
% 2.25/1.58  MUC search           : 0.00
% 2.25/1.58  Cooper               : 0.00
% 2.25/1.58  Total                : 0.72
% 2.25/1.58  Index Insertion      : 0.00
% 2.25/1.58  Index Deletion       : 0.00
% 2.25/1.58  Index Matching       : 0.00
% 2.25/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
