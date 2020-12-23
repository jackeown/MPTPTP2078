%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:26 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.98s
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
%$ r1_xboole_0 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_8,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_30,B_31] : k3_xboole_0(k1_tarski(A_30),k2_tarski(A_30,B_31)) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [A_5] : k3_xboole_0(k1_tarski(A_5),k1_tarski(A_5)) = k1_tarski(A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [B_11] : ~ r1_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    ! [B_11] : k3_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_14])).

tff(c_103,plain,(
    ! [B_11] : k1_tarski(B_11) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_46])).

tff(c_20,plain,(
    ! [A_16] : k1_setfam_1(k1_tarski(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(k1_setfam_1(A_37),k1_setfam_1(B_38)) = k1_setfam_1(k2_xboole_0(A_37,B_38))
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_154,plain,(
    ! [A_37,A_16] :
      ( k1_setfam_1(k2_xboole_0(A_37,k1_tarski(A_16))) = k3_xboole_0(k1_setfam_1(A_37),A_16)
      | k1_tarski(A_16) = k1_xboole_0
      | k1_xboole_0 = A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_142])).

tff(c_160,plain,(
    ! [A_39,A_40] :
      ( k1_setfam_1(k2_xboole_0(A_39,k1_tarski(A_40))) = k3_xboole_0(k1_setfam_1(A_39),A_40)
      | k1_xboole_0 = A_39 ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_154])).

tff(c_175,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_3)),B_4) = k1_setfam_1(k2_tarski(A_3,B_4))
      | k1_tarski(A_3) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_160])).

tff(c_182,plain,(
    ! [A_3,B_4] :
      ( k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4)
      | k1_tarski(A_3) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_175])).

tff(c_183,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_182])).

tff(c_22,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 10:30:30 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  %$ r1_xboole_0 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.98/1.22  
% 1.98/1.23  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.98/1.23  tff(f_44, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 1.98/1.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.98/1.23  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.98/1.23  tff(f_56, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.98/1.23  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.98/1.23  tff(f_54, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 1.98/1.23  tff(f_59, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.98/1.23  tff(c_8, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.23  tff(c_91, plain, (![A_30, B_31]: (k3_xboole_0(k1_tarski(A_30), k2_tarski(A_30, B_31))=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.23  tff(c_100, plain, (![A_5]: (k3_xboole_0(k1_tarski(A_5), k1_tarski(A_5))=k1_tarski(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_91])).
% 1.98/1.23  tff(c_42, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.23  tff(c_14, plain, (![B_11]: (~r1_xboole_0(k1_tarski(B_11), k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.98/1.23  tff(c_46, plain, (![B_11]: (k3_xboole_0(k1_tarski(B_11), k1_tarski(B_11))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_14])).
% 1.98/1.23  tff(c_103, plain, (![B_11]: (k1_tarski(B_11)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_46])).
% 1.98/1.23  tff(c_20, plain, (![A_16]: (k1_setfam_1(k1_tarski(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.23  tff(c_6, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4))=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.23  tff(c_142, plain, (![A_37, B_38]: (k3_xboole_0(k1_setfam_1(A_37), k1_setfam_1(B_38))=k1_setfam_1(k2_xboole_0(A_37, B_38)) | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.23  tff(c_154, plain, (![A_37, A_16]: (k1_setfam_1(k2_xboole_0(A_37, k1_tarski(A_16)))=k3_xboole_0(k1_setfam_1(A_37), A_16) | k1_tarski(A_16)=k1_xboole_0 | k1_xboole_0=A_37)), inference(superposition, [status(thm), theory('equality')], [c_20, c_142])).
% 1.98/1.23  tff(c_160, plain, (![A_39, A_40]: (k1_setfam_1(k2_xboole_0(A_39, k1_tarski(A_40)))=k3_xboole_0(k1_setfam_1(A_39), A_40) | k1_xboole_0=A_39)), inference(negUnitSimplification, [status(thm)], [c_103, c_154])).
% 1.98/1.23  tff(c_175, plain, (![A_3, B_4]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_3)), B_4)=k1_setfam_1(k2_tarski(A_3, B_4)) | k1_tarski(A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_160])).
% 1.98/1.23  tff(c_182, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4) | k1_tarski(A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_175])).
% 1.98/1.23  tff(c_183, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(negUnitSimplification, [status(thm)], [c_103, c_182])).
% 1.98/1.23  tff(c_22, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.98/1.23  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_22])).
% 1.98/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  Inference rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Ref     : 0
% 1.98/1.23  #Sup     : 48
% 1.98/1.23  #Fact    : 0
% 1.98/1.23  #Define  : 0
% 1.98/1.23  #Split   : 0
% 1.98/1.23  #Chain   : 0
% 1.98/1.23  #Close   : 0
% 1.98/1.23  
% 1.98/1.23  Ordering : KBO
% 1.98/1.23  
% 1.98/1.23  Simplification rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Subsume      : 0
% 1.98/1.23  #Demod        : 19
% 1.98/1.23  #Tautology    : 34
% 1.98/1.23  #SimpNegUnit  : 7
% 1.98/1.23  #BackRed      : 2
% 1.98/1.23  
% 1.98/1.23  #Partial instantiations: 0
% 1.98/1.23  #Strategies tried      : 1
% 1.98/1.23  
% 1.98/1.23  Timing (in seconds)
% 1.98/1.23  ----------------------
% 1.98/1.23  Preprocessing        : 0.30
% 1.98/1.23  Parsing              : 0.16
% 1.98/1.23  CNF conversion       : 0.02
% 1.98/1.23  Main loop            : 0.16
% 1.98/1.23  Inferencing          : 0.07
% 1.98/1.23  Reduction            : 0.05
% 1.98/1.23  Demodulation         : 0.04
% 1.98/1.23  BG Simplification    : 0.01
% 1.98/1.23  Subsumption          : 0.02
% 1.98/1.23  Abstraction          : 0.01
% 1.98/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.48
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
