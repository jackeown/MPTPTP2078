%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:21 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  59 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(k1_tarski(A),B)
      | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_172,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(k1_tarski(A_41),B_42) = k1_tarski(A_41)
      | r1_xboole_0(k1_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [B_15] : ~ r1_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_181,plain,(
    ! [A_41] : k3_xboole_0(k1_tarski(A_41),k1_tarski(A_41)) = k1_tarski(A_41) ),
    inference(resolution,[status(thm)],[c_172,c_18])).

tff(c_118,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [B_15] : k3_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_118,c_18])).

tff(c_182,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_126])).

tff(c_24,plain,(
    ! [A_20] : k1_setfam_1(k1_tarski(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_214,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(k1_setfam_1(A_47),k1_setfam_1(B_48)) = k1_setfam_1(k2_xboole_0(A_47,B_48))
      | k1_xboole_0 = B_48
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_241,plain,(
    ! [A_47,A_20] :
      ( k1_setfam_1(k2_xboole_0(A_47,k1_tarski(A_20))) = k3_xboole_0(k1_setfam_1(A_47),A_20)
      | k1_tarski(A_20) = k1_xboole_0
      | k1_xboole_0 = A_47 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_214])).

tff(c_284,plain,(
    ! [A_51,A_52] :
      ( k1_setfam_1(k2_xboole_0(A_51,k1_tarski(A_52))) = k3_xboole_0(k1_setfam_1(A_51),A_52)
      | k1_xboole_0 = A_51 ) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_241])).

tff(c_299,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_7)),B_8) = k1_setfam_1(k2_tarski(A_7,B_8))
      | k1_tarski(A_7) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_284])).

tff(c_306,plain,(
    ! [A_7,B_8] :
      ( k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8)
      | k1_tarski(A_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_299])).

tff(c_307,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_306])).

tff(c_26,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:00:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  %$ r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.13/1.24  
% 2.13/1.24  %Foreground sorts:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Background operators:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Foreground operators:
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.24  
% 2.13/1.25  tff(f_50, axiom, (![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.13/1.25  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.13/1.25  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.13/1.25  tff(f_62, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.13/1.25  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.13/1.25  tff(f_60, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.13/1.25  tff(f_65, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.13/1.25  tff(c_172, plain, (![A_41, B_42]: (k3_xboole_0(k1_tarski(A_41), B_42)=k1_tarski(A_41) | r1_xboole_0(k1_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.25  tff(c_18, plain, (![B_15]: (~r1_xboole_0(k1_tarski(B_15), k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.25  tff(c_181, plain, (![A_41]: (k3_xboole_0(k1_tarski(A_41), k1_tarski(A_41))=k1_tarski(A_41))), inference(resolution, [status(thm)], [c_172, c_18])).
% 2.13/1.25  tff(c_118, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.25  tff(c_126, plain, (![B_15]: (k3_xboole_0(k1_tarski(B_15), k1_tarski(B_15))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_118, c_18])).
% 2.13/1.25  tff(c_182, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_181, c_126])).
% 2.13/1.25  tff(c_24, plain, (![A_20]: (k1_setfam_1(k1_tarski(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.13/1.25  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.25  tff(c_214, plain, (![A_47, B_48]: (k3_xboole_0(k1_setfam_1(A_47), k1_setfam_1(B_48))=k1_setfam_1(k2_xboole_0(A_47, B_48)) | k1_xboole_0=B_48 | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.25  tff(c_241, plain, (![A_47, A_20]: (k1_setfam_1(k2_xboole_0(A_47, k1_tarski(A_20)))=k3_xboole_0(k1_setfam_1(A_47), A_20) | k1_tarski(A_20)=k1_xboole_0 | k1_xboole_0=A_47)), inference(superposition, [status(thm), theory('equality')], [c_24, c_214])).
% 2.13/1.25  tff(c_284, plain, (![A_51, A_52]: (k1_setfam_1(k2_xboole_0(A_51, k1_tarski(A_52)))=k3_xboole_0(k1_setfam_1(A_51), A_52) | k1_xboole_0=A_51)), inference(negUnitSimplification, [status(thm)], [c_182, c_241])).
% 2.13/1.25  tff(c_299, plain, (![A_7, B_8]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_7)), B_8)=k1_setfam_1(k2_tarski(A_7, B_8)) | k1_tarski(A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_284])).
% 2.13/1.25  tff(c_306, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8) | k1_tarski(A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_299])).
% 2.13/1.25  tff(c_307, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(negUnitSimplification, [status(thm)], [c_182, c_306])).
% 2.13/1.25  tff(c_26, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.13/1.25  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_26])).
% 2.13/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  Inference rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Ref     : 0
% 2.13/1.25  #Sup     : 83
% 2.13/1.25  #Fact    : 1
% 2.13/1.25  #Define  : 0
% 2.13/1.25  #Split   : 0
% 2.13/1.25  #Chain   : 0
% 2.13/1.25  #Close   : 0
% 2.13/1.25  
% 2.13/1.25  Ordering : KBO
% 2.13/1.25  
% 2.13/1.25  Simplification rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Subsume      : 1
% 2.13/1.25  #Demod        : 16
% 2.13/1.25  #Tautology    : 51
% 2.13/1.25  #SimpNegUnit  : 6
% 2.13/1.25  #BackRed      : 2
% 2.13/1.25  
% 2.13/1.25  #Partial instantiations: 0
% 2.13/1.25  #Strategies tried      : 1
% 2.13/1.25  
% 2.13/1.25  Timing (in seconds)
% 2.13/1.25  ----------------------
% 2.13/1.26  Preprocessing        : 0.30
% 2.13/1.26  Parsing              : 0.16
% 2.13/1.26  CNF conversion       : 0.02
% 2.13/1.26  Main loop            : 0.21
% 2.13/1.26  Inferencing          : 0.08
% 2.13/1.26  Reduction            : 0.07
% 2.13/1.26  Demodulation         : 0.06
% 2.13/1.26  BG Simplification    : 0.01
% 2.13/1.26  Subsumption          : 0.03
% 2.13/1.26  Abstraction          : 0.01
% 2.13/1.26  MUC search           : 0.00
% 2.13/1.26  Cooper               : 0.00
% 2.13/1.26  Total                : 0.53
% 2.13/1.26  Index Insertion      : 0.00
% 2.13/1.26  Index Deletion       : 0.00
% 2.13/1.26  Index Matching       : 0.00
% 2.13/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
