%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:26 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.97s
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
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(k1_tarski(A),B)
      | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_97,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(k1_tarski(A_37),B_38) = k1_tarski(A_37)
      | r1_xboole_0(k1_tarski(A_37),B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [B_14] : ~ r1_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,(
    ! [A_37] : k3_xboole_0(k1_tarski(A_37),k1_tarski(A_37)) = k1_tarski(A_37) ),
    inference(resolution,[status(thm)],[c_97,c_16])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [B_14] : k3_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_16])).

tff(c_107,plain,(
    ! [B_14] : k1_tarski(B_14) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_48])).

tff(c_22,plain,(
    ! [A_19] : k1_setfam_1(k1_tarski(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(k1_setfam_1(A_43),k1_setfam_1(B_44)) = k1_setfam_1(k2_xboole_0(A_43,B_44))
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_148,plain,(
    ! [A_43,A_19] :
      ( k1_setfam_1(k2_xboole_0(A_43,k1_tarski(A_19))) = k3_xboole_0(k1_setfam_1(A_43),A_19)
      | k1_tarski(A_19) = k1_xboole_0
      | k1_xboole_0 = A_43 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_133])).

tff(c_154,plain,(
    ! [A_45,A_46] :
      ( k1_setfam_1(k2_xboole_0(A_45,k1_tarski(A_46))) = k3_xboole_0(k1_setfam_1(A_45),A_46)
      | k1_xboole_0 = A_45 ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_148])).

tff(c_169,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_5)),B_6) = k1_setfam_1(k2_tarski(A_5,B_6))
      | k1_tarski(A_5) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_154])).

tff(c_172,plain,(
    ! [A_5,B_6] :
      ( k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6)
      | k1_tarski(A_5) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_169])).

tff(c_173,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_172])).

tff(c_24,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:05:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.19  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.19  
% 1.97/1.19  %Foreground sorts:
% 1.97/1.19  
% 1.97/1.19  
% 1.97/1.19  %Background operators:
% 1.97/1.19  
% 1.97/1.19  
% 1.97/1.19  %Foreground operators:
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.97/1.19  
% 1.97/1.20  tff(f_48, axiom, (![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.97/1.20  tff(f_44, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.97/1.20  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.97/1.20  tff(f_60, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.97/1.20  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.97/1.20  tff(f_58, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 1.97/1.20  tff(f_63, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.97/1.20  tff(c_97, plain, (![A_37, B_38]: (k3_xboole_0(k1_tarski(A_37), B_38)=k1_tarski(A_37) | r1_xboole_0(k1_tarski(A_37), B_38))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.20  tff(c_16, plain, (![B_14]: (~r1_xboole_0(k1_tarski(B_14), k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.20  tff(c_106, plain, (![A_37]: (k3_xboole_0(k1_tarski(A_37), k1_tarski(A_37))=k1_tarski(A_37))), inference(resolution, [status(thm)], [c_97, c_16])).
% 1.97/1.20  tff(c_44, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.20  tff(c_48, plain, (![B_14]: (k3_xboole_0(k1_tarski(B_14), k1_tarski(B_14))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_16])).
% 1.97/1.20  tff(c_107, plain, (![B_14]: (k1_tarski(B_14)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_48])).
% 1.97/1.20  tff(c_22, plain, (![A_19]: (k1_setfam_1(k1_tarski(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.97/1.20  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.20  tff(c_133, plain, (![A_43, B_44]: (k3_xboole_0(k1_setfam_1(A_43), k1_setfam_1(B_44))=k1_setfam_1(k2_xboole_0(A_43, B_44)) | k1_xboole_0=B_44 | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.20  tff(c_148, plain, (![A_43, A_19]: (k1_setfam_1(k2_xboole_0(A_43, k1_tarski(A_19)))=k3_xboole_0(k1_setfam_1(A_43), A_19) | k1_tarski(A_19)=k1_xboole_0 | k1_xboole_0=A_43)), inference(superposition, [status(thm), theory('equality')], [c_22, c_133])).
% 1.97/1.20  tff(c_154, plain, (![A_45, A_46]: (k1_setfam_1(k2_xboole_0(A_45, k1_tarski(A_46)))=k3_xboole_0(k1_setfam_1(A_45), A_46) | k1_xboole_0=A_45)), inference(negUnitSimplification, [status(thm)], [c_107, c_148])).
% 1.97/1.20  tff(c_169, plain, (![A_5, B_6]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_5)), B_6)=k1_setfam_1(k2_tarski(A_5, B_6)) | k1_tarski(A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_154])).
% 1.97/1.20  tff(c_172, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6) | k1_tarski(A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_169])).
% 1.97/1.20  tff(c_173, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(negUnitSimplification, [status(thm)], [c_107, c_172])).
% 1.97/1.20  tff(c_24, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.97/1.20  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_24])).
% 1.97/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  Inference rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Ref     : 0
% 1.97/1.20  #Sup     : 34
% 1.97/1.20  #Fact    : 0
% 1.97/1.20  #Define  : 0
% 1.97/1.20  #Split   : 0
% 1.97/1.20  #Chain   : 0
% 1.97/1.20  #Close   : 0
% 1.97/1.20  
% 1.97/1.20  Ordering : KBO
% 1.97/1.20  
% 1.97/1.20  Simplification rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Subsume      : 0
% 1.97/1.20  #Demod        : 4
% 1.97/1.20  #Tautology    : 22
% 1.97/1.20  #SimpNegUnit  : 3
% 1.97/1.20  #BackRed      : 2
% 1.97/1.20  
% 1.97/1.20  #Partial instantiations: 0
% 1.97/1.20  #Strategies tried      : 1
% 1.97/1.20  
% 1.97/1.20  Timing (in seconds)
% 1.97/1.20  ----------------------
% 1.97/1.20  Preprocessing        : 0.31
% 1.97/1.20  Parsing              : 0.16
% 1.97/1.20  CNF conversion       : 0.02
% 1.97/1.20  Main loop            : 0.14
% 1.97/1.20  Inferencing          : 0.06
% 1.97/1.20  Reduction            : 0.04
% 1.97/1.20  Demodulation         : 0.03
% 1.97/1.20  BG Simplification    : 0.01
% 1.97/1.20  Subsumption          : 0.02
% 1.97/1.20  Abstraction          : 0.01
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.20  Total                : 0.48
% 1.97/1.20  Index Insertion      : 0.00
% 1.97/1.20  Index Deletion       : 0.00
% 1.97/1.20  Index Matching       : 0.00
% 1.97/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
