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
% DateTime   : Thu Dec  3 09:48:29 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(k1_tarski(A_11),k1_tarski(B_12))
      | B_12 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(k1_tarski(A_29),k1_tarski(B_30)) = k1_tarski(A_29)
      | B_30 = A_29 ) ),
    inference(resolution,[status(thm)],[c_14,c_30])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(k1_tarski(A_37),k1_tarski(A_37)) = k3_xboole_0(k1_tarski(A_37),k1_tarski(B_38))
      | B_38 = A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_35,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k4_xboole_0(A_20,B_21) != A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [B_10] : ~ r1_xboole_0(k1_tarski(B_10),k1_tarski(B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [B_10] : k4_xboole_0(k1_tarski(B_10),k1_tarski(B_10)) != k1_tarski(B_10) ),
    inference(resolution,[status(thm)],[c_35,c_12])).

tff(c_231,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(k1_tarski(A_39),k1_tarski(B_40)) != k1_tarski(A_39)
      | B_40 = A_39 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_43])).

tff(c_237,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_231])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.93/1.27  
% 1.93/1.27  %Foreground sorts:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Background operators:
% 1.93/1.27  
% 1.93/1.27  
% 1.93/1.27  %Foreground operators:
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.27  
% 1.93/1.27  tff(f_56, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.93/1.27  tff(f_47, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.93/1.27  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.93/1.27  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.93/1.27  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.93/1.27  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.27  tff(c_20, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.27  tff(c_14, plain, (![A_11, B_12]: (r1_xboole_0(k1_tarski(A_11), k1_tarski(B_12)) | B_12=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.27  tff(c_30, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.27  tff(c_78, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), k1_tarski(B_30))=k1_tarski(A_29) | B_30=A_29)), inference(resolution, [status(thm)], [c_14, c_30])).
% 1.93/1.27  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.27  tff(c_189, plain, (![A_37, B_38]: (k4_xboole_0(k1_tarski(A_37), k1_tarski(A_37))=k3_xboole_0(k1_tarski(A_37), k1_tarski(B_38)) | B_38=A_37)), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 1.93/1.27  tff(c_35, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k4_xboole_0(A_20, B_21)!=A_20)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.27  tff(c_12, plain, (![B_10]: (~r1_xboole_0(k1_tarski(B_10), k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.93/1.27  tff(c_43, plain, (![B_10]: (k4_xboole_0(k1_tarski(B_10), k1_tarski(B_10))!=k1_tarski(B_10))), inference(resolution, [status(thm)], [c_35, c_12])).
% 1.93/1.27  tff(c_231, plain, (![A_39, B_40]: (k3_xboole_0(k1_tarski(A_39), k1_tarski(B_40))!=k1_tarski(A_39) | B_40=A_39)), inference(superposition, [status(thm), theory('equality')], [c_189, c_43])).
% 1.93/1.27  tff(c_237, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_20, c_231])).
% 1.93/1.27  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_237])).
% 1.93/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  
% 1.93/1.27  Inference rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Ref     : 0
% 1.93/1.27  #Sup     : 56
% 1.93/1.27  #Fact    : 0
% 1.93/1.27  #Define  : 0
% 1.93/1.27  #Split   : 0
% 1.93/1.27  #Chain   : 0
% 1.93/1.27  #Close   : 0
% 1.93/1.27  
% 1.93/1.27  Ordering : KBO
% 1.93/1.27  
% 1.93/1.27  Simplification rules
% 1.93/1.28  ----------------------
% 1.93/1.28  #Subsume      : 2
% 1.93/1.28  #Demod        : 9
% 1.93/1.28  #Tautology    : 24
% 1.93/1.28  #SimpNegUnit  : 1
% 1.93/1.28  #BackRed      : 0
% 1.93/1.28  
% 1.93/1.28  #Partial instantiations: 0
% 1.93/1.28  #Strategies tried      : 1
% 1.93/1.28  
% 1.93/1.28  Timing (in seconds)
% 1.93/1.28  ----------------------
% 1.93/1.28  Preprocessing        : 0.30
% 1.93/1.28  Parsing              : 0.16
% 1.93/1.28  CNF conversion       : 0.02
% 1.93/1.28  Main loop            : 0.16
% 1.93/1.28  Inferencing          : 0.07
% 1.93/1.28  Reduction            : 0.05
% 1.93/1.28  Demodulation         : 0.04
% 1.93/1.28  BG Simplification    : 0.01
% 1.93/1.28  Subsumption          : 0.02
% 1.93/1.28  Abstraction          : 0.01
% 1.93/1.28  MUC search           : 0.00
% 1.93/1.28  Cooper               : 0.00
% 1.93/1.28  Total                : 0.49
% 1.93/1.28  Index Insertion      : 0.00
% 1.93/1.28  Index Deletion       : 0.00
% 1.93/1.28  Index Matching       : 0.00
% 1.93/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
