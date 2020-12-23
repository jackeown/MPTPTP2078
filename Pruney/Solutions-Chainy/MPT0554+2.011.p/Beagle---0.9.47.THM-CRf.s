%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:04 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  54 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( r1_tarski(C_5,'#skF_1'(A_3,B_4,C_5))
      | k2_xboole_0(A_3,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [B_32,A_33,C_34] :
      ( ~ r1_tarski(B_32,'#skF_1'(A_33,B_32,C_34))
      | k2_xboole_0(A_33,C_34) = B_32
      | ~ r1_tarski(C_34,B_32)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(B_4,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_78])).

tff(c_86,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_106,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_51,plain,(
    ! [C_21,A_22,B_23] :
      ( k2_xboole_0(k9_relat_1(C_21,A_22),k9_relat_1(C_21,B_23)) = k9_relat_1(C_21,k2_xboole_0(A_22,B_23))
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [C_21,A_22,B_23] :
      ( r1_tarski(k9_relat_1(C_21,A_22),k9_relat_1(C_21,k2_xboole_0(A_22,B_23)))
      | ~ v1_relat_1(C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_14])).

tff(c_308,plain,(
    ! [C_47] :
      ( r1_tarski(k9_relat_1(C_47,'#skF_2'),k9_relat_1(C_47,'#skF_3'))
      | ~ v1_relat_1(C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_57])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_319,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_308,c_20])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.30  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.06/1.30  
% 2.06/1.30  %Foreground sorts:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Background operators:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Foreground operators:
% 2.06/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.06/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.30  
% 2.06/1.31  tff(f_59, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 2.06/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/1.31  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 2.06/1.31  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 2.06/1.31  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.06/1.31  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.31  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.31  tff(c_10, plain, (![C_5, A_3, B_4]: (r1_tarski(C_5, '#skF_1'(A_3, B_4, C_5)) | k2_xboole_0(A_3, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.31  tff(c_78, plain, (![B_32, A_33, C_34]: (~r1_tarski(B_32, '#skF_1'(A_33, B_32, C_34)) | k2_xboole_0(A_33, C_34)=B_32 | ~r1_tarski(C_34, B_32) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.31  tff(c_82, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(B_4, B_4) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_78])).
% 2.06/1.31  tff(c_86, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_82])).
% 2.06/1.31  tff(c_106, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_22, c_86])).
% 2.06/1.31  tff(c_51, plain, (![C_21, A_22, B_23]: (k2_xboole_0(k9_relat_1(C_21, A_22), k9_relat_1(C_21, B_23))=k9_relat_1(C_21, k2_xboole_0(A_22, B_23)) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.06/1.31  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.31  tff(c_57, plain, (![C_21, A_22, B_23]: (r1_tarski(k9_relat_1(C_21, A_22), k9_relat_1(C_21, k2_xboole_0(A_22, B_23))) | ~v1_relat_1(C_21))), inference(superposition, [status(thm), theory('equality')], [c_51, c_14])).
% 2.06/1.31  tff(c_308, plain, (![C_47]: (r1_tarski(k9_relat_1(C_47, '#skF_2'), k9_relat_1(C_47, '#skF_3')) | ~v1_relat_1(C_47))), inference(superposition, [status(thm), theory('equality')], [c_106, c_57])).
% 2.06/1.31  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.31  tff(c_319, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_308, c_20])).
% 2.06/1.31  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_319])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 72
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 1
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 3
% 2.06/1.31  #Demod        : 48
% 2.06/1.31  #Tautology    : 42
% 2.06/1.31  #SimpNegUnit  : 0
% 2.06/1.31  #BackRed      : 0
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.31  Preprocessing        : 0.29
% 2.06/1.31  Parsing              : 0.16
% 2.06/1.31  CNF conversion       : 0.02
% 2.06/1.31  Main loop            : 0.21
% 2.06/1.31  Inferencing          : 0.08
% 2.06/1.31  Reduction            : 0.06
% 2.06/1.31  Demodulation         : 0.05
% 2.06/1.31  BG Simplification    : 0.01
% 2.06/1.31  Subsumption          : 0.05
% 2.06/1.31  Abstraction          : 0.01
% 2.06/1.31  MUC search           : 0.00
% 2.06/1.31  Cooper               : 0.00
% 2.06/1.31  Total                : 0.53
% 2.06/1.31  Index Insertion      : 0.00
% 2.06/1.31  Index Deletion       : 0.00
% 2.06/1.31  Index Matching       : 0.00
% 2.06/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
