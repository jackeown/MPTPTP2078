%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:35 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  52 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : r1_relat_2(k1_wellord2(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord2)).

tff(c_32,plain,(
    ! [A_21] : v1_relat_1(k1_wellord2(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_3,B_9] :
      ( r2_hidden('#skF_1'(A_3,B_9),B_9)
      | r1_relat_2(A_3,B_9)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [C_19,D_20,A_13] :
      ( r2_hidden(k4_tarski(C_19,D_20),k1_wellord2(A_13))
      | ~ r1_tarski(C_19,D_20)
      | ~ r2_hidden(D_20,A_13)
      | ~ r2_hidden(C_19,A_13)
      | ~ v1_relat_1(k1_wellord2(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,(
    ! [C_36,D_37,A_38] :
      ( r2_hidden(k4_tarski(C_36,D_37),k1_wellord2(A_38))
      | ~ r1_tarski(C_36,D_37)
      | ~ r2_hidden(D_37,A_38)
      | ~ r2_hidden(C_36,A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_10,plain,(
    ! [A_3,B_9] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3,B_9),'#skF_1'(A_3,B_9)),A_3)
      | r1_relat_2(A_3,B_9)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_38,B_9] :
      ( r1_relat_2(k1_wellord2(A_38),B_9)
      | ~ v1_relat_1(k1_wellord2(A_38))
      | ~ r1_tarski('#skF_1'(k1_wellord2(A_38),B_9),'#skF_1'(k1_wellord2(A_38),B_9))
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_38),B_9),A_38) ) ),
    inference(resolution,[status(thm)],[c_94,c_10])).

tff(c_105,plain,(
    ! [A_39,B_40] :
      ( r1_relat_2(k1_wellord2(A_39),B_40)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_39),B_40),A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32,c_98])).

tff(c_109,plain,(
    ! [B_9] :
      ( r1_relat_2(k1_wellord2(B_9),B_9)
      | ~ v1_relat_1(k1_wellord2(B_9)) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_112,plain,(
    ! [B_9] : r1_relat_2(k1_wellord2(B_9),B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_109])).

tff(c_34,plain,(
    ~ r1_relat_2(k1_wellord2('#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.27  %$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.91/1.27  
% 1.91/1.27  %Foreground sorts:
% 1.91/1.27  
% 1.91/1.27  
% 1.91/1.27  %Background operators:
% 1.91/1.27  
% 1.91/1.27  
% 1.91/1.27  %Foreground operators:
% 1.91/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.27  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.91/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.27  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 1.91/1.27  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.91/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.27  
% 1.91/1.28  tff(f_58, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.91/1.28  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 1.91/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.91/1.28  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 1.91/1.28  tff(f_61, negated_conjecture, ~(![A]: r1_relat_2(k1_wellord2(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord2)).
% 1.91/1.28  tff(c_32, plain, (![A_21]: (v1_relat_1(k1_wellord2(A_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.91/1.28  tff(c_12, plain, (![A_3, B_9]: (r2_hidden('#skF_1'(A_3, B_9), B_9) | r1_relat_2(A_3, B_9) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.28  tff(c_28, plain, (![C_19, D_20, A_13]: (r2_hidden(k4_tarski(C_19, D_20), k1_wellord2(A_13)) | ~r1_tarski(C_19, D_20) | ~r2_hidden(D_20, A_13) | ~r2_hidden(C_19, A_13) | ~v1_relat_1(k1_wellord2(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.91/1.28  tff(c_94, plain, (![C_36, D_37, A_38]: (r2_hidden(k4_tarski(C_36, D_37), k1_wellord2(A_38)) | ~r1_tarski(C_36, D_37) | ~r2_hidden(D_37, A_38) | ~r2_hidden(C_36, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 1.91/1.28  tff(c_10, plain, (![A_3, B_9]: (~r2_hidden(k4_tarski('#skF_1'(A_3, B_9), '#skF_1'(A_3, B_9)), A_3) | r1_relat_2(A_3, B_9) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.28  tff(c_98, plain, (![A_38, B_9]: (r1_relat_2(k1_wellord2(A_38), B_9) | ~v1_relat_1(k1_wellord2(A_38)) | ~r1_tarski('#skF_1'(k1_wellord2(A_38), B_9), '#skF_1'(k1_wellord2(A_38), B_9)) | ~r2_hidden('#skF_1'(k1_wellord2(A_38), B_9), A_38))), inference(resolution, [status(thm)], [c_94, c_10])).
% 1.91/1.28  tff(c_105, plain, (![A_39, B_40]: (r1_relat_2(k1_wellord2(A_39), B_40) | ~r2_hidden('#skF_1'(k1_wellord2(A_39), B_40), A_39))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32, c_98])).
% 1.91/1.28  tff(c_109, plain, (![B_9]: (r1_relat_2(k1_wellord2(B_9), B_9) | ~v1_relat_1(k1_wellord2(B_9)))), inference(resolution, [status(thm)], [c_12, c_105])).
% 1.91/1.28  tff(c_112, plain, (![B_9]: (r1_relat_2(k1_wellord2(B_9), B_9))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_109])).
% 1.91/1.28  tff(c_34, plain, (~r1_relat_2(k1_wellord2('#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.28  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_34])).
% 1.91/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.28  
% 1.91/1.28  Inference rules
% 1.91/1.28  ----------------------
% 1.91/1.28  #Ref     : 0
% 1.91/1.28  #Sup     : 13
% 1.91/1.28  #Fact    : 0
% 1.91/1.28  #Define  : 0
% 1.91/1.28  #Split   : 0
% 1.91/1.28  #Chain   : 0
% 1.91/1.28  #Close   : 0
% 1.91/1.28  
% 1.91/1.28  Ordering : KBO
% 1.91/1.28  
% 1.91/1.28  Simplification rules
% 1.91/1.28  ----------------------
% 1.91/1.28  #Subsume      : 0
% 1.91/1.28  #Demod        : 21
% 1.91/1.28  #Tautology    : 10
% 1.91/1.28  #SimpNegUnit  : 0
% 1.91/1.28  #BackRed      : 1
% 1.91/1.28  
% 1.91/1.28  #Partial instantiations: 0
% 1.91/1.28  #Strategies tried      : 1
% 1.91/1.28  
% 1.91/1.28  Timing (in seconds)
% 1.91/1.28  ----------------------
% 1.91/1.28  Preprocessing        : 0.32
% 1.91/1.28  Parsing              : 0.16
% 1.91/1.28  CNF conversion       : 0.02
% 1.91/1.28  Main loop            : 0.11
% 1.91/1.28  Inferencing          : 0.04
% 1.91/1.28  Reduction            : 0.04
% 1.91/1.28  Demodulation         : 0.03
% 1.91/1.28  BG Simplification    : 0.02
% 1.91/1.28  Subsumption          : 0.02
% 1.91/1.28  Abstraction          : 0.01
% 1.91/1.29  MUC search           : 0.00
% 1.91/1.29  Cooper               : 0.00
% 1.91/1.29  Total                : 0.46
% 1.91/1.29  Index Insertion      : 0.00
% 1.91/1.29  Index Deletion       : 0.00
% 1.91/1.29  Index Matching       : 0.00
% 1.91/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
