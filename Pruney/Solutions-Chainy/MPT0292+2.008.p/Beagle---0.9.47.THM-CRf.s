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
% DateTime   : Thu Dec  3 09:53:35 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  48 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_3'(A_24,B_25),A_24)
      | r1_tarski(k3_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [A_30,B_31] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_30),B_31),A_30)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_30)),B_31) ) ),
    inference(resolution,[status(thm)],[c_51,c_8])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( ~ r1_tarski('#skF_3'(A_10,B_11),B_11)
      | r1_tarski(k3_tarski(A_10),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [A_32] : r1_tarski(k3_tarski(k1_zfmisc_1(A_32)),A_32) ),
    inference(resolution,[status(thm)],[c_74,c_22])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k3_tarski(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [B_20,A_21] :
      ( B_20 = A_21
      | ~ r1_tarski(B_20,A_21)
      | ~ r1_tarski(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [B_9,A_8] :
      ( k3_tarski(B_9) = A_8
      | ~ r1_tarski(k3_tarski(B_9),A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_97,plain,(
    ! [A_33] :
      ( k3_tarski(k1_zfmisc_1(A_33)) = A_33
      | ~ r2_hidden(A_33,k1_zfmisc_1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_89,c_41])).

tff(c_101,plain,(
    ! [A_3] :
      ( k3_tarski(k1_zfmisc_1(A_3)) = A_3
      | ~ r1_tarski(A_3,A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_97])).

tff(c_104,plain,(
    ! [A_3] : k3_tarski(k1_zfmisc_1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_101])).

tff(c_26,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.21  
% 1.75/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.21  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.83/1.21  
% 1.83/1.21  %Foreground sorts:
% 1.83/1.21  
% 1.83/1.21  
% 1.83/1.21  %Background operators:
% 1.83/1.21  
% 1.83/1.21  
% 1.83/1.21  %Foreground operators:
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.83/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.83/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.21  
% 1.83/1.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.83/1.23  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.83/1.23  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.83/1.23  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.83/1.23  tff(f_52, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.83/1.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.23  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.83/1.23  tff(c_51, plain, (![A_24, B_25]: (r2_hidden('#skF_3'(A_24, B_25), A_24) | r1_tarski(k3_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.23  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.83/1.23  tff(c_74, plain, (![A_30, B_31]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_30), B_31), A_30) | r1_tarski(k3_tarski(k1_zfmisc_1(A_30)), B_31))), inference(resolution, [status(thm)], [c_51, c_8])).
% 1.83/1.23  tff(c_22, plain, (![A_10, B_11]: (~r1_tarski('#skF_3'(A_10, B_11), B_11) | r1_tarski(k3_tarski(A_10), B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.23  tff(c_89, plain, (![A_32]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_32)), A_32))), inference(resolution, [status(thm)], [c_74, c_22])).
% 1.83/1.23  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, k3_tarski(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.83/1.23  tff(c_36, plain, (![B_20, A_21]: (B_20=A_21 | ~r1_tarski(B_20, A_21) | ~r1_tarski(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.23  tff(c_41, plain, (![B_9, A_8]: (k3_tarski(B_9)=A_8 | ~r1_tarski(k3_tarski(B_9), A_8) | ~r2_hidden(A_8, B_9))), inference(resolution, [status(thm)], [c_20, c_36])).
% 1.83/1.23  tff(c_97, plain, (![A_33]: (k3_tarski(k1_zfmisc_1(A_33))=A_33 | ~r2_hidden(A_33, k1_zfmisc_1(A_33)))), inference(resolution, [status(thm)], [c_89, c_41])).
% 1.83/1.23  tff(c_101, plain, (![A_3]: (k3_tarski(k1_zfmisc_1(A_3))=A_3 | ~r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_10, c_97])).
% 1.83/1.23  tff(c_104, plain, (![A_3]: (k3_tarski(k1_zfmisc_1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_101])).
% 1.83/1.23  tff(c_26, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.83/1.23  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_26])).
% 1.83/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.23  
% 1.83/1.23  Inference rules
% 1.83/1.23  ----------------------
% 1.83/1.23  #Ref     : 0
% 1.83/1.23  #Sup     : 15
% 1.83/1.23  #Fact    : 0
% 1.83/1.23  #Define  : 0
% 1.83/1.23  #Split   : 0
% 1.83/1.23  #Chain   : 0
% 1.83/1.23  #Close   : 0
% 1.83/1.23  
% 1.83/1.23  Ordering : KBO
% 1.83/1.23  
% 1.83/1.23  Simplification rules
% 1.83/1.23  ----------------------
% 1.83/1.23  #Subsume      : 0
% 1.83/1.23  #Demod        : 8
% 1.83/1.23  #Tautology    : 6
% 1.83/1.23  #SimpNegUnit  : 0
% 1.83/1.23  #BackRed      : 3
% 1.83/1.23  
% 1.83/1.23  #Partial instantiations: 0
% 1.83/1.23  #Strategies tried      : 1
% 1.83/1.23  
% 1.83/1.23  Timing (in seconds)
% 1.83/1.23  ----------------------
% 1.83/1.24  Preprocessing        : 0.25
% 1.83/1.24  Parsing              : 0.13
% 1.83/1.24  CNF conversion       : 0.02
% 1.87/1.24  Main loop            : 0.15
% 1.87/1.24  Inferencing          : 0.06
% 1.87/1.24  Reduction            : 0.03
% 1.87/1.24  Demodulation         : 0.03
% 1.87/1.24  BG Simplification    : 0.01
% 1.87/1.24  Subsumption          : 0.03
% 1.87/1.24  Abstraction          : 0.01
% 1.87/1.24  MUC search           : 0.00
% 1.87/1.24  Cooper               : 0.00
% 1.87/1.24  Total                : 0.44
% 1.87/1.24  Index Insertion      : 0.00
% 1.87/1.24  Index Deletion       : 0.00
% 1.87/1.24  Index Matching       : 0.00
% 1.87/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
