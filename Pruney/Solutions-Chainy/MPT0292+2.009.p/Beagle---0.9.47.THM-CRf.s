%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:35 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  41 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_49,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_80,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_3'(A_28,B_29),A_28)
      | r1_tarski(k3_tarski(A_28),B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_152,plain,(
    ! [A_46,B_47] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_46),B_47),A_46)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_46)),B_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_8])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( ~ r1_tarski('#skF_3'(A_10,B_11),B_11)
      | r1_tarski(k3_tarski(A_10),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [A_46] : r1_tarski(k3_tarski(k1_zfmisc_1(A_46)),A_46) ),
    inference(resolution,[status(thm)],[c_152,c_24])).

tff(c_22,plain,(
    ! [A_9] : r1_tarski(k1_tarski(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_8] : k3_tarski(k1_tarski(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k3_tarski(A_24),k3_tarski(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,k3_tarski(B_27))
      | ~ r1_tarski(k1_tarski(A_26),B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_86,plain,(
    ! [A_30] : r1_tarski(A_30,k3_tarski(k1_zfmisc_1(A_30))) ),
    inference(resolution,[status(thm)],[c_22,c_69])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_30] :
      ( k3_tarski(k1_zfmisc_1(A_30)) = A_30
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_30)),A_30) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_169,plain,(
    ! [A_30] : k3_tarski(k1_zfmisc_1(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_94])).

tff(c_30,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.27  
% 1.97/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.28  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.97/1.28  
% 1.97/1.28  %Foreground sorts:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Background operators:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Foreground operators:
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.97/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.97/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.28  
% 1.97/1.28  tff(f_49, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.97/1.28  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.97/1.28  tff(f_42, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.97/1.28  tff(f_40, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.97/1.28  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.97/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.97/1.28  tff(f_56, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.97/1.28  tff(c_80, plain, (![A_28, B_29]: (r2_hidden('#skF_3'(A_28, B_29), A_28) | r1_tarski(k3_tarski(A_28), B_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.28  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.97/1.28  tff(c_152, plain, (![A_46, B_47]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_46), B_47), A_46) | r1_tarski(k3_tarski(k1_zfmisc_1(A_46)), B_47))), inference(resolution, [status(thm)], [c_80, c_8])).
% 1.97/1.28  tff(c_24, plain, (![A_10, B_11]: (~r1_tarski('#skF_3'(A_10, B_11), B_11) | r1_tarski(k3_tarski(A_10), B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.28  tff(c_164, plain, (![A_46]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_46)), A_46))), inference(resolution, [status(thm)], [c_152, c_24])).
% 1.97/1.28  tff(c_22, plain, (![A_9]: (r1_tarski(k1_tarski(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.28  tff(c_20, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.28  tff(c_59, plain, (![A_24, B_25]: (r1_tarski(k3_tarski(A_24), k3_tarski(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.97/1.28  tff(c_69, plain, (![A_26, B_27]: (r1_tarski(A_26, k3_tarski(B_27)) | ~r1_tarski(k1_tarski(A_26), B_27))), inference(superposition, [status(thm), theory('equality')], [c_20, c_59])).
% 1.97/1.28  tff(c_86, plain, (![A_30]: (r1_tarski(A_30, k3_tarski(k1_zfmisc_1(A_30))))), inference(resolution, [status(thm)], [c_22, c_69])).
% 1.97/1.28  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.28  tff(c_94, plain, (![A_30]: (k3_tarski(k1_zfmisc_1(A_30))=A_30 | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_30)), A_30))), inference(resolution, [status(thm)], [c_86, c_2])).
% 1.97/1.28  tff(c_169, plain, (![A_30]: (k3_tarski(k1_zfmisc_1(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_94])).
% 1.97/1.28  tff(c_30, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.28  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_30])).
% 1.97/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.28  
% 1.97/1.28  Inference rules
% 1.97/1.28  ----------------------
% 1.97/1.28  #Ref     : 0
% 1.97/1.28  #Sup     : 29
% 1.97/1.28  #Fact    : 0
% 1.97/1.28  #Define  : 0
% 1.97/1.28  #Split   : 0
% 1.97/1.28  #Chain   : 0
% 1.97/1.28  #Close   : 0
% 1.97/1.28  
% 1.97/1.28  Ordering : KBO
% 1.97/1.28  
% 1.97/1.28  Simplification rules
% 1.97/1.28  ----------------------
% 1.97/1.28  #Subsume      : 0
% 1.97/1.28  #Demod        : 21
% 1.97/1.28  #Tautology    : 12
% 1.97/1.28  #SimpNegUnit  : 0
% 1.97/1.28  #BackRed      : 7
% 1.97/1.28  
% 1.97/1.28  #Partial instantiations: 0
% 1.97/1.28  #Strategies tried      : 1
% 1.97/1.28  
% 1.97/1.28  Timing (in seconds)
% 1.97/1.28  ----------------------
% 1.97/1.29  Preprocessing        : 0.29
% 1.97/1.29  Parsing              : 0.16
% 1.97/1.29  CNF conversion       : 0.02
% 1.97/1.29  Main loop            : 0.17
% 1.97/1.29  Inferencing          : 0.07
% 1.97/1.29  Reduction            : 0.05
% 1.97/1.29  Demodulation         : 0.04
% 1.97/1.29  BG Simplification    : 0.01
% 1.97/1.29  Subsumption          : 0.04
% 1.97/1.29  Abstraction          : 0.01
% 1.97/1.29  MUC search           : 0.00
% 1.97/1.29  Cooper               : 0.00
% 1.97/1.29  Total                : 0.49
% 1.97/1.29  Index Insertion      : 0.00
% 1.97/1.29  Index Deletion       : 0.00
% 1.97/1.29  Index Matching       : 0.00
% 1.97/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
