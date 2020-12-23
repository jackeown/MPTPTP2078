%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:34 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   38 (  61 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_49,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_3'(A_27,B_28),A_27)
      | r1_tarski(k3_tarski(A_27),B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_141,plain,(
    ! [A_44,B_45,B_46] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_44,B_45),B_46),A_44)
      | r1_tarski(k3_tarski(k3_xboole_0(A_44,B_45)),B_46) ) ),
    inference(resolution,[status(thm)],[c_49,c_6])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,k3_tarski(B_13))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ! [A_29,B_30] :
      ( ~ r1_tarski('#skF_3'(A_29,B_30),B_30)
      | r1_tarski(k3_tarski(A_29),B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [A_29,B_13] :
      ( r1_tarski(k3_tarski(A_29),k3_tarski(B_13))
      | ~ r2_hidden('#skF_3'(A_29,k3_tarski(B_13)),B_13) ) ),
    inference(resolution,[status(thm)],[c_24,c_60])).

tff(c_154,plain,(
    ! [A_44,B_45] : r1_tarski(k3_tarski(k3_xboole_0(A_44,B_45)),k3_tarski(A_44)) ),
    inference(resolution,[status(thm)],[c_141,c_64])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_179,plain,(
    ! [A_52,B_53,B_54] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_52,B_53),B_54),B_53)
      | r1_tarski(k3_tarski(k3_xboole_0(A_52,B_53)),B_54) ) ),
    inference(resolution,[status(thm)],[c_49,c_4])).

tff(c_192,plain,(
    ! [A_52,B_53] : r1_tarski(k3_tarski(k3_xboole_0(A_52,B_53)),k3_tarski(B_53)) ),
    inference(resolution,[status(thm)],[c_179,c_64])).

tff(c_78,plain,(
    ! [A_33,B_34,C_35] :
      ( r1_tarski(A_33,k3_xboole_0(B_34,C_35))
      | ~ r1_tarski(A_33,C_35)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k3_tarski('#skF_4'),k3_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_4','#skF_5')),k3_tarski('#skF_5'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_4','#skF_5')),k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_78,c_30])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_192,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.17  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.84/1.17  
% 1.84/1.17  %Foreground sorts:
% 1.84/1.17  
% 1.84/1.17  
% 1.84/1.17  %Background operators:
% 1.84/1.17  
% 1.84/1.17  
% 1.84/1.17  %Foreground operators:
% 1.84/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.84/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.84/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.17  
% 1.84/1.18  tff(f_53, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.84/1.18  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.84/1.18  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.84/1.18  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.84/1.18  tff(f_56, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 1.84/1.18  tff(c_49, plain, (![A_27, B_28]: (r2_hidden('#skF_3'(A_27, B_28), A_27) | r1_tarski(k3_tarski(A_27), B_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.18  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.18  tff(c_141, plain, (![A_44, B_45, B_46]: (r2_hidden('#skF_3'(k3_xboole_0(A_44, B_45), B_46), A_44) | r1_tarski(k3_tarski(k3_xboole_0(A_44, B_45)), B_46))), inference(resolution, [status(thm)], [c_49, c_6])).
% 1.84/1.18  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, k3_tarski(B_13)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.18  tff(c_60, plain, (![A_29, B_30]: (~r1_tarski('#skF_3'(A_29, B_30), B_30) | r1_tarski(k3_tarski(A_29), B_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.18  tff(c_64, plain, (![A_29, B_13]: (r1_tarski(k3_tarski(A_29), k3_tarski(B_13)) | ~r2_hidden('#skF_3'(A_29, k3_tarski(B_13)), B_13))), inference(resolution, [status(thm)], [c_24, c_60])).
% 1.84/1.18  tff(c_154, plain, (![A_44, B_45]: (r1_tarski(k3_tarski(k3_xboole_0(A_44, B_45)), k3_tarski(A_44)))), inference(resolution, [status(thm)], [c_141, c_64])).
% 1.84/1.18  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.84/1.18  tff(c_179, plain, (![A_52, B_53, B_54]: (r2_hidden('#skF_3'(k3_xboole_0(A_52, B_53), B_54), B_53) | r1_tarski(k3_tarski(k3_xboole_0(A_52, B_53)), B_54))), inference(resolution, [status(thm)], [c_49, c_4])).
% 1.84/1.18  tff(c_192, plain, (![A_52, B_53]: (r1_tarski(k3_tarski(k3_xboole_0(A_52, B_53)), k3_tarski(B_53)))), inference(resolution, [status(thm)], [c_179, c_64])).
% 1.84/1.18  tff(c_78, plain, (![A_33, B_34, C_35]: (r1_tarski(A_33, k3_xboole_0(B_34, C_35)) | ~r1_tarski(A_33, C_35) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.84/1.18  tff(c_30, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k3_tarski('#skF_4'), k3_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.18  tff(c_85, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_4', '#skF_5')), k3_tarski('#skF_5')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_4', '#skF_5')), k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_30])).
% 1.84/1.18  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_192, c_85])).
% 1.84/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  Inference rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Ref     : 0
% 1.84/1.18  #Sup     : 35
% 1.84/1.18  #Fact    : 0
% 1.84/1.18  #Define  : 0
% 1.84/1.18  #Split   : 0
% 1.84/1.18  #Chain   : 0
% 1.84/1.18  #Close   : 0
% 1.84/1.18  
% 1.84/1.18  Ordering : KBO
% 1.84/1.18  
% 1.84/1.18  Simplification rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Subsume      : 0
% 1.84/1.18  #Demod        : 5
% 1.84/1.18  #Tautology    : 11
% 1.84/1.18  #SimpNegUnit  : 0
% 1.84/1.18  #BackRed      : 0
% 1.84/1.18  
% 1.84/1.18  #Partial instantiations: 0
% 1.84/1.18  #Strategies tried      : 1
% 1.84/1.18  
% 1.84/1.18  Timing (in seconds)
% 1.84/1.18  ----------------------
% 1.84/1.19  Preprocessing        : 0.27
% 1.84/1.19  Parsing              : 0.15
% 1.84/1.19  CNF conversion       : 0.02
% 1.84/1.19  Main loop            : 0.16
% 1.84/1.19  Inferencing          : 0.07
% 1.84/1.19  Reduction            : 0.04
% 1.84/1.19  Demodulation         : 0.03
% 1.84/1.19  BG Simplification    : 0.01
% 1.84/1.19  Subsumption          : 0.03
% 1.84/1.19  Abstraction          : 0.01
% 1.84/1.19  MUC search           : 0.00
% 1.84/1.19  Cooper               : 0.00
% 1.84/1.19  Total                : 0.46
% 1.84/1.19  Index Insertion      : 0.00
% 1.84/1.19  Index Deletion       : 0.00
% 1.84/1.19  Index Matching       : 0.00
% 1.84/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
