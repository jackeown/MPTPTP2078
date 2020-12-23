%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:25 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  50 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_8,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,k3_tarski(B_18))
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [A_43,A_44,B_45] :
      ( r1_tarski(A_43,k2_xboole_0(A_44,B_45))
      | ~ r2_hidden(A_43,k2_tarski(A_44,B_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_28])).

tff(c_88,plain,(
    ! [D_11,A_6] : r1_tarski(D_11,k2_xboole_0(A_6,D_11)) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_zfmisc_1(A_21),k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(k2_xboole_0(A_48,C_49),B_50)
      | ~ r1_tarski(C_49,B_50)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'),k1_zfmisc_1('#skF_4')),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_92,c_34])).

tff(c_97,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_100,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_105,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_110,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_105])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.22  
% 1.75/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.23  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.75/1.23  
% 1.75/1.23  %Foreground sorts:
% 1.75/1.23  
% 1.75/1.23  
% 1.75/1.23  %Background operators:
% 1.75/1.23  
% 1.75/1.23  
% 1.75/1.23  %Foreground operators:
% 1.75/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.75/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.75/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.75/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.23  
% 1.92/1.24  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.24  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.92/1.24  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.92/1.24  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.92/1.24  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.92/1.24  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.92/1.24  tff(f_59, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 1.92/1.24  tff(c_8, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.24  tff(c_48, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.24  tff(c_28, plain, (![A_17, B_18]: (r1_tarski(A_17, k3_tarski(B_18)) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.24  tff(c_81, plain, (![A_43, A_44, B_45]: (r1_tarski(A_43, k2_xboole_0(A_44, B_45)) | ~r2_hidden(A_43, k2_tarski(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_28])).
% 1.92/1.24  tff(c_88, plain, (![D_11, A_6]: (r1_tarski(D_11, k2_xboole_0(A_6, D_11)))), inference(resolution, [status(thm)], [c_8, c_81])).
% 1.92/1.24  tff(c_32, plain, (![A_21, B_22]: (r1_tarski(k1_zfmisc_1(A_21), k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.24  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.24  tff(c_92, plain, (![A_48, C_49, B_50]: (r1_tarski(k2_xboole_0(A_48, C_49), B_50) | ~r1_tarski(C_49, B_50) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.24  tff(c_34, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'), k1_zfmisc_1('#skF_4')), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.24  tff(c_96, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4'))) | ~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_92, c_34])).
% 1.92/1.24  tff(c_97, plain, (~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_96])).
% 1.92/1.24  tff(c_100, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_97])).
% 1.92/1.24  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_100])).
% 1.92/1.24  tff(c_105, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_96])).
% 1.92/1.24  tff(c_110, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_105])).
% 1.92/1.24  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_110])).
% 1.92/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.24  
% 1.92/1.24  Inference rules
% 1.92/1.24  ----------------------
% 1.92/1.24  #Ref     : 0
% 1.92/1.24  #Sup     : 14
% 1.92/1.24  #Fact    : 0
% 1.92/1.24  #Define  : 0
% 1.92/1.24  #Split   : 1
% 1.92/1.24  #Chain   : 0
% 1.92/1.24  #Close   : 0
% 1.92/1.24  
% 1.92/1.24  Ordering : KBO
% 1.92/1.24  
% 1.92/1.24  Simplification rules
% 1.92/1.24  ----------------------
% 1.92/1.24  #Subsume      : 0
% 1.92/1.24  #Demod        : 3
% 1.92/1.24  #Tautology    : 9
% 1.92/1.24  #SimpNegUnit  : 0
% 1.92/1.24  #BackRed      : 0
% 1.92/1.24  
% 1.92/1.24  #Partial instantiations: 0
% 1.92/1.24  #Strategies tried      : 1
% 1.92/1.24  
% 1.92/1.24  Timing (in seconds)
% 1.92/1.24  ----------------------
% 1.92/1.24  Preprocessing        : 0.31
% 1.92/1.24  Parsing              : 0.16
% 1.92/1.24  CNF conversion       : 0.02
% 1.92/1.24  Main loop            : 0.12
% 1.92/1.24  Inferencing          : 0.04
% 1.92/1.24  Reduction            : 0.04
% 1.92/1.24  Demodulation         : 0.03
% 1.92/1.24  BG Simplification    : 0.01
% 1.92/1.24  Subsumption          : 0.02
% 1.92/1.24  Abstraction          : 0.01
% 1.92/1.24  MUC search           : 0.00
% 1.92/1.24  Cooper               : 0.00
% 1.92/1.24  Total                : 0.45
% 1.92/1.24  Index Insertion      : 0.00
% 1.92/1.24  Index Deletion       : 0.00
% 1.92/1.24  Index Matching       : 0.00
% 1.92/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
