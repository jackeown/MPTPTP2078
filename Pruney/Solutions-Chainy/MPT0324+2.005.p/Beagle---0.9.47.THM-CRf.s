%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:20 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( r2_hidden(A,k2_zfmisc_1(B,C))
          & r2_hidden(A,k2_zfmisc_1(D,E)) )
       => r2_hidden(A,k2_zfmisc_1(k3_xboole_0(B,D),k3_xboole_0(C,E))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_26,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_20,C_21,B_22,D_23] : k3_xboole_0(k2_zfmisc_1(A_20,C_21),k2_zfmisc_1(B_22,D_23)) = k2_zfmisc_1(k3_xboole_0(A_20,B_22),k3_xboole_0(C_21,D_23)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_955,plain,(
    ! [D_104,B_103,A_105,C_101,D_102] :
      ( r2_hidden(D_102,k2_zfmisc_1(k3_xboole_0(A_105,B_103),k3_xboole_0(C_101,D_104)))
      | ~ r2_hidden(D_102,k2_zfmisc_1(B_103,D_104))
      | ~ r2_hidden(D_102,k2_zfmisc_1(A_105,C_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_22,plain,(
    ~ r2_hidden('#skF_3',k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_989,plain,
    ( ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_6','#skF_7'))
    | ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_955,c_22])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  %$ r2_hidden > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.07/1.52  
% 3.07/1.52  %Foreground sorts:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Background operators:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Foreground operators:
% 3.07/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.07/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.07/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.52  
% 3.07/1.52  tff(f_43, negated_conjecture, ~(![A, B, C, D, E]: ((r2_hidden(A, k2_zfmisc_1(B, C)) & r2_hidden(A, k2_zfmisc_1(D, E))) => r2_hidden(A, k2_zfmisc_1(k3_xboole_0(B, D), k3_xboole_0(C, E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_zfmisc_1)).
% 3.07/1.52  tff(f_36, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 3.07/1.52  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.07/1.52  tff(c_26, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.52  tff(c_24, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.52  tff(c_38, plain, (![A_20, C_21, B_22, D_23]: (k3_xboole_0(k2_zfmisc_1(A_20, C_21), k2_zfmisc_1(B_22, D_23))=k2_zfmisc_1(k3_xboole_0(A_20, B_22), k3_xboole_0(C_21, D_23)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.52  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.07/1.52  tff(c_955, plain, (![D_104, B_103, A_105, C_101, D_102]: (r2_hidden(D_102, k2_zfmisc_1(k3_xboole_0(A_105, B_103), k3_xboole_0(C_101, D_104))) | ~r2_hidden(D_102, k2_zfmisc_1(B_103, D_104)) | ~r2_hidden(D_102, k2_zfmisc_1(A_105, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2])).
% 3.07/1.52  tff(c_22, plain, (~r2_hidden('#skF_3', k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.52  tff(c_989, plain, (~r2_hidden('#skF_3', k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_955, c_22])).
% 3.07/1.52  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_989])).
% 3.07/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  Inference rules
% 3.07/1.52  ----------------------
% 3.07/1.52  #Ref     : 0
% 3.07/1.52  #Sup     : 212
% 3.07/1.52  #Fact    : 0
% 3.07/1.52  #Define  : 0
% 3.07/1.52  #Split   : 0
% 3.07/1.52  #Chain   : 0
% 3.07/1.52  #Close   : 0
% 3.07/1.52  
% 3.07/1.52  Ordering : KBO
% 3.07/1.53  
% 3.07/1.53  Simplification rules
% 3.07/1.53  ----------------------
% 3.07/1.53  #Subsume      : 13
% 3.07/1.53  #Demod        : 60
% 3.07/1.53  #Tautology    : 24
% 3.07/1.53  #SimpNegUnit  : 0
% 3.07/1.53  #BackRed      : 0
% 3.07/1.53  
% 3.07/1.53  #Partial instantiations: 0
% 3.07/1.53  #Strategies tried      : 1
% 3.07/1.53  
% 3.07/1.53  Timing (in seconds)
% 3.07/1.53  ----------------------
% 3.07/1.53  Preprocessing        : 0.27
% 3.07/1.53  Parsing              : 0.14
% 3.07/1.53  CNF conversion       : 0.02
% 3.07/1.53  Main loop            : 0.43
% 3.07/1.53  Inferencing          : 0.17
% 3.07/1.53  Reduction            : 0.10
% 3.07/1.53  Demodulation         : 0.08
% 3.07/1.53  BG Simplification    : 0.03
% 3.07/1.53  Subsumption          : 0.10
% 3.07/1.53  Abstraction          : 0.04
% 3.07/1.53  MUC search           : 0.00
% 3.07/1.53  Cooper               : 0.00
% 3.07/1.53  Total                : 0.73
% 3.07/1.53  Index Insertion      : 0.00
% 3.07/1.53  Index Deletion       : 0.00
% 3.07/1.53  Index Matching       : 0.00
% 3.07/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
