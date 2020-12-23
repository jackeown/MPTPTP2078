%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:32 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  54 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_16,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k3_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11),A_10)
      | r1_tarski(k3_tarski(A_10),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(k1_tarski(A_28),B_29) = B_29
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_28,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k1_tarski(A_41),C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r2_hidden(A_41,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_2])).

tff(c_168,plain,(
    ! [A_44] :
      ( r1_tarski(k1_tarski(A_44),'#skF_3')
      | ~ r2_hidden(A_44,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_152])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_45] :
      ( r2_hidden(A_45,'#skF_3')
      | ~ r2_hidden(A_45,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_168,c_6])).

tff(c_185,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_1'('#skF_2',B_11),'#skF_3')
      | r1_tarski(k3_tarski('#skF_2'),B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_180])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k3_tarski(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_32,B_33] :
      ( ~ r1_tarski('#skF_1'(A_32,B_33),B_33)
      | r1_tarski(k3_tarski(A_32),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_211,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k3_tarski(A_48),k3_tarski(B_49))
      | ~ r2_hidden('#skF_1'(A_48,k3_tarski(B_49)),B_49) ) ),
    inference(resolution,[status(thm)],[c_10,c_86])).

tff(c_215,plain,(
    r1_tarski(k3_tarski('#skF_2'),k3_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_185,c_211])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_16,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.88/1.17  
% 1.88/1.17  %Foreground sorts:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Background operators:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Foreground operators:
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.17  
% 1.88/1.18  tff(f_53, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.88/1.18  tff(f_48, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.88/1.18  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.88/1.18  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.88/1.18  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.88/1.18  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.88/1.18  tff(c_16, plain, (~r1_tarski(k3_tarski('#skF_2'), k3_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.18  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11), A_10) | r1_tarski(k3_tarski(A_10), B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.18  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.88/1.18  tff(c_28, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.18  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.18  tff(c_73, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)=B_29 | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_28, c_4])).
% 1.88/1.18  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.18  tff(c_152, plain, (![A_41, C_42, B_43]: (r1_tarski(k1_tarski(A_41), C_42) | ~r1_tarski(B_43, C_42) | ~r2_hidden(A_41, B_43))), inference(superposition, [status(thm), theory('equality')], [c_73, c_2])).
% 1.88/1.18  tff(c_168, plain, (![A_44]: (r1_tarski(k1_tarski(A_44), '#skF_3') | ~r2_hidden(A_44, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_152])).
% 1.88/1.18  tff(c_6, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.18  tff(c_180, plain, (![A_45]: (r2_hidden(A_45, '#skF_3') | ~r2_hidden(A_45, '#skF_2'))), inference(resolution, [status(thm)], [c_168, c_6])).
% 1.88/1.18  tff(c_185, plain, (![B_11]: (r2_hidden('#skF_1'('#skF_2', B_11), '#skF_3') | r1_tarski(k3_tarski('#skF_2'), B_11))), inference(resolution, [status(thm)], [c_14, c_180])).
% 1.88/1.18  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k3_tarski(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.18  tff(c_86, plain, (![A_32, B_33]: (~r1_tarski('#skF_1'(A_32, B_33), B_33) | r1_tarski(k3_tarski(A_32), B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.18  tff(c_211, plain, (![A_48, B_49]: (r1_tarski(k3_tarski(A_48), k3_tarski(B_49)) | ~r2_hidden('#skF_1'(A_48, k3_tarski(B_49)), B_49))), inference(resolution, [status(thm)], [c_10, c_86])).
% 1.88/1.18  tff(c_215, plain, (r1_tarski(k3_tarski('#skF_2'), k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_185, c_211])).
% 1.88/1.18  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_16, c_215])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 48
% 1.88/1.18  #Fact    : 0
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 0
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 1
% 1.88/1.18  #Demod        : 0
% 1.88/1.18  #Tautology    : 17
% 1.88/1.18  #SimpNegUnit  : 1
% 1.88/1.18  #BackRed      : 0
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.19  Preprocessing        : 0.27
% 1.88/1.19  Parsing              : 0.15
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.18
% 1.88/1.19  Inferencing          : 0.08
% 1.88/1.19  Reduction            : 0.04
% 1.88/1.19  Demodulation         : 0.02
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.04
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.47
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
