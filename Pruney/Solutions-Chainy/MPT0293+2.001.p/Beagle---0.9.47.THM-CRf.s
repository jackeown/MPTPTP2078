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
% DateTime   : Thu Dec  3 09:53:36 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,k3_tarski(B_13))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_zfmisc_1(A_14),k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_16] : r1_tarski(k1_tarski(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_37,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | ~ r1_tarski(k1_tarski(A_25),B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [A_16] : r2_hidden(A_16,k1_zfmisc_1(A_16)) ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_98,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | ~ r1_tarski(k1_zfmisc_1(A_46),B_47) ) ),
    inference(resolution,[status(thm)],[c_50,c_98])).

tff(c_151,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,k1_zfmisc_1(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_733,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(A_95,k1_zfmisc_1(B_96))
      | ~ r1_tarski('#skF_1'(A_95,k1_zfmisc_1(B_96)),B_96) ) ),
    inference(resolution,[status(thm)],[c_151,c_4])).

tff(c_6007,plain,(
    ! [A_342,B_343] :
      ( r1_tarski(A_342,k1_zfmisc_1(k3_tarski(B_343)))
      | ~ r2_hidden('#skF_1'(A_342,k1_zfmisc_1(k3_tarski(B_343))),B_343) ) ),
    inference(resolution,[status(thm)],[c_24,c_733])).

tff(c_6102,plain,(
    ! [A_1] : r1_tarski(A_1,k1_zfmisc_1(k3_tarski(A_1))) ),
    inference(resolution,[status(thm)],[c_6,c_6007])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_2',k1_zfmisc_1(k3_tarski('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6102,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.20/2.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/2.53  
% 7.20/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/2.53  %$ r3_xboole_0 > r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 7.20/2.53  
% 7.20/2.53  %Foreground sorts:
% 7.20/2.53  
% 7.20/2.53  
% 7.20/2.53  %Background operators:
% 7.20/2.53  
% 7.20/2.53  
% 7.20/2.53  %Foreground operators:
% 7.20/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.20/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.20/2.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.20/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.20/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.20/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.20/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.20/2.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.20/2.53  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 7.20/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.20/2.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.20/2.53  
% 7.20/2.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.20/2.54  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 7.20/2.54  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 7.20/2.54  tff(f_58, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 7.20/2.54  tff(f_48, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.20/2.54  tff(f_61, negated_conjecture, ~(![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 7.20/2.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.20/2.54  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, k3_tarski(B_13)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.20/2.54  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.20/2.54  tff(c_28, plain, (![A_16]: (r1_tarski(k1_tarski(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.20/2.54  tff(c_37, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | ~r1_tarski(k1_tarski(A_25), B_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.20/2.54  tff(c_50, plain, (![A_16]: (r2_hidden(A_16, k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_28, c_37])).
% 7.20/2.54  tff(c_98, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.20/2.54  tff(c_126, plain, (![A_46, B_47]: (r2_hidden(A_46, B_47) | ~r1_tarski(k1_zfmisc_1(A_46), B_47))), inference(resolution, [status(thm)], [c_50, c_98])).
% 7.20/2.54  tff(c_151, plain, (![A_50, B_51]: (r2_hidden(A_50, k1_zfmisc_1(B_51)) | ~r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_26, c_126])).
% 7.20/2.54  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.20/2.54  tff(c_733, plain, (![A_95, B_96]: (r1_tarski(A_95, k1_zfmisc_1(B_96)) | ~r1_tarski('#skF_1'(A_95, k1_zfmisc_1(B_96)), B_96))), inference(resolution, [status(thm)], [c_151, c_4])).
% 7.20/2.54  tff(c_6007, plain, (![A_342, B_343]: (r1_tarski(A_342, k1_zfmisc_1(k3_tarski(B_343))) | ~r2_hidden('#skF_1'(A_342, k1_zfmisc_1(k3_tarski(B_343))), B_343))), inference(resolution, [status(thm)], [c_24, c_733])).
% 7.20/2.54  tff(c_6102, plain, (![A_1]: (r1_tarski(A_1, k1_zfmisc_1(k3_tarski(A_1))))), inference(resolution, [status(thm)], [c_6, c_6007])).
% 7.20/2.54  tff(c_30, plain, (~r1_tarski('#skF_2', k1_zfmisc_1(k3_tarski('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.20/2.54  tff(c_6105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6102, c_30])).
% 7.20/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/2.54  
% 7.20/2.54  Inference rules
% 7.20/2.54  ----------------------
% 7.20/2.54  #Ref     : 0
% 7.20/2.54  #Sup     : 1256
% 7.20/2.54  #Fact    : 0
% 7.20/2.54  #Define  : 0
% 7.20/2.54  #Split   : 0
% 7.20/2.54  #Chain   : 0
% 7.20/2.54  #Close   : 0
% 7.20/2.54  
% 7.20/2.54  Ordering : KBO
% 7.20/2.54  
% 7.20/2.54  Simplification rules
% 7.20/2.54  ----------------------
% 7.20/2.54  #Subsume      : 17
% 7.20/2.54  #Demod        : 48
% 7.20/2.54  #Tautology    : 54
% 7.20/2.54  #SimpNegUnit  : 0
% 7.20/2.54  #BackRed      : 1
% 7.20/2.54  
% 7.20/2.54  #Partial instantiations: 0
% 7.20/2.54  #Strategies tried      : 1
% 7.20/2.54  
% 7.20/2.54  Timing (in seconds)
% 7.20/2.54  ----------------------
% 7.20/2.54  Preprocessing        : 0.29
% 7.20/2.54  Parsing              : 0.16
% 7.20/2.54  CNF conversion       : 0.02
% 7.20/2.54  Main loop            : 1.45
% 7.20/2.54  Inferencing          : 0.42
% 7.20/2.54  Reduction            : 0.42
% 7.20/2.54  Demodulation         : 0.32
% 7.20/2.54  BG Simplification    : 0.05
% 7.20/2.54  Subsumption          : 0.44
% 7.20/2.54  Abstraction          : 0.06
% 7.20/2.54  MUC search           : 0.00
% 7.20/2.54  Cooper               : 0.00
% 7.20/2.54  Total                : 1.77
% 7.20/2.54  Index Insertion      : 0.00
% 7.20/2.54  Index Deletion       : 0.00
% 7.20/2.54  Index Matching       : 0.00
% 7.20/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
