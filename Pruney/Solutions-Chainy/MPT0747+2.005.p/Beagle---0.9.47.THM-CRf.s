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
% DateTime   : Thu Dec  3 10:06:23 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  67 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > v1_xboole_0 > #nlpp > k3_tarski > k1_ordinal1 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_45,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => v3_ordinal1(B) )
     => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_36,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | v3_ordinal1(k3_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [B_10] :
      ( v3_ordinal1(B_10)
      | ~ r2_hidden(B_10,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,
    ( v3_ordinal1('#skF_1'('#skF_2'))
    | v3_ordinal1(k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_16])).

tff(c_50,plain,(
    v3_ordinal1(k3_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_4,plain,(
    ! [A_3] :
      ( v3_ordinal1(k1_ordinal1(A_3))
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [B_10] :
      ( r2_hidden(B_10,'#skF_2')
      | ~ v3_ordinal1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_51,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,k3_tarski(B_23))
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_4] : r2_hidden(A_4,k1_ordinal1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ! [B_17,A_18] :
      ( ~ r1_tarski(B_17,A_18)
      | ~ r2_hidden(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [A_4] : ~ r1_tarski(k1_ordinal1(A_4),A_4) ),
    inference(resolution,[status(thm)],[c_8,c_29])).

tff(c_62,plain,(
    ! [B_24] : ~ r2_hidden(k1_ordinal1(k3_tarski(B_24)),B_24) ),
    inference(resolution,[status(thm)],[c_51,c_37])).

tff(c_67,plain,(
    ~ v3_ordinal1(k1_ordinal1(k3_tarski('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_70,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_67])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_70])).

tff(c_75,plain,(
    v3_ordinal1('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ v3_ordinal1('#skF_1'(A_5))
      | v3_ordinal1(k3_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_90,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  %$ r2_hidden > r1_tarski > v3_ordinal1 > v1_xboole_0 > #nlpp > k3_tarski > k1_ordinal1 > #skF_1 > #skF_2
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.65/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.65/1.11  
% 1.65/1.12  tff(f_45, axiom, (![A]: ((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_ordinal1)).
% 1.65/1.12  tff(f_57, negated_conjecture, ~(![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_ordinal1)).
% 1.65/1.12  tff(f_36, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_ordinal1)).
% 1.65/1.12  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.65/1.12  tff(f_38, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.65/1.12  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.65/1.12  tff(c_40, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | v3_ordinal1(k3_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.12  tff(c_16, plain, (![B_10]: (v3_ordinal1(B_10) | ~r2_hidden(B_10, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.12  tff(c_49, plain, (v3_ordinal1('#skF_1'('#skF_2')) | v3_ordinal1(k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_16])).
% 1.65/1.12  tff(c_50, plain, (v3_ordinal1(k3_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_49])).
% 1.65/1.12  tff(c_4, plain, (![A_3]: (v3_ordinal1(k1_ordinal1(A_3)) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.12  tff(c_18, plain, (![B_10]: (r2_hidden(B_10, '#skF_2') | ~v3_ordinal1(B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.65/1.12  tff(c_51, plain, (![A_22, B_23]: (r1_tarski(A_22, k3_tarski(B_23)) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.12  tff(c_8, plain, (![A_4]: (r2_hidden(A_4, k1_ordinal1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.12  tff(c_29, plain, (![B_17, A_18]: (~r1_tarski(B_17, A_18) | ~r2_hidden(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.65/1.12  tff(c_37, plain, (![A_4]: (~r1_tarski(k1_ordinal1(A_4), A_4))), inference(resolution, [status(thm)], [c_8, c_29])).
% 1.65/1.12  tff(c_62, plain, (![B_24]: (~r2_hidden(k1_ordinal1(k3_tarski(B_24)), B_24))), inference(resolution, [status(thm)], [c_51, c_37])).
% 1.65/1.12  tff(c_67, plain, (~v3_ordinal1(k1_ordinal1(k3_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_62])).
% 1.65/1.12  tff(c_70, plain, (~v3_ordinal1(k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_67])).
% 1.65/1.12  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_70])).
% 1.65/1.12  tff(c_75, plain, (v3_ordinal1('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_49])).
% 1.65/1.12  tff(c_10, plain, (![A_5]: (~v3_ordinal1('#skF_1'(A_5)) | v3_ordinal1(k3_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.12  tff(c_76, plain, (~v3_ordinal1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_49])).
% 1.65/1.12  tff(c_90, plain, (~v3_ordinal1('#skF_1'('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_76])).
% 1.65/1.12  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_90])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 12
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 1
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 0
% 1.65/1.12  #Demod        : 2
% 1.65/1.12  #Tautology    : 1
% 1.65/1.12  #SimpNegUnit  : 0
% 1.65/1.12  #BackRed      : 0
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.13  Preprocessing        : 0.26
% 1.65/1.13  Parsing              : 0.15
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.11
% 1.65/1.13  Inferencing          : 0.05
% 1.65/1.13  Reduction            : 0.02
% 1.65/1.13  Demodulation         : 0.02
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.01
% 1.65/1.13  Abstraction          : 0.00
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.13  Cooper               : 0.00
% 1.65/1.13  Total                : 0.39
% 1.65/1.13  Index Insertion      : 0.00
% 1.65/1.13  Index Deletion       : 0.00
% 1.65/1.13  Index Matching       : 0.00
% 1.65/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
