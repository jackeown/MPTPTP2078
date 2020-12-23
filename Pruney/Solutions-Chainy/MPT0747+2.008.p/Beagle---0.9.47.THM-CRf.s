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
% DateTime   : Thu Dec  3 10:06:23 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   31 (  47 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  62 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_1 > #skF_2

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

tff(f_35,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_42,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => v3_ordinal1(B) )
     => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

tff(c_6,plain,(
    ! [A_4] :
      ( v3_ordinal1(k1_ordinal1(A_4))
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [B_10] :
      ( r2_hidden(B_10,'#skF_2')
      | ~ v3_ordinal1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,k3_tarski(B_21))
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3] : r2_hidden(A_3,k1_ordinal1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [B_16,A_17] :
      ( ~ r1_tarski(B_16,A_17)
      | ~ r2_hidden(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [A_3] : ~ r1_tarski(k1_ordinal1(A_3),A_3) ),
    inference(resolution,[status(thm)],[c_4,c_26])).

tff(c_53,plain,(
    ! [B_23] : ~ r2_hidden(k1_ordinal1(k3_tarski(B_23)),B_23) ),
    inference(resolution,[status(thm)],[c_37,c_34])).

tff(c_58,plain,(
    ~ v3_ordinal1(k1_ordinal1(k3_tarski('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_62,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_8,plain,(
    ! [A_5] :
      ( ~ v3_ordinal1('#skF_1'(A_5))
      | v3_ordinal1(k3_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66,plain,(
    ~ v3_ordinal1('#skF_1'('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_68,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | v3_ordinal1(k3_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [B_10] :
      ( v3_ordinal1(B_10)
      | ~ r2_hidden(B_10,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,
    ( v3_ordinal1('#skF_1'('#skF_2'))
    | v3_ordinal1(k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_14])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_66,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:58:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.18  %$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_1 > #skF_2
% 1.81/1.18  
% 1.81/1.18  %Foreground sorts:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Background operators:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Foreground operators:
% 1.81/1.18  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.18  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.18  
% 1.81/1.19  tff(f_35, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 1.81/1.19  tff(f_54, negated_conjecture, ~(![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_ordinal1)).
% 1.81/1.19  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.81/1.19  tff(f_31, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.81/1.19  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.81/1.19  tff(f_42, axiom, (![A]: ((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 1.81/1.19  tff(c_6, plain, (![A_4]: (v3_ordinal1(k1_ordinal1(A_4)) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.19  tff(c_16, plain, (![B_10]: (r2_hidden(B_10, '#skF_2') | ~v3_ordinal1(B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.19  tff(c_37, plain, (![A_20, B_21]: (r1_tarski(A_20, k3_tarski(B_21)) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.19  tff(c_4, plain, (![A_3]: (r2_hidden(A_3, k1_ordinal1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.19  tff(c_26, plain, (![B_16, A_17]: (~r1_tarski(B_16, A_17) | ~r2_hidden(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.19  tff(c_34, plain, (![A_3]: (~r1_tarski(k1_ordinal1(A_3), A_3))), inference(resolution, [status(thm)], [c_4, c_26])).
% 1.81/1.19  tff(c_53, plain, (![B_23]: (~r2_hidden(k1_ordinal1(k3_tarski(B_23)), B_23))), inference(resolution, [status(thm)], [c_37, c_34])).
% 1.81/1.19  tff(c_58, plain, (~v3_ordinal1(k1_ordinal1(k3_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_53])).
% 1.81/1.19  tff(c_62, plain, (~v3_ordinal1(k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_58])).
% 1.81/1.19  tff(c_8, plain, (![A_5]: (~v3_ordinal1('#skF_1'(A_5)) | v3_ordinal1(k3_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.19  tff(c_66, plain, (~v3_ordinal1('#skF_1'('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_62])).
% 1.81/1.19  tff(c_68, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | v3_ordinal1(k3_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.19  tff(c_14, plain, (![B_10]: (v3_ordinal1(B_10) | ~r2_hidden(B_10, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.19  tff(c_75, plain, (v3_ordinal1('#skF_1'('#skF_2')) | v3_ordinal1(k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_14])).
% 1.81/1.19  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_66, c_75])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 11
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 0
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 0
% 1.81/1.19  #Demod        : 0
% 1.81/1.19  #Tautology    : 1
% 1.81/1.19  #SimpNegUnit  : 1
% 1.81/1.19  #BackRed      : 0
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.81/1.19  Preprocessing        : 0.27
% 1.81/1.19  Parsing              : 0.16
% 1.81/1.19  CNF conversion       : 0.02
% 1.81/1.20  Main loop            : 0.10
% 1.81/1.20  Inferencing          : 0.05
% 1.81/1.20  Reduction            : 0.02
% 1.81/1.20  Demodulation         : 0.01
% 1.81/1.20  BG Simplification    : 0.01
% 1.81/1.20  Subsumption          : 0.02
% 1.81/1.20  Abstraction          : 0.00
% 1.81/1.20  MUC search           : 0.00
% 1.81/1.20  Cooper               : 0.00
% 1.81/1.20  Total                : 0.40
% 1.81/1.20  Index Insertion      : 0.00
% 1.81/1.20  Index Deletion       : 0.00
% 1.81/1.20  Index Matching       : 0.00
% 1.81/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
