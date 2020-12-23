%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  49 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k1_tarski(A_12),k2_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    r1_tarski(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [C_32,B_33,A_34] :
      ( r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_35,B_36,B_37] :
      ( r2_hidden('#skF_1'(A_35,B_36),B_37)
      | ~ r1_tarski(A_35,B_37)
      | r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_38,B_39,B_40,B_41] :
      ( r2_hidden('#skF_1'(A_38,B_39),B_40)
      | ~ r1_tarski(B_41,B_40)
      | ~ r1_tarski(A_38,B_41)
      | r1_tarski(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_109,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),k1_tarski('#skF_4'))
      | ~ r1_tarski(A_46,k2_tarski('#skF_2','#skF_3'))
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_20,c_87])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_51] :
      ( ~ r1_tarski(A_51,k2_tarski('#skF_2','#skF_3'))
      | r1_tarski(A_51,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_141,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(k1_tarski(A_14),k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_146,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_141,c_16])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n022.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:27:40 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.81/1.16  
% 1.81/1.16  %Foreground sorts:
% 1.81/1.16  
% 1.81/1.16  
% 1.81/1.16  %Background operators:
% 1.81/1.16  
% 1.81/1.16  
% 1.81/1.16  %Foreground operators:
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.81/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.16  
% 1.81/1.17  tff(f_49, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.81/1.17  tff(f_40, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.81/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.81/1.17  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.81/1.17  tff(c_18, plain, ('#skF_2'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.17  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k1_tarski(A_12), k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.17  tff(c_20, plain, (r1_tarski(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.17  tff(c_74, plain, (![C_32, B_33, A_34]: (r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.17  tff(c_78, plain, (![A_35, B_36, B_37]: (r2_hidden('#skF_1'(A_35, B_36), B_37) | ~r1_tarski(A_35, B_37) | r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_6, c_74])).
% 1.81/1.17  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.17  tff(c_87, plain, (![A_38, B_39, B_40, B_41]: (r2_hidden('#skF_1'(A_38, B_39), B_40) | ~r1_tarski(B_41, B_40) | ~r1_tarski(A_38, B_41) | r1_tarski(A_38, B_39))), inference(resolution, [status(thm)], [c_78, c_2])).
% 1.81/1.17  tff(c_109, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), k1_tarski('#skF_4')) | ~r1_tarski(A_46, k2_tarski('#skF_2', '#skF_3')) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_20, c_87])).
% 1.81/1.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.17  tff(c_125, plain, (![A_51]: (~r1_tarski(A_51, k2_tarski('#skF_2', '#skF_3')) | r1_tarski(A_51, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_109, c_4])).
% 1.81/1.17  tff(c_141, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_125])).
% 1.81/1.17  tff(c_16, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(k1_tarski(A_14), k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.17  tff(c_146, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_141, c_16])).
% 1.81/1.17  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_146])).
% 1.81/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  Inference rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Ref     : 0
% 1.81/1.17  #Sup     : 28
% 1.81/1.17  #Fact    : 0
% 1.81/1.17  #Define  : 0
% 1.81/1.17  #Split   : 0
% 1.81/1.17  #Chain   : 0
% 1.81/1.17  #Close   : 0
% 1.81/1.17  
% 1.81/1.17  Ordering : KBO
% 1.81/1.17  
% 1.81/1.17  Simplification rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Subsume      : 2
% 1.81/1.17  #Demod        : 2
% 1.81/1.17  #Tautology    : 12
% 1.81/1.17  #SimpNegUnit  : 1
% 1.81/1.17  #BackRed      : 0
% 1.81/1.17  
% 1.81/1.17  #Partial instantiations: 0
% 1.81/1.17  #Strategies tried      : 1
% 1.81/1.17  
% 1.81/1.17  Timing (in seconds)
% 1.81/1.17  ----------------------
% 1.90/1.17  Preprocessing        : 0.29
% 1.90/1.17  Parsing              : 0.15
% 1.90/1.17  CNF conversion       : 0.02
% 1.90/1.17  Main loop            : 0.15
% 1.90/1.17  Inferencing          : 0.06
% 1.90/1.17  Reduction            : 0.04
% 1.90/1.17  Demodulation         : 0.03
% 1.90/1.17  BG Simplification    : 0.01
% 1.90/1.17  Subsumption          : 0.03
% 1.90/1.17  Abstraction          : 0.01
% 1.90/1.17  MUC search           : 0.00
% 1.90/1.17  Cooper               : 0.00
% 1.90/1.17  Total                : 0.46
% 1.90/1.17  Index Insertion      : 0.00
% 1.90/1.17  Index Deletion       : 0.00
% 1.90/1.17  Index Matching       : 0.00
% 1.90/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
