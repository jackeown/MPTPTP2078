%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:56 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  51 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ! [B_16,A_17] :
      ( r1_xboole_0(k1_relat_1(B_16),A_17)
      | k9_relat_1(B_16,A_17) != k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_20,A_21,B_22] :
      ( r1_xboole_0(A_20,A_21)
      | ~ r1_tarski(A_20,k1_relat_1(B_22))
      | k9_relat_1(B_22,A_21) != k1_xboole_0
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_71,plain,(
    ! [A_21] :
      ( r1_xboole_0('#skF_1',A_21)
      | k9_relat_1('#skF_2',A_21) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_75,plain,(
    ! [A_23] :
      ( r1_xboole_0('#skF_1',A_23)
      | k9_relat_1('#skF_2',A_23) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_71])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ r1_xboole_0(A_4,A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,
    ( k1_xboole_0 = '#skF_1'
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_75,c_6])).

tff(c_85,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_81])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:55:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.10  
% 1.68/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.10  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.10  
% 1.68/1.10  %Foreground sorts:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Background operators:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Foreground operators:
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.68/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.10  
% 1.68/1.11  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 1.68/1.11  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.68/1.11  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.68/1.11  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.68/1.11  tff(c_16, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.68/1.11  tff(c_12, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.68/1.11  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.68/1.11  tff(c_14, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.68/1.11  tff(c_54, plain, (![B_16, A_17]: (r1_xboole_0(k1_relat_1(B_16), A_17) | k9_relat_1(B_16, A_17)!=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.11  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.11  tff(c_69, plain, (![A_20, A_21, B_22]: (r1_xboole_0(A_20, A_21) | ~r1_tarski(A_20, k1_relat_1(B_22)) | k9_relat_1(B_22, A_21)!=k1_xboole_0 | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_54, c_2])).
% 1.68/1.11  tff(c_71, plain, (![A_21]: (r1_xboole_0('#skF_1', A_21) | k9_relat_1('#skF_2', A_21)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_69])).
% 1.68/1.11  tff(c_75, plain, (![A_23]: (r1_xboole_0('#skF_1', A_23) | k9_relat_1('#skF_2', A_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_71])).
% 1.68/1.11  tff(c_6, plain, (![A_4]: (~r1_xboole_0(A_4, A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.68/1.11  tff(c_81, plain, (k1_xboole_0='#skF_1' | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_75, c_6])).
% 1.68/1.11  tff(c_85, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_81])).
% 1.68/1.11  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_85])).
% 1.68/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  Inference rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Ref     : 0
% 1.68/1.11  #Sup     : 14
% 1.68/1.11  #Fact    : 0
% 1.68/1.11  #Define  : 0
% 1.68/1.11  #Split   : 1
% 1.68/1.11  #Chain   : 0
% 1.68/1.11  #Close   : 0
% 1.68/1.11  
% 1.68/1.11  Ordering : KBO
% 1.68/1.11  
% 1.68/1.11  Simplification rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Subsume      : 0
% 1.68/1.11  #Demod        : 2
% 1.68/1.11  #Tautology    : 5
% 1.68/1.11  #SimpNegUnit  : 1
% 1.68/1.11  #BackRed      : 0
% 1.68/1.11  
% 1.68/1.11  #Partial instantiations: 0
% 1.68/1.11  #Strategies tried      : 1
% 1.68/1.11  
% 1.68/1.11  Timing (in seconds)
% 1.68/1.11  ----------------------
% 1.68/1.12  Preprocessing        : 0.26
% 1.68/1.12  Parsing              : 0.14
% 1.68/1.12  CNF conversion       : 0.02
% 1.68/1.12  Main loop            : 0.11
% 1.68/1.12  Inferencing          : 0.04
% 1.68/1.12  Reduction            : 0.03
% 1.68/1.12  Demodulation         : 0.02
% 1.68/1.12  BG Simplification    : 0.01
% 1.68/1.12  Subsumption          : 0.03
% 1.68/1.12  Abstraction          : 0.00
% 1.68/1.12  MUC search           : 0.00
% 1.68/1.12  Cooper               : 0.00
% 1.68/1.12  Total                : 0.40
% 1.68/1.12  Index Insertion      : 0.00
% 1.68/1.12  Index Deletion       : 0.00
% 1.68/1.12  Index Matching       : 0.00
% 1.68/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
