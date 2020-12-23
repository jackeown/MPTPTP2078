%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:53 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 105 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_45,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(k1_relat_1(B_20),A_21)
      | k9_relat_1(B_20,A_21) != k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_xboole_0(A_4,C_6)
      | ~ r1_xboole_0(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [A_27,A_28,B_29] :
      ( r1_xboole_0(A_27,A_28)
      | ~ r1_tarski(A_27,k1_relat_1(B_29))
      | k9_relat_1(B_29,A_28) != k1_xboole_0
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_45,c_10])).

tff(c_67,plain,(
    ! [A_28] :
      ( r1_xboole_0('#skF_1',A_28)
      | k9_relat_1('#skF_2',A_28) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_75,plain,(
    ! [A_30] :
      ( r1_xboole_0('#skF_1',A_30)
      | k9_relat_1('#skF_2',A_30) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_67])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [A_30] :
      ( ~ r1_tarski('#skF_1',A_30)
      | v1_xboole_0('#skF_1')
      | k9_relat_1('#skF_2',A_30) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_75,c_12])).

tff(c_84,plain,(
    ! [A_31] :
      ( ~ r1_tarski('#skF_1',A_31)
      | k9_relat_1('#skF_2',A_31) != k1_xboole_0 ) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_91,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_91])).

tff(c_97,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n007.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:19:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.13  
% 1.62/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.13  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.62/1.13  
% 1.62/1.13  %Foreground sorts:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Background operators:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Foreground operators:
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.62/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.13  
% 1.62/1.14  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 1.62/1.14  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.62/1.14  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.62/1.14  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.62/1.14  tff(f_49, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.62/1.14  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.62/1.14  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.62/1.14  tff(c_18, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.62/1.14  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.14  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.62/1.14  tff(c_20, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.62/1.14  tff(c_45, plain, (![B_20, A_21]: (r1_xboole_0(k1_relat_1(B_20), A_21) | k9_relat_1(B_20, A_21)!=k1_xboole_0 | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.62/1.14  tff(c_10, plain, (![A_4, C_6, B_5]: (r1_xboole_0(A_4, C_6) | ~r1_xboole_0(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.14  tff(c_65, plain, (![A_27, A_28, B_29]: (r1_xboole_0(A_27, A_28) | ~r1_tarski(A_27, k1_relat_1(B_29)) | k9_relat_1(B_29, A_28)!=k1_xboole_0 | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_45, c_10])).
% 1.62/1.14  tff(c_67, plain, (![A_28]: (r1_xboole_0('#skF_1', A_28) | k9_relat_1('#skF_2', A_28)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_65])).
% 1.62/1.14  tff(c_75, plain, (![A_30]: (r1_xboole_0('#skF_1', A_30) | k9_relat_1('#skF_2', A_30)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_67])).
% 1.62/1.14  tff(c_12, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.62/1.14  tff(c_82, plain, (![A_30]: (~r1_tarski('#skF_1', A_30) | v1_xboole_0('#skF_1') | k9_relat_1('#skF_2', A_30)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_75, c_12])).
% 1.62/1.14  tff(c_84, plain, (![A_31]: (~r1_tarski('#skF_1', A_31) | k9_relat_1('#skF_2', A_31)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_82])).
% 1.62/1.14  tff(c_91, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_84])).
% 1.62/1.14  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_91])).
% 1.62/1.14  tff(c_97, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_82])).
% 1.62/1.14  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.14  tff(c_113, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_97, c_2])).
% 1.62/1.14  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_113])).
% 1.62/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  Inference rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Ref     : 0
% 1.62/1.14  #Sup     : 18
% 1.62/1.14  #Fact    : 0
% 1.62/1.14  #Define  : 0
% 1.62/1.14  #Split   : 2
% 1.62/1.14  #Chain   : 0
% 1.62/1.14  #Close   : 0
% 1.62/1.14  
% 1.62/1.14  Ordering : KBO
% 1.62/1.14  
% 1.62/1.14  Simplification rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Subsume      : 1
% 1.62/1.14  #Demod        : 4
% 1.62/1.14  #Tautology    : 5
% 1.62/1.14  #SimpNegUnit  : 1
% 1.62/1.14  #BackRed      : 0
% 1.62/1.14  
% 1.62/1.14  #Partial instantiations: 0
% 1.62/1.14  #Strategies tried      : 1
% 1.62/1.14  
% 1.62/1.14  Timing (in seconds)
% 1.62/1.14  ----------------------
% 1.62/1.15  Preprocessing        : 0.26
% 1.62/1.15  Parsing              : 0.14
% 1.62/1.15  CNF conversion       : 0.02
% 1.62/1.15  Main loop            : 0.12
% 1.62/1.15  Inferencing          : 0.04
% 1.62/1.15  Reduction            : 0.03
% 1.62/1.15  Demodulation         : 0.02
% 1.62/1.15  BG Simplification    : 0.01
% 1.62/1.15  Subsumption          : 0.03
% 1.62/1.15  Abstraction          : 0.00
% 1.62/1.15  MUC search           : 0.00
% 1.62/1.15  Cooper               : 0.00
% 1.62/1.15  Total                : 0.41
% 1.62/1.15  Index Insertion      : 0.00
% 1.62/1.15  Index Deletion       : 0.00
% 1.62/1.15  Index Matching       : 0.00
% 1.62/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
