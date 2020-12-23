%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:56 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  70 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(k1_relat_1(B_25),A_26)
      | k9_relat_1(B_25,A_26) != k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_204,plain,(
    ! [B_39,A_40] :
      ( k4_xboole_0(k1_relat_1(B_39),A_40) = k1_relat_1(B_39)
      | k9_relat_1(B_39,A_40) != k1_xboole_0
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_xboole_0(A_20,C_21)
      | ~ r1_xboole_0(B_22,C_21)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [A_31,B_32,A_33] :
      ( r1_xboole_0(A_31,B_32)
      | ~ r1_tarski(A_31,A_33)
      | k4_xboole_0(A_33,B_32) != A_33 ) ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_156,plain,(
    ! [B_32] :
      ( r1_xboole_0('#skF_1',B_32)
      | k4_xboole_0(k1_relat_1('#skF_2'),B_32) != k1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_153])).

tff(c_211,plain,(
    ! [A_40] :
      ( r1_xboole_0('#skF_1',A_40)
      | k9_relat_1('#skF_2',A_40) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_156])).

tff(c_289,plain,(
    ! [A_44] :
      ( r1_xboole_0('#skF_1',A_44)
      | k9_relat_1('#skF_2',A_44) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_211])).

tff(c_330,plain,(
    ! [A_46] :
      ( k4_xboole_0('#skF_1',A_46) = '#skF_1'
      | k9_relat_1('#skF_2',A_46) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_289,c_10])).

tff(c_339,plain,(
    k4_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_330])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_51])).

tff(c_69,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_342,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_69])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.04/1.28  
% 2.04/1.28  %Foreground sorts:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Background operators:
% 2.04/1.28  
% 2.04/1.28  
% 2.04/1.28  %Foreground operators:
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.04/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.28  
% 2.04/1.29  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 2.04/1.29  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.04/1.29  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.04/1.29  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.04/1.29  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.04/1.29  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.04/1.29  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.04/1.29  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.29  tff(c_18, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.29  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.29  tff(c_114, plain, (![B_25, A_26]: (r1_xboole_0(k1_relat_1(B_25), A_26) | k9_relat_1(B_25, A_26)!=k1_xboole_0 | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.29  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.29  tff(c_204, plain, (![B_39, A_40]: (k4_xboole_0(k1_relat_1(B_39), A_40)=k1_relat_1(B_39) | k9_relat_1(B_39, A_40)!=k1_xboole_0 | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_114, c_10])).
% 2.04/1.29  tff(c_20, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.29  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.29  tff(c_70, plain, (![A_20, C_21, B_22]: (r1_xboole_0(A_20, C_21) | ~r1_xboole_0(B_22, C_21) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.29  tff(c_153, plain, (![A_31, B_32, A_33]: (r1_xboole_0(A_31, B_32) | ~r1_tarski(A_31, A_33) | k4_xboole_0(A_33, B_32)!=A_33)), inference(resolution, [status(thm)], [c_12, c_70])).
% 2.04/1.29  tff(c_156, plain, (![B_32]: (r1_xboole_0('#skF_1', B_32) | k4_xboole_0(k1_relat_1('#skF_2'), B_32)!=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_153])).
% 2.04/1.29  tff(c_211, plain, (![A_40]: (r1_xboole_0('#skF_1', A_40) | k9_relat_1('#skF_2', A_40)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_156])).
% 2.04/1.29  tff(c_289, plain, (![A_44]: (r1_xboole_0('#skF_1', A_44) | k9_relat_1('#skF_2', A_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_211])).
% 2.04/1.29  tff(c_330, plain, (![A_46]: (k4_xboole_0('#skF_1', A_46)='#skF_1' | k9_relat_1('#skF_2', A_46)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_289, c_10])).
% 2.04/1.29  tff(c_339, plain, (k4_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_18, c_330])).
% 2.04/1.29  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.29  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.29  tff(c_51, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.29  tff(c_66, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_51])).
% 2.04/1.29  tff(c_69, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_66])).
% 2.04/1.29  tff(c_342, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_339, c_69])).
% 2.04/1.29  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_342])).
% 2.04/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  Inference rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Ref     : 0
% 2.04/1.29  #Sup     : 78
% 2.04/1.29  #Fact    : 0
% 2.04/1.29  #Define  : 0
% 2.04/1.29  #Split   : 1
% 2.04/1.29  #Chain   : 0
% 2.04/1.29  #Close   : 0
% 2.04/1.29  
% 2.04/1.29  Ordering : KBO
% 2.04/1.29  
% 2.04/1.29  Simplification rules
% 2.04/1.29  ----------------------
% 2.04/1.29  #Subsume      : 2
% 2.04/1.29  #Demod        : 19
% 2.04/1.29  #Tautology    : 36
% 2.04/1.29  #SimpNegUnit  : 1
% 2.04/1.29  #BackRed      : 0
% 2.04/1.29  
% 2.04/1.29  #Partial instantiations: 0
% 2.04/1.29  #Strategies tried      : 1
% 2.04/1.29  
% 2.04/1.29  Timing (in seconds)
% 2.04/1.29  ----------------------
% 2.04/1.29  Preprocessing        : 0.27
% 2.04/1.29  Parsing              : 0.14
% 2.04/1.29  CNF conversion       : 0.02
% 2.04/1.29  Main loop            : 0.21
% 2.04/1.30  Inferencing          : 0.08
% 2.04/1.30  Reduction            : 0.06
% 2.04/1.30  Demodulation         : 0.04
% 2.04/1.30  BG Simplification    : 0.01
% 2.04/1.30  Subsumption          : 0.04
% 2.04/1.30  Abstraction          : 0.01
% 2.04/1.30  MUC search           : 0.00
% 2.04/1.30  Cooper               : 0.00
% 2.04/1.30  Total                : 0.50
% 2.04/1.30  Index Insertion      : 0.00
% 2.04/1.30  Index Deletion       : 0.00
% 2.04/1.30  Index Matching       : 0.00
% 2.04/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
