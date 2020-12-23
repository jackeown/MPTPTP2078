%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:44 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  72 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_110,plain,(
    ! [B_31,A_32] :
      ( r1_xboole_0(k2_relat_1(B_31),A_32)
      | k10_relat_1(B_31,A_32) != k1_xboole_0
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [B_42,A_43] :
      ( k4_xboole_0(k2_relat_1(B_42),A_43) = k2_relat_1(B_42)
      | k10_relat_1(B_42,A_43) != k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_110,c_14])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_xboole_0(A_24,C_25)
      | ~ r1_xboole_0(B_26,C_25)
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_33,B_34,A_35] :
      ( r1_xboole_0(A_33,B_34)
      | ~ r1_tarski(A_33,A_35)
      | k4_xboole_0(A_35,B_34) != A_35 ) ),
    inference(resolution,[status(thm)],[c_16,c_84])).

tff(c_130,plain,(
    ! [B_34] :
      ( r1_xboole_0('#skF_1',B_34)
      | k4_xboole_0(k2_relat_1('#skF_2'),B_34) != k2_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_122])).

tff(c_164,plain,(
    ! [A_43] :
      ( r1_xboole_0('#skF_1',A_43)
      | k10_relat_1('#skF_2',A_43) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_130])).

tff(c_187,plain,(
    ! [A_44] :
      ( r1_xboole_0('#skF_1',A_44)
      | k10_relat_1('#skF_2',A_44) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_164])).

tff(c_195,plain,(
    ! [A_45] :
      ( k4_xboole_0('#skF_1',A_45) = '#skF_1'
      | k10_relat_1('#skF_2',A_45) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_187,c_14])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_206,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_54])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_206])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.98/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  
% 2.04/1.24  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.04/1.24  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.04/1.24  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.04/1.24  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.04/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.24  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.04/1.24  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.24  tff(c_22, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.24  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.24  tff(c_110, plain, (![B_31, A_32]: (r1_xboole_0(k2_relat_1(B_31), A_32) | k10_relat_1(B_31, A_32)!=k1_xboole_0 | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.24  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.24  tff(c_153, plain, (![B_42, A_43]: (k4_xboole_0(k2_relat_1(B_42), A_43)=k2_relat_1(B_42) | k10_relat_1(B_42, A_43)!=k1_xboole_0 | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_110, c_14])).
% 2.04/1.24  tff(c_24, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.24  tff(c_16, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.24  tff(c_84, plain, (![A_24, C_25, B_26]: (r1_xboole_0(A_24, C_25) | ~r1_xboole_0(B_26, C_25) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.24  tff(c_122, plain, (![A_33, B_34, A_35]: (r1_xboole_0(A_33, B_34) | ~r1_tarski(A_33, A_35) | k4_xboole_0(A_35, B_34)!=A_35)), inference(resolution, [status(thm)], [c_16, c_84])).
% 2.04/1.24  tff(c_130, plain, (![B_34]: (r1_xboole_0('#skF_1', B_34) | k4_xboole_0(k2_relat_1('#skF_2'), B_34)!=k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_122])).
% 2.04/1.24  tff(c_164, plain, (![A_43]: (r1_xboole_0('#skF_1', A_43) | k10_relat_1('#skF_2', A_43)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_130])).
% 2.04/1.24  tff(c_187, plain, (![A_44]: (r1_xboole_0('#skF_1', A_44) | k10_relat_1('#skF_2', A_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_164])).
% 2.04/1.24  tff(c_195, plain, (![A_45]: (k4_xboole_0('#skF_1', A_45)='#skF_1' | k10_relat_1('#skF_2', A_45)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_187, c_14])).
% 2.04/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.24  tff(c_42, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.24  tff(c_54, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.04/1.24  tff(c_206, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_195, c_54])).
% 2.04/1.24  tff(c_223, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_206])).
% 2.04/1.24  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_223])).
% 2.04/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  Inference rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Ref     : 0
% 2.04/1.24  #Sup     : 48
% 2.04/1.24  #Fact    : 0
% 2.04/1.24  #Define  : 0
% 2.04/1.24  #Split   : 2
% 2.04/1.24  #Chain   : 0
% 2.04/1.24  #Close   : 0
% 2.04/1.24  
% 2.04/1.24  Ordering : KBO
% 2.04/1.24  
% 2.04/1.24  Simplification rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Subsume      : 6
% 2.04/1.24  #Demod        : 8
% 2.04/1.24  #Tautology    : 16
% 2.04/1.24  #SimpNegUnit  : 1
% 2.04/1.24  #BackRed      : 0
% 2.04/1.24  
% 2.04/1.24  #Partial instantiations: 0
% 2.04/1.24  #Strategies tried      : 1
% 2.04/1.24  
% 2.04/1.24  Timing (in seconds)
% 2.04/1.24  ----------------------
% 2.04/1.24  Preprocessing        : 0.30
% 2.04/1.25  Parsing              : 0.16
% 2.04/1.25  CNF conversion       : 0.02
% 2.04/1.25  Main loop            : 0.18
% 2.04/1.25  Inferencing          : 0.07
% 2.04/1.25  Reduction            : 0.05
% 2.04/1.25  Demodulation         : 0.04
% 2.04/1.25  BG Simplification    : 0.02
% 2.04/1.25  Subsumption          : 0.04
% 2.04/1.25  Abstraction          : 0.01
% 2.04/1.25  MUC search           : 0.00
% 2.04/1.25  Cooper               : 0.00
% 2.04/1.25  Total                : 0.51
% 2.04/1.25  Index Insertion      : 0.00
% 2.04/1.25  Index Deletion       : 0.00
% 2.04/1.25  Index Matching       : 0.00
% 2.04/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
