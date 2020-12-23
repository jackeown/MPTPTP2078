%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:30 EST 2020

% Result     : Theorem 14.80s
% Output     : CNFRefutation 14.83s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  66 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_16,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_498,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(A_69,C_70)
      | ~ r1_tarski(B_71,C_70)
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_561,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,'#skF_2')
      | ~ r1_tarski(A_73,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_498])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_735,plain,(
    ! [A_80] :
      ( k2_xboole_0(A_80,'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_80,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_561,c_12])).

tff(c_747,plain,(
    ! [B_81] : k2_xboole_0(k4_xboole_0('#skF_1',B_81),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_735])).

tff(c_22,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_777,plain,(
    ! [B_81] : r1_tarski(k4_xboole_0('#skF_1',B_81),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_22])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_532,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,'#skF_2')
      | ~ r1_tarski(A_72,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_498])).

tff(c_921,plain,(
    ! [A_87] :
      ( k2_xboole_0(A_87,'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_87,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_532,c_12])).

tff(c_933,plain,(
    ! [B_88] : k2_xboole_0(k4_xboole_0('#skF_3',B_88),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_921])).

tff(c_969,plain,(
    ! [B_88] : r1_tarski(k4_xboole_0('#skF_3',B_88),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_22])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1345,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_tarski(k2_xboole_0(A_107,C_108),B_109)
      | ~ r1_tarski(C_108,B_109)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24322,plain,(
    ! [A_384,B_385,B_386] :
      ( r1_tarski(k5_xboole_0(A_384,B_385),B_386)
      | ~ r1_tarski(k4_xboole_0(B_385,A_384),B_386)
      | ~ r1_tarski(k4_xboole_0(A_384,B_385),B_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1345])).

tff(c_30,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24397,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24322,c_30])).

tff(c_24450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_969,c_24397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:45:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.80/6.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.80/6.62  
% 14.80/6.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.80/6.62  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 14.80/6.62  
% 14.80/6.62  %Foreground sorts:
% 14.80/6.62  
% 14.80/6.62  
% 14.80/6.62  %Background operators:
% 14.80/6.62  
% 14.80/6.62  
% 14.80/6.62  %Foreground operators:
% 14.80/6.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.80/6.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.80/6.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.80/6.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.80/6.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.80/6.62  tff('#skF_2', type, '#skF_2': $i).
% 14.80/6.62  tff('#skF_3', type, '#skF_3': $i).
% 14.80/6.62  tff('#skF_1', type, '#skF_1': $i).
% 14.80/6.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.80/6.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.80/6.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.80/6.62  
% 14.83/6.63  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.83/6.63  tff(f_82, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 14.83/6.63  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.83/6.63  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.83/6.63  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.83/6.63  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 14.83/6.63  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 14.83/6.63  tff(c_16, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.83/6.63  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.83/6.63  tff(c_498, plain, (![A_69, C_70, B_71]: (r1_tarski(A_69, C_70) | ~r1_tarski(B_71, C_70) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.83/6.63  tff(c_561, plain, (![A_73]: (r1_tarski(A_73, '#skF_2') | ~r1_tarski(A_73, '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_498])).
% 14.83/6.63  tff(c_12, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.83/6.63  tff(c_735, plain, (![A_80]: (k2_xboole_0(A_80, '#skF_2')='#skF_2' | ~r1_tarski(A_80, '#skF_1'))), inference(resolution, [status(thm)], [c_561, c_12])).
% 14.83/6.63  tff(c_747, plain, (![B_81]: (k2_xboole_0(k4_xboole_0('#skF_1', B_81), '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_16, c_735])).
% 14.83/6.63  tff(c_22, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.83/6.63  tff(c_777, plain, (![B_81]: (r1_tarski(k4_xboole_0('#skF_1', B_81), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_747, c_22])).
% 14.83/6.63  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.83/6.63  tff(c_532, plain, (![A_72]: (r1_tarski(A_72, '#skF_2') | ~r1_tarski(A_72, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_498])).
% 14.83/6.63  tff(c_921, plain, (![A_87]: (k2_xboole_0(A_87, '#skF_2')='#skF_2' | ~r1_tarski(A_87, '#skF_3'))), inference(resolution, [status(thm)], [c_532, c_12])).
% 14.83/6.63  tff(c_933, plain, (![B_88]: (k2_xboole_0(k4_xboole_0('#skF_3', B_88), '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_16, c_921])).
% 14.83/6.63  tff(c_969, plain, (![B_88]: (r1_tarski(k4_xboole_0('#skF_3', B_88), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_933, c_22])).
% 14.83/6.63  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.83/6.63  tff(c_1345, plain, (![A_107, C_108, B_109]: (r1_tarski(k2_xboole_0(A_107, C_108), B_109) | ~r1_tarski(C_108, B_109) | ~r1_tarski(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.83/6.63  tff(c_24322, plain, (![A_384, B_385, B_386]: (r1_tarski(k5_xboole_0(A_384, B_385), B_386) | ~r1_tarski(k4_xboole_0(B_385, A_384), B_386) | ~r1_tarski(k4_xboole_0(A_384, B_385), B_386))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1345])).
% 14.83/6.63  tff(c_30, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.83/6.63  tff(c_24397, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_24322, c_30])).
% 14.83/6.63  tff(c_24450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_777, c_969, c_24397])).
% 14.83/6.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.83/6.63  
% 14.83/6.63  Inference rules
% 14.83/6.63  ----------------------
% 14.83/6.63  #Ref     : 0
% 14.83/6.63  #Sup     : 6192
% 14.83/6.63  #Fact    : 0
% 14.83/6.63  #Define  : 0
% 14.83/6.63  #Split   : 2
% 14.83/6.63  #Chain   : 0
% 14.83/6.63  #Close   : 0
% 14.83/6.63  
% 14.83/6.63  Ordering : KBO
% 14.83/6.63  
% 14.83/6.63  Simplification rules
% 14.83/6.63  ----------------------
% 14.83/6.63  #Subsume      : 1350
% 14.83/6.63  #Demod        : 4064
% 14.83/6.63  #Tautology    : 2906
% 14.83/6.63  #SimpNegUnit  : 6
% 14.83/6.63  #BackRed      : 3
% 14.83/6.63  
% 14.83/6.63  #Partial instantiations: 0
% 14.83/6.63  #Strategies tried      : 1
% 14.83/6.63  
% 14.83/6.63  Timing (in seconds)
% 14.83/6.63  ----------------------
% 14.83/6.63  Preprocessing        : 0.45
% 14.83/6.63  Parsing              : 0.24
% 14.83/6.63  CNF conversion       : 0.03
% 14.83/6.63  Main loop            : 5.33
% 14.83/6.63  Inferencing          : 1.04
% 14.83/6.63  Reduction            : 2.63
% 14.83/6.63  Demodulation         : 2.25
% 14.83/6.63  BG Simplification    : 0.12
% 14.83/6.63  Subsumption          : 1.25
% 14.83/6.63  Abstraction          : 0.15
% 14.83/6.63  MUC search           : 0.00
% 14.83/6.63  Cooper               : 0.00
% 14.83/6.63  Total                : 5.81
% 14.83/6.63  Index Insertion      : 0.00
% 14.83/6.63  Index Deletion       : 0.00
% 14.83/6.63  Index Matching       : 0.00
% 14.83/6.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
