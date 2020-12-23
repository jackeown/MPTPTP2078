%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:25 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   42 (  85 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 ( 148 expanded)
%              Number of equality atoms :   27 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,
    ( k1_xboole_0 != '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_15,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_8,plain,
    ( r1_xboole_0('#skF_1','#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_25,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_15])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_4])).

tff(c_12,plain,
    ( r1_xboole_0('#skF_1','#skF_1')
    | ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_37,plain,(
    k3_xboole_0('#skF_2','#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_32])).

tff(c_41,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_42,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = '#skF_2'
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_2])).

tff(c_56,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_47])).

tff(c_61,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56])).

tff(c_63,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_61])).

tff(c_64,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_68,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    k3_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_68])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_77])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_110,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_4])).

tff(c_80,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_86,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_80])).

tff(c_14,plain,
    ( k1_xboole_0 != '#skF_1'
    | ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,(
    ~ r1_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_81,c_14])).

tff(c_113,plain,(
    k3_xboole_0('#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_110,c_106])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:33:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.11  %$ r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.64/1.11  
% 1.64/1.11  %Foreground sorts:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Background operators:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Foreground operators:
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.11  
% 1.64/1.12  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.64/1.12  tff(f_44, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.64/1.12  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.64/1.12  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.12  tff(c_10, plain, (k1_xboole_0!='#skF_1' | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.12  tff(c_15, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_10])).
% 1.64/1.12  tff(c_8, plain, (r1_xboole_0('#skF_1', '#skF_1') | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.12  tff(c_25, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_8])).
% 1.64/1.12  tff(c_26, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25, c_15])).
% 1.64/1.12  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.12  tff(c_34, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25, c_4])).
% 1.64/1.12  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_1') | ~r1_xboole_0('#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.12  tff(c_32, plain, (~r1_xboole_0('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_12])).
% 1.64/1.12  tff(c_37, plain, (k3_xboole_0('#skF_2', '#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_34, c_32])).
% 1.64/1.12  tff(c_41, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_37])).
% 1.64/1.12  tff(c_42, plain, (r1_xboole_0('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_12])).
% 1.64/1.12  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.12  tff(c_47, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)='#skF_2' | ~r1_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_2])).
% 1.64/1.12  tff(c_56, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_42, c_47])).
% 1.64/1.12  tff(c_61, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56])).
% 1.64/1.12  tff(c_63, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_61])).
% 1.64/1.12  tff(c_64, plain, (r1_xboole_0('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_8])).
% 1.64/1.12  tff(c_68, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.12  tff(c_74, plain, (k3_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_68])).
% 1.64/1.12  tff(c_77, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_74])).
% 1.64/1.12  tff(c_79, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15, c_77])).
% 1.64/1.12  tff(c_81, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_10])).
% 1.64/1.12  tff(c_110, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_4])).
% 1.64/1.12  tff(c_80, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_10])).
% 1.64/1.12  tff(c_86, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_80])).
% 1.64/1.12  tff(c_14, plain, (k1_xboole_0!='#skF_1' | ~r1_xboole_0('#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.12  tff(c_106, plain, (~r1_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_81, c_14])).
% 1.64/1.12  tff(c_113, plain, (k3_xboole_0('#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_110, c_106])).
% 1.64/1.12  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_113])).
% 1.64/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  Inference rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Ref     : 0
% 1.64/1.12  #Sup     : 19
% 1.64/1.12  #Fact    : 0
% 1.64/1.12  #Define  : 0
% 1.64/1.12  #Split   : 3
% 1.64/1.12  #Chain   : 0
% 1.64/1.12  #Close   : 0
% 1.64/1.12  
% 1.64/1.12  Ordering : KBO
% 1.64/1.12  
% 1.64/1.12  Simplification rules
% 1.64/1.12  ----------------------
% 1.64/1.13  #Subsume      : 3
% 1.64/1.13  #Demod        : 20
% 1.64/1.13  #Tautology    : 17
% 1.64/1.13  #SimpNegUnit  : 3
% 1.64/1.13  #BackRed      : 2
% 1.64/1.13  
% 1.64/1.13  #Partial instantiations: 0
% 1.64/1.13  #Strategies tried      : 1
% 1.64/1.13  
% 1.64/1.13  Timing (in seconds)
% 1.64/1.13  ----------------------
% 1.64/1.13  Preprocessing        : 0.26
% 1.64/1.13  Parsing              : 0.14
% 1.64/1.13  CNF conversion       : 0.02
% 1.64/1.13  Main loop            : 0.10
% 1.64/1.13  Inferencing          : 0.04
% 1.64/1.13  Reduction            : 0.03
% 1.64/1.13  Demodulation         : 0.02
% 1.64/1.13  BG Simplification    : 0.01
% 1.64/1.13  Subsumption          : 0.01
% 1.64/1.13  Abstraction          : 0.00
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.13  Total                : 0.39
% 1.64/1.13  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
