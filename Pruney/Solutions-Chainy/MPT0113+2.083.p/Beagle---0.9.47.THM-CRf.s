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
% DateTime   : Thu Dec  3 09:45:22 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   47 (  70 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 114 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_24,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_184,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_xboole_0(A_60,C_61)
      | ~ r1_tarski(B_62,C_61)
      | ~ r2_xboole_0(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_205,plain,(
    ! [A_64,A_65,B_66] :
      ( r2_xboole_0(A_64,A_65)
      | ~ r2_xboole_0(A_64,k4_xboole_0(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_12,c_184])).

tff(c_628,plain,(
    ! [A_127,A_128,B_129] :
      ( r2_xboole_0(A_127,A_128)
      | k4_xboole_0(A_128,B_129) = A_127
      | ~ r1_tarski(A_127,k4_xboole_0(A_128,B_129)) ) ),
    inference(resolution,[status(thm)],[c_2,c_205])).

tff(c_640,plain,
    ( r2_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_628])).

tff(c_642,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_640])).

tff(c_698,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_12])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_698])).

tff(c_710,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_640])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_714,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_710,c_6])).

tff(c_718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_714])).

tff(c_719,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_722,plain,(
    ! [B_132,A_133] :
      ( r1_xboole_0(B_132,A_133)
      | ~ r1_xboole_0(A_133,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_725,plain,(
    ! [B_16,A_15] : r1_xboole_0(B_16,k4_xboole_0(A_15,B_16)) ),
    inference(resolution,[status(thm)],[c_22,c_722])).

tff(c_731,plain,(
    ! [A_136,B_137] :
      ( k2_xboole_0(A_136,B_137) = B_137
      | ~ r1_tarski(A_136,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_742,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_731])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_xboole_0(A_12,B_13)
      | ~ r1_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1043,plain,(
    ! [A_194] :
      ( r1_xboole_0(A_194,'#skF_1')
      | ~ r1_xboole_0(A_194,k4_xboole_0('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_20])).

tff(c_1078,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_725,c_1043])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1082,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_1078,c_8])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_719,c_1082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:22:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.45  
% 3.15/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.45  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.15/1.45  
% 3.15/1.45  %Foreground sorts:
% 3.15/1.45  
% 3.15/1.45  
% 3.15/1.45  %Background operators:
% 3.15/1.45  
% 3.15/1.45  
% 3.15/1.45  %Foreground operators:
% 3.15/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.45  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.15/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.45  
% 3.15/1.46  tff(f_73, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.15/1.46  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.15/1.46  tff(f_42, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.15/1.46  tff(f_48, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 3.15/1.46  tff(f_66, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.15/1.46  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.15/1.46  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.15/1.46  tff(f_64, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.15/1.46  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.15/1.46  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 3.15/1.46  tff(c_26, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.15/1.46  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.46  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.46  tff(c_184, plain, (![A_60, C_61, B_62]: (r2_xboole_0(A_60, C_61) | ~r1_tarski(B_62, C_61) | ~r2_xboole_0(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.15/1.46  tff(c_205, plain, (![A_64, A_65, B_66]: (r2_xboole_0(A_64, A_65) | ~r2_xboole_0(A_64, k4_xboole_0(A_65, B_66)))), inference(resolution, [status(thm)], [c_12, c_184])).
% 3.15/1.46  tff(c_628, plain, (![A_127, A_128, B_129]: (r2_xboole_0(A_127, A_128) | k4_xboole_0(A_128, B_129)=A_127 | ~r1_tarski(A_127, k4_xboole_0(A_128, B_129)))), inference(resolution, [status(thm)], [c_2, c_205])).
% 3.15/1.46  tff(c_640, plain, (r2_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_2', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_26, c_628])).
% 3.15/1.46  tff(c_642, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_640])).
% 3.15/1.46  tff(c_698, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_642, c_12])).
% 3.15/1.46  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_698])).
% 3.15/1.46  tff(c_710, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_640])).
% 3.15/1.46  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.46  tff(c_714, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_710, c_6])).
% 3.15/1.46  tff(c_718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_714])).
% 3.15/1.46  tff(c_719, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 3.15/1.46  tff(c_22, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.46  tff(c_722, plain, (![B_132, A_133]: (r1_xboole_0(B_132, A_133) | ~r1_xboole_0(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.15/1.46  tff(c_725, plain, (![B_16, A_15]: (r1_xboole_0(B_16, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_22, c_722])).
% 3.15/1.46  tff(c_731, plain, (![A_136, B_137]: (k2_xboole_0(A_136, B_137)=B_137 | ~r1_tarski(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.46  tff(c_742, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_731])).
% 3.15/1.46  tff(c_20, plain, (![A_12, B_13, C_14]: (r1_xboole_0(A_12, B_13) | ~r1_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.15/1.46  tff(c_1043, plain, (![A_194]: (r1_xboole_0(A_194, '#skF_1') | ~r1_xboole_0(A_194, k4_xboole_0('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_742, c_20])).
% 3.15/1.46  tff(c_1078, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_725, c_1043])).
% 3.15/1.46  tff(c_8, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.15/1.46  tff(c_1082, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_1078, c_8])).
% 3.15/1.46  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_719, c_1082])).
% 3.15/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.46  
% 3.15/1.46  Inference rules
% 3.15/1.46  ----------------------
% 3.15/1.46  #Ref     : 0
% 3.15/1.46  #Sup     : 240
% 3.15/1.46  #Fact    : 0
% 3.15/1.46  #Define  : 0
% 3.15/1.46  #Split   : 6
% 3.15/1.46  #Chain   : 0
% 3.15/1.46  #Close   : 0
% 3.15/1.46  
% 3.15/1.46  Ordering : KBO
% 3.15/1.46  
% 3.15/1.46  Simplification rules
% 3.15/1.46  ----------------------
% 3.15/1.46  #Subsume      : 14
% 3.15/1.46  #Demod        : 76
% 3.15/1.46  #Tautology    : 96
% 3.15/1.46  #SimpNegUnit  : 3
% 3.15/1.46  #BackRed      : 8
% 3.15/1.46  
% 3.15/1.46  #Partial instantiations: 0
% 3.15/1.46  #Strategies tried      : 1
% 3.15/1.46  
% 3.15/1.46  Timing (in seconds)
% 3.15/1.46  ----------------------
% 3.15/1.47  Preprocessing        : 0.27
% 3.15/1.47  Parsing              : 0.15
% 3.15/1.47  CNF conversion       : 0.02
% 3.15/1.47  Main loop            : 0.44
% 3.15/1.47  Inferencing          : 0.17
% 3.15/1.47  Reduction            : 0.14
% 3.15/1.47  Demodulation         : 0.10
% 3.15/1.47  BG Simplification    : 0.02
% 3.15/1.47  Subsumption          : 0.09
% 3.15/1.47  Abstraction          : 0.02
% 3.15/1.47  MUC search           : 0.00
% 3.15/1.47  Cooper               : 0.00
% 3.15/1.47  Total                : 0.73
% 3.15/1.47  Index Insertion      : 0.00
% 3.15/1.47  Index Deletion       : 0.00
% 3.15/1.47  Index Matching       : 0.00
% 3.15/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
