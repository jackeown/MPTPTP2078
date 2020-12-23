%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:13 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   50 (  58 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 104 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(B_27,A_28)
      | ~ r1_xboole_0(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_368,plain,(
    ! [A_102,C_103,B_104] :
      ( ~ r1_xboole_0(A_102,C_103)
      | ~ r1_xboole_0(A_102,B_104)
      | r1_xboole_0(A_102,k2_xboole_0(B_104,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_661,plain,(
    ! [B_155,C_156,A_157] :
      ( r1_xboole_0(k2_xboole_0(B_155,C_156),A_157)
      | ~ r1_xboole_0(A_157,C_156)
      | ~ r1_xboole_0(A_157,B_155) ) ),
    inference(resolution,[status(thm)],[c_368,c_2])).

tff(c_32,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_682,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_661,c_32])).

tff(c_691,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_682])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,k1_tarski(B_23)) = A_22
      | r2_hidden(B_23,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_410,plain,(
    ! [A_122,C_123,B_124,D_125] :
      ( r1_xboole_0(A_122,C_123)
      | ~ r1_xboole_0(B_124,D_125)
      | ~ r1_tarski(C_123,D_125)
      | ~ r1_tarski(A_122,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_551,plain,(
    ! [A_138,C_139,B_140,A_141] :
      ( r1_xboole_0(A_138,C_139)
      | ~ r1_tarski(C_139,B_140)
      | ~ r1_tarski(A_138,k4_xboole_0(A_141,B_140)) ) ),
    inference(resolution,[status(thm)],[c_26,c_410])).

tff(c_579,plain,(
    ! [A_149,A_150] :
      ( r1_xboole_0(A_149,k3_xboole_0('#skF_2','#skF_3'))
      | ~ r1_tarski(A_149,k4_xboole_0(A_150,k1_tarski('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_551])).

tff(c_589,plain,(
    ! [A_151] : r1_xboole_0(k4_xboole_0(A_151,k1_tarski('#skF_5')),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_579])).

tff(c_622,plain,(
    ! [A_153] :
      ( r1_xboole_0(A_153,k3_xboole_0('#skF_2','#skF_3'))
      | r2_hidden('#skF_5',A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_589])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r1_xboole_0(A_17,k3_xboole_0(B_18,C_19))
      | ~ r1_tarski(A_17,C_19)
      | r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_704,plain,(
    ! [A_161] :
      ( ~ r1_tarski(A_161,'#skF_3')
      | r1_xboole_0(A_161,'#skF_2')
      | r2_hidden('#skF_5',A_161) ) ),
    inference(resolution,[status(thm)],[c_622,c_24])).

tff(c_159,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,B_64)
      | ~ r2_hidden(C_65,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_189,plain,(
    ! [C_65] :
      ( ~ r2_hidden(C_65,'#skF_3')
      | ~ r2_hidden(C_65,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_159])).

tff(c_723,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3')
    | r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_704,c_189])).

tff(c_730,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36,c_723])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:20:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.41  
% 2.80/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.80/1.41  
% 2.80/1.41  %Foreground sorts:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Background operators:
% 2.80/1.41  
% 2.80/1.41  
% 2.80/1.41  %Foreground operators:
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.41  
% 2.80/1.42  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.80/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.80/1.42  tff(f_77, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.80/1.42  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.42  tff(f_92, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.80/1.42  tff(f_87, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.80/1.42  tff(f_61, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 2.80/1.42  tff(f_85, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.80/1.42  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.80/1.42  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_42, plain, (![B_27, A_28]: (r1_xboole_0(B_27, A_28) | ~r1_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.42  tff(c_48, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_42])).
% 2.80/1.42  tff(c_368, plain, (![A_102, C_103, B_104]: (~r1_xboole_0(A_102, C_103) | ~r1_xboole_0(A_102, B_104) | r1_xboole_0(A_102, k2_xboole_0(B_104, C_103)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.80/1.42  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.42  tff(c_661, plain, (![B_155, C_156, A_157]: (r1_xboole_0(k2_xboole_0(B_155, C_156), A_157) | ~r1_xboole_0(A_157, C_156) | ~r1_xboole_0(A_157, B_155))), inference(resolution, [status(thm)], [c_368, c_2])).
% 2.80/1.42  tff(c_32, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_682, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_661, c_32])).
% 2.80/1.42  tff(c_691, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_682])).
% 2.80/1.42  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.42  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_30, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k1_tarski(B_23))=A_22 | r2_hidden(B_23, A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.42  tff(c_38, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.42  tff(c_26, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.80/1.42  tff(c_410, plain, (![A_122, C_123, B_124, D_125]: (r1_xboole_0(A_122, C_123) | ~r1_xboole_0(B_124, D_125) | ~r1_tarski(C_123, D_125) | ~r1_tarski(A_122, B_124))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.80/1.42  tff(c_551, plain, (![A_138, C_139, B_140, A_141]: (r1_xboole_0(A_138, C_139) | ~r1_tarski(C_139, B_140) | ~r1_tarski(A_138, k4_xboole_0(A_141, B_140)))), inference(resolution, [status(thm)], [c_26, c_410])).
% 2.80/1.42  tff(c_579, plain, (![A_149, A_150]: (r1_xboole_0(A_149, k3_xboole_0('#skF_2', '#skF_3')) | ~r1_tarski(A_149, k4_xboole_0(A_150, k1_tarski('#skF_5'))))), inference(resolution, [status(thm)], [c_38, c_551])).
% 2.80/1.42  tff(c_589, plain, (![A_151]: (r1_xboole_0(k4_xboole_0(A_151, k1_tarski('#skF_5')), k3_xboole_0('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_14, c_579])).
% 2.80/1.42  tff(c_622, plain, (![A_153]: (r1_xboole_0(A_153, k3_xboole_0('#skF_2', '#skF_3')) | r2_hidden('#skF_5', A_153))), inference(superposition, [status(thm), theory('equality')], [c_30, c_589])).
% 2.80/1.42  tff(c_24, plain, (![A_17, B_18, C_19]: (~r1_xboole_0(A_17, k3_xboole_0(B_18, C_19)) | ~r1_tarski(A_17, C_19) | r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.42  tff(c_704, plain, (![A_161]: (~r1_tarski(A_161, '#skF_3') | r1_xboole_0(A_161, '#skF_2') | r2_hidden('#skF_5', A_161))), inference(resolution, [status(thm)], [c_622, c_24])).
% 2.80/1.42  tff(c_159, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, B_64) | ~r2_hidden(C_65, A_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.42  tff(c_189, plain, (![C_65]: (~r2_hidden(C_65, '#skF_3') | ~r2_hidden(C_65, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_159])).
% 2.80/1.42  tff(c_723, plain, (~r2_hidden('#skF_5', '#skF_4') | ~r1_tarski('#skF_3', '#skF_3') | r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_704, c_189])).
% 2.80/1.42  tff(c_730, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36, c_723])).
% 2.80/1.42  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_691, c_730])).
% 2.80/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  Inference rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Ref     : 0
% 2.80/1.42  #Sup     : 161
% 2.80/1.42  #Fact    : 0
% 2.80/1.42  #Define  : 0
% 2.80/1.42  #Split   : 3
% 2.80/1.42  #Chain   : 0
% 2.80/1.42  #Close   : 0
% 2.80/1.42  
% 2.80/1.42  Ordering : KBO
% 2.80/1.42  
% 2.80/1.42  Simplification rules
% 2.80/1.42  ----------------------
% 2.80/1.42  #Subsume      : 12
% 2.80/1.42  #Demod        : 19
% 2.80/1.42  #Tautology    : 19
% 2.80/1.42  #SimpNegUnit  : 1
% 2.80/1.42  #BackRed      : 0
% 2.80/1.42  
% 2.80/1.42  #Partial instantiations: 0
% 2.80/1.42  #Strategies tried      : 1
% 2.80/1.42  
% 2.80/1.42  Timing (in seconds)
% 2.80/1.42  ----------------------
% 2.80/1.43  Preprocessing        : 0.28
% 2.80/1.43  Parsing              : 0.16
% 2.80/1.43  CNF conversion       : 0.02
% 2.80/1.43  Main loop            : 0.38
% 2.80/1.43  Inferencing          : 0.14
% 2.80/1.43  Reduction            : 0.10
% 2.80/1.43  Demodulation         : 0.08
% 2.80/1.43  BG Simplification    : 0.02
% 2.80/1.43  Subsumption          : 0.09
% 2.80/1.43  Abstraction          : 0.01
% 2.80/1.43  MUC search           : 0.00
% 2.80/1.43  Cooper               : 0.00
% 2.80/1.43  Total                : 0.69
% 2.80/1.43  Index Insertion      : 0.00
% 2.80/1.43  Index Deletion       : 0.00
% 2.80/1.43  Index Matching       : 0.00
% 2.80/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
