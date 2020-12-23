%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:57 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   48 (  48 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_4 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_77,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k4_enumset1(A_17,A_17,B_18,C_19,D_20,E_21) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_227,plain,(
    ! [D_133,C_130,E_131,F_132,A_129,B_134] : k5_enumset1(A_129,A_129,B_134,C_130,D_133,E_131,F_132) = k4_enumset1(A_129,B_134,C_130,D_133,E_131,F_132) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    ! [A_30,C_32,I_40,B_31,E_34,G_36,F_35] : r2_hidden(I_40,k5_enumset1(A_30,B_31,C_32,I_40,E_34,F_35,G_36)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_257,plain,(
    ! [B_137,A_139,E_135,C_138,F_136,D_140] : r2_hidden(C_138,k4_enumset1(A_139,B_137,C_138,D_140,E_135,F_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_42])).

tff(c_261,plain,(
    ! [B_143,D_144,C_141,E_145,A_142] : r2_hidden(B_143,k3_enumset1(A_142,B_143,C_141,D_144,E_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_257])).

tff(c_286,plain,(
    ! [A_149,B_150,C_151,D_152] : r2_hidden(A_149,k2_enumset1(A_149,B_150,C_151,D_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_261])).

tff(c_290,plain,(
    ! [A_153,B_154,C_155] : r2_hidden(A_153,k1_enumset1(A_153,B_154,C_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_286])).

tff(c_294,plain,(
    ! [A_156,B_157] : r2_hidden(A_156,k2_tarski(A_156,B_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_290])).

tff(c_298,plain,(
    ! [A_158] : r2_hidden(A_158,k1_tarski(A_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_294])).

tff(c_82,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_tarski(A_41)) = k1_ordinal1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_153,plain,(
    ! [D_54,B_55,A_56] :
      ( ~ r2_hidden(D_54,B_55)
      | r2_hidden(D_54,k2_xboole_0(A_56,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_159,plain,(
    ! [D_54,A_41] :
      ( ~ r2_hidden(D_54,k1_tarski(A_41))
      | r2_hidden(D_54,k1_ordinal1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_153])).

tff(c_302,plain,(
    ! [A_158] : r2_hidden(A_158,k1_ordinal1(A_158)) ),
    inference(resolution,[status(thm)],[c_298,c_159])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:10:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_4 > #skF_5 > #skF_2
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.49/1.35  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.49/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.35  
% 2.49/1.36  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.49/1.36  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.49/1.36  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.49/1.36  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.49/1.36  tff(f_44, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.49/1.36  tff(f_46, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.49/1.36  tff(f_75, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 2.49/1.36  tff(f_77, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.49/1.36  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.49/1.36  tff(f_80, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.49/1.36  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.49/1.36  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.49/1.36  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.36  tff(c_26, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.49/1.36  tff(c_28, plain, (![E_21, D_20, C_19, B_18, A_17]: (k4_enumset1(A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.49/1.36  tff(c_227, plain, (![D_133, C_130, E_131, F_132, A_129, B_134]: (k5_enumset1(A_129, A_129, B_134, C_130, D_133, E_131, F_132)=k4_enumset1(A_129, B_134, C_130, D_133, E_131, F_132))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.49/1.36  tff(c_42, plain, (![A_30, C_32, I_40, B_31, E_34, G_36, F_35]: (r2_hidden(I_40, k5_enumset1(A_30, B_31, C_32, I_40, E_34, F_35, G_36)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.36  tff(c_257, plain, (![B_137, A_139, E_135, C_138, F_136, D_140]: (r2_hidden(C_138, k4_enumset1(A_139, B_137, C_138, D_140, E_135, F_136)))), inference(superposition, [status(thm), theory('equality')], [c_227, c_42])).
% 2.49/1.36  tff(c_261, plain, (![B_143, D_144, C_141, E_145, A_142]: (r2_hidden(B_143, k3_enumset1(A_142, B_143, C_141, D_144, E_145)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_257])).
% 2.49/1.36  tff(c_286, plain, (![A_149, B_150, C_151, D_152]: (r2_hidden(A_149, k2_enumset1(A_149, B_150, C_151, D_152)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_261])).
% 2.49/1.36  tff(c_290, plain, (![A_153, B_154, C_155]: (r2_hidden(A_153, k1_enumset1(A_153, B_154, C_155)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_286])).
% 2.49/1.36  tff(c_294, plain, (![A_156, B_157]: (r2_hidden(A_156, k2_tarski(A_156, B_157)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_290])).
% 2.49/1.36  tff(c_298, plain, (![A_158]: (r2_hidden(A_158, k1_tarski(A_158)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_294])).
% 2.49/1.36  tff(c_82, plain, (![A_41]: (k2_xboole_0(A_41, k1_tarski(A_41))=k1_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.49/1.36  tff(c_153, plain, (![D_54, B_55, A_56]: (~r2_hidden(D_54, B_55) | r2_hidden(D_54, k2_xboole_0(A_56, B_55)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.49/1.36  tff(c_159, plain, (![D_54, A_41]: (~r2_hidden(D_54, k1_tarski(A_41)) | r2_hidden(D_54, k1_ordinal1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_153])).
% 2.49/1.36  tff(c_302, plain, (![A_158]: (r2_hidden(A_158, k1_ordinal1(A_158)))), inference(resolution, [status(thm)], [c_298, c_159])).
% 2.49/1.36  tff(c_84, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.49/1.36  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_302, c_84])).
% 2.49/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  Inference rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Ref     : 0
% 2.49/1.36  #Sup     : 52
% 2.49/1.36  #Fact    : 0
% 2.49/1.36  #Define  : 0
% 2.49/1.36  #Split   : 0
% 2.49/1.36  #Chain   : 0
% 2.49/1.36  #Close   : 0
% 2.49/1.36  
% 2.49/1.36  Ordering : KBO
% 2.49/1.36  
% 2.49/1.36  Simplification rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Subsume      : 3
% 2.49/1.36  #Demod        : 1
% 2.49/1.36  #Tautology    : 24
% 2.49/1.36  #SimpNegUnit  : 0
% 2.49/1.36  #BackRed      : 1
% 2.49/1.36  
% 2.49/1.36  #Partial instantiations: 0
% 2.49/1.36  #Strategies tried      : 1
% 2.49/1.36  
% 2.49/1.36  Timing (in seconds)
% 2.49/1.36  ----------------------
% 2.74/1.36  Preprocessing        : 0.35
% 2.74/1.36  Parsing              : 0.17
% 2.74/1.36  CNF conversion       : 0.03
% 2.74/1.36  Main loop            : 0.24
% 2.74/1.36  Inferencing          : 0.08
% 2.74/1.36  Reduction            : 0.06
% 2.74/1.36  Demodulation         : 0.05
% 2.74/1.36  BG Simplification    : 0.02
% 2.74/1.36  Subsumption          : 0.07
% 2.74/1.36  Abstraction          : 0.02
% 2.74/1.36  MUC search           : 0.00
% 2.74/1.36  Cooper               : 0.00
% 2.74/1.36  Total                : 0.62
% 2.74/1.36  Index Insertion      : 0.00
% 2.74/1.36  Index Deletion       : 0.00
% 2.74/1.37  Index Matching       : 0.00
% 2.74/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
