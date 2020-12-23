%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:23 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  85 expanded)
%              Number of equality atoms :   26 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_52,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    ! [A_34,B_35] : r2_hidden(A_34,k2_tarski(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_26])).

tff(c_88,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_85])).

tff(c_54,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,(
    ! [D_58,A_59,B_60] :
      ( r2_hidden(D_58,k4_xboole_0(A_59,B_60))
      | r2_hidden(D_58,B_60)
      | ~ r2_hidden(D_58,A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [D_6,A_45,B_46] :
      ( ~ r2_hidden(D_6,k4_xboole_0(A_45,B_46))
      | ~ r2_hidden(D_6,k3_xboole_0(A_45,B_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_195,plain,(
    ! [D_61,A_62,B_63] :
      ( ~ r2_hidden(D_61,k3_xboole_0(A_62,B_63))
      | r2_hidden(D_61,B_63)
      | ~ r2_hidden(D_61,A_62) ) ),
    inference(resolution,[status(thm)],[c_176,c_111])).

tff(c_309,plain,(
    ! [D_81] :
      ( ~ r2_hidden(D_81,k1_tarski('#skF_5'))
      | r2_hidden(D_81,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_81,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_195])).

tff(c_312,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_88,c_309])).

tff(c_315,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_312])).

tff(c_48,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_202,plain,(
    ! [E_64,C_65,B_66,A_67] :
      ( E_64 = C_65
      | E_64 = B_66
      | E_64 = A_67
      | ~ r2_hidden(E_64,k1_enumset1(A_67,B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_221,plain,(
    ! [E_68,B_69,A_70] :
      ( E_68 = B_69
      | E_68 = A_70
      | E_68 = A_70
      | ~ r2_hidden(E_68,k2_tarski(A_70,B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_202])).

tff(c_230,plain,(
    ! [E_68,A_16] :
      ( E_68 = A_16
      | E_68 = A_16
      | E_68 = A_16
      | ~ r2_hidden(E_68,k1_tarski(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_221])).

tff(c_318,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_315,c_230])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_52,c_318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:00:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.26/1.33  
% 2.26/1.33  %Foreground sorts:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Background operators:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Foreground operators:
% 2.26/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.26/1.33  
% 2.26/1.34  tff(f_63, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.26/1.34  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.34  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.26/1.34  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.26/1.34  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.26/1.34  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.26/1.34  tff(c_52, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.26/1.34  tff(c_46, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.34  tff(c_67, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.34  tff(c_26, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.26/1.34  tff(c_85, plain, (![A_34, B_35]: (r2_hidden(A_34, k2_tarski(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_26])).
% 2.26/1.34  tff(c_88, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_85])).
% 2.26/1.34  tff(c_54, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.26/1.34  tff(c_176, plain, (![D_58, A_59, B_60]: (r2_hidden(D_58, k4_xboole_0(A_59, B_60)) | r2_hidden(D_58, B_60) | ~r2_hidden(D_58, A_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.34  tff(c_102, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.34  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.34  tff(c_111, plain, (![D_6, A_45, B_46]: (~r2_hidden(D_6, k4_xboole_0(A_45, B_46)) | ~r2_hidden(D_6, k3_xboole_0(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 2.26/1.34  tff(c_195, plain, (![D_61, A_62, B_63]: (~r2_hidden(D_61, k3_xboole_0(A_62, B_63)) | r2_hidden(D_61, B_63) | ~r2_hidden(D_61, A_62))), inference(resolution, [status(thm)], [c_176, c_111])).
% 2.26/1.34  tff(c_309, plain, (![D_81]: (~r2_hidden(D_81, k1_tarski('#skF_5')) | r2_hidden(D_81, k1_tarski('#skF_6')) | ~r2_hidden(D_81, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_54, c_195])).
% 2.26/1.34  tff(c_312, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_88, c_309])).
% 2.26/1.34  tff(c_315, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_312])).
% 2.26/1.34  tff(c_48, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.34  tff(c_202, plain, (![E_64, C_65, B_66, A_67]: (E_64=C_65 | E_64=B_66 | E_64=A_67 | ~r2_hidden(E_64, k1_enumset1(A_67, B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.26/1.34  tff(c_221, plain, (![E_68, B_69, A_70]: (E_68=B_69 | E_68=A_70 | E_68=A_70 | ~r2_hidden(E_68, k2_tarski(A_70, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_202])).
% 2.26/1.34  tff(c_230, plain, (![E_68, A_16]: (E_68=A_16 | E_68=A_16 | E_68=A_16 | ~r2_hidden(E_68, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_221])).
% 2.26/1.34  tff(c_318, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_315, c_230])).
% 2.26/1.34  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_52, c_318])).
% 2.26/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  Inference rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Ref     : 0
% 2.26/1.34  #Sup     : 68
% 2.26/1.34  #Fact    : 0
% 2.26/1.34  #Define  : 0
% 2.26/1.34  #Split   : 0
% 2.26/1.34  #Chain   : 0
% 2.26/1.34  #Close   : 0
% 2.26/1.34  
% 2.26/1.34  Ordering : KBO
% 2.26/1.34  
% 2.26/1.34  Simplification rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Subsume      : 5
% 2.26/1.34  #Demod        : 12
% 2.26/1.34  #Tautology    : 32
% 2.26/1.34  #SimpNegUnit  : 1
% 2.26/1.34  #BackRed      : 0
% 2.26/1.34  
% 2.26/1.34  #Partial instantiations: 0
% 2.26/1.34  #Strategies tried      : 1
% 2.26/1.34  
% 2.26/1.34  Timing (in seconds)
% 2.26/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.32
% 2.26/1.34  Parsing              : 0.16
% 2.26/1.34  CNF conversion       : 0.02
% 2.26/1.34  Main loop            : 0.22
% 2.26/1.34  Inferencing          : 0.08
% 2.26/1.34  Reduction            : 0.07
% 2.26/1.34  Demodulation         : 0.05
% 2.26/1.34  BG Simplification    : 0.02
% 2.26/1.34  Subsumption          : 0.04
% 2.26/1.34  Abstraction          : 0.01
% 2.26/1.34  MUC search           : 0.00
% 2.26/1.34  Cooper               : 0.00
% 2.26/1.34  Total                : 0.57
% 2.26/1.34  Index Insertion      : 0.00
% 2.26/1.34  Index Deletion       : 0.00
% 2.26/1.34  Index Matching       : 0.00
% 2.26/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
