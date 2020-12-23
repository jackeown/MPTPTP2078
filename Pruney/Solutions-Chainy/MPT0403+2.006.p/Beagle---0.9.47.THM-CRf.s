%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:41 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  68 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_setfam_1(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_setfam_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_49] : r1_setfam_1(A_49,A_49) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [E_64,F_65,A_66,B_67] :
      ( r2_hidden(k2_xboole_0(E_64,F_65),k2_setfam_1(A_66,B_67))
      | ~ r2_hidden(F_65,B_67)
      | ~ r2_hidden(E_64,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [A_1,A_66,B_67] :
      ( r2_hidden(A_1,k2_setfam_1(A_66,B_67))
      | ~ r2_hidden(A_1,B_67)
      | ~ r2_hidden(A_1,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_6,plain,(
    ! [A_3,B_4,C_13] :
      ( r2_hidden('#skF_2'(A_3,B_4,C_13),B_4)
      | ~ r2_hidden(C_13,A_3)
      | ~ r1_setfam_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(C_61,'#skF_2'(A_62,B_63,C_61))
      | ~ r2_hidden(C_61,A_62)
      | ~ r1_setfam_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4,D_12] :
      ( ~ r1_tarski('#skF_1'(A_3,B_4),D_12)
      | ~ r2_hidden(D_12,B_4)
      | r1_setfam_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [A_86,B_87,A_88,B_89] :
      ( ~ r2_hidden('#skF_2'(A_86,B_87,'#skF_1'(A_88,B_89)),B_89)
      | r1_setfam_1(A_88,B_89)
      | ~ r2_hidden('#skF_1'(A_88,B_89),A_86)
      | ~ r1_setfam_1(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_52,c_8])).

tff(c_91,plain,(
    ! [A_93,B_94,A_95] :
      ( r1_setfam_1(A_93,B_94)
      | ~ r2_hidden('#skF_1'(A_93,B_94),A_95)
      | ~ r1_setfam_1(A_95,B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_101,plain,(
    ! [A_96,B_97,A_98,B_99] :
      ( r1_setfam_1(A_96,B_97)
      | ~ r1_setfam_1(k2_setfam_1(A_98,B_99),B_97)
      | ~ r2_hidden('#skF_1'(A_96,B_97),B_99)
      | ~ r2_hidden('#skF_1'(A_96,B_97),A_98) ) ),
    inference(resolution,[status(thm)],[c_61,c_91])).

tff(c_106,plain,(
    ! [A_100,A_101,B_102] :
      ( r1_setfam_1(A_100,k2_setfam_1(A_101,B_102))
      | ~ r2_hidden('#skF_1'(A_100,k2_setfam_1(A_101,B_102)),B_102)
      | ~ r2_hidden('#skF_1'(A_100,k2_setfam_1(A_101,B_102)),A_101) ) ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_127,plain,(
    ! [A_106,A_107] :
      ( ~ r2_hidden('#skF_1'(A_106,k2_setfam_1(A_107,A_106)),A_107)
      | r1_setfam_1(A_106,k2_setfam_1(A_107,A_106)) ) ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_137,plain,(
    ! [A_3] : r1_setfam_1(A_3,k2_setfam_1(A_3,A_3)) ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_38,plain,(
    ~ r1_setfam_1('#skF_9',k2_setfam_1('#skF_9','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.25  
% 1.90/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.26  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1
% 1.90/1.26  
% 1.90/1.26  %Foreground sorts:
% 1.90/1.26  
% 1.90/1.26  
% 1.90/1.26  %Background operators:
% 1.90/1.26  
% 1.90/1.26  
% 1.90/1.26  %Foreground operators:
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.26  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.90/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.26  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.90/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.90/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.26  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 1.90/1.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.90/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.26  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 1.90/1.26  tff('#skF_9', type, '#skF_9': $i).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.26  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 1.90/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.26  
% 1.99/1.27  tff(f_39, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.99/1.27  tff(f_53, axiom, (![A, B]: r1_setfam_1(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r1_setfam_1)).
% 1.99/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.99/1.27  tff(f_51, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 1.99/1.27  tff(f_56, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 1.99/1.27  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_setfam_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.27  tff(c_36, plain, (![A_49]: (r1_setfam_1(A_49, A_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.27  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.27  tff(c_58, plain, (![E_64, F_65, A_66, B_67]: (r2_hidden(k2_xboole_0(E_64, F_65), k2_setfam_1(A_66, B_67)) | ~r2_hidden(F_65, B_67) | ~r2_hidden(E_64, A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.27  tff(c_61, plain, (![A_1, A_66, B_67]: (r2_hidden(A_1, k2_setfam_1(A_66, B_67)) | ~r2_hidden(A_1, B_67) | ~r2_hidden(A_1, A_66))), inference(superposition, [status(thm), theory('equality')], [c_2, c_58])).
% 1.99/1.27  tff(c_6, plain, (![A_3, B_4, C_13]: (r2_hidden('#skF_2'(A_3, B_4, C_13), B_4) | ~r2_hidden(C_13, A_3) | ~r1_setfam_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.27  tff(c_52, plain, (![C_61, A_62, B_63]: (r1_tarski(C_61, '#skF_2'(A_62, B_63, C_61)) | ~r2_hidden(C_61, A_62) | ~r1_setfam_1(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.27  tff(c_8, plain, (![A_3, B_4, D_12]: (~r1_tarski('#skF_1'(A_3, B_4), D_12) | ~r2_hidden(D_12, B_4) | r1_setfam_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.27  tff(c_68, plain, (![A_86, B_87, A_88, B_89]: (~r2_hidden('#skF_2'(A_86, B_87, '#skF_1'(A_88, B_89)), B_89) | r1_setfam_1(A_88, B_89) | ~r2_hidden('#skF_1'(A_88, B_89), A_86) | ~r1_setfam_1(A_86, B_87))), inference(resolution, [status(thm)], [c_52, c_8])).
% 1.99/1.27  tff(c_91, plain, (![A_93, B_94, A_95]: (r1_setfam_1(A_93, B_94) | ~r2_hidden('#skF_1'(A_93, B_94), A_95) | ~r1_setfam_1(A_95, B_94))), inference(resolution, [status(thm)], [c_6, c_68])).
% 1.99/1.27  tff(c_101, plain, (![A_96, B_97, A_98, B_99]: (r1_setfam_1(A_96, B_97) | ~r1_setfam_1(k2_setfam_1(A_98, B_99), B_97) | ~r2_hidden('#skF_1'(A_96, B_97), B_99) | ~r2_hidden('#skF_1'(A_96, B_97), A_98))), inference(resolution, [status(thm)], [c_61, c_91])).
% 1.99/1.27  tff(c_106, plain, (![A_100, A_101, B_102]: (r1_setfam_1(A_100, k2_setfam_1(A_101, B_102)) | ~r2_hidden('#skF_1'(A_100, k2_setfam_1(A_101, B_102)), B_102) | ~r2_hidden('#skF_1'(A_100, k2_setfam_1(A_101, B_102)), A_101))), inference(resolution, [status(thm)], [c_36, c_101])).
% 1.99/1.27  tff(c_127, plain, (![A_106, A_107]: (~r2_hidden('#skF_1'(A_106, k2_setfam_1(A_107, A_106)), A_107) | r1_setfam_1(A_106, k2_setfam_1(A_107, A_106)))), inference(resolution, [status(thm)], [c_10, c_106])).
% 1.99/1.27  tff(c_137, plain, (![A_3]: (r1_setfam_1(A_3, k2_setfam_1(A_3, A_3)))), inference(resolution, [status(thm)], [c_10, c_127])).
% 1.99/1.27  tff(c_38, plain, (~r1_setfam_1('#skF_9', k2_setfam_1('#skF_9', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.27  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_38])).
% 1.99/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.27  
% 1.99/1.27  Inference rules
% 1.99/1.27  ----------------------
% 1.99/1.27  #Ref     : 0
% 1.99/1.27  #Sup     : 19
% 1.99/1.27  #Fact    : 0
% 1.99/1.27  #Define  : 0
% 1.99/1.27  #Split   : 0
% 1.99/1.27  #Chain   : 0
% 1.99/1.27  #Close   : 0
% 1.99/1.27  
% 1.99/1.27  Ordering : KBO
% 1.99/1.27  
% 1.99/1.27  Simplification rules
% 1.99/1.27  ----------------------
% 1.99/1.27  #Subsume      : 0
% 1.99/1.27  #Demod        : 1
% 1.99/1.27  #Tautology    : 7
% 1.99/1.27  #SimpNegUnit  : 0
% 1.99/1.27  #BackRed      : 1
% 1.99/1.27  
% 1.99/1.27  #Partial instantiations: 0
% 1.99/1.27  #Strategies tried      : 1
% 1.99/1.27  
% 1.99/1.27  Timing (in seconds)
% 1.99/1.27  ----------------------
% 1.99/1.27  Preprocessing        : 0.29
% 1.99/1.27  Parsing              : 0.16
% 1.99/1.27  CNF conversion       : 0.02
% 1.99/1.27  Main loop            : 0.16
% 1.99/1.27  Inferencing          : 0.07
% 1.99/1.27  Reduction            : 0.04
% 1.99/1.27  Demodulation         : 0.03
% 1.99/1.27  BG Simplification    : 0.02
% 1.99/1.27  Subsumption          : 0.03
% 1.99/1.27  Abstraction          : 0.01
% 1.99/1.27  MUC search           : 0.00
% 1.99/1.27  Cooper               : 0.00
% 1.99/1.27  Total                : 0.48
% 1.99/1.27  Index Insertion      : 0.00
% 1.99/1.27  Index Deletion       : 0.00
% 1.99/1.27  Index Matching       : 0.00
% 1.99/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
